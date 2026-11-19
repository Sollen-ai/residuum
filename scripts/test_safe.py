#!/usr/bin/env python3
"""Compile and run Rust tests in separate systemd cgroups with enforced limits."""

import argparse
import collections
import datetime
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parent.parent
TEST_FAMILIES = {'test-core', 'test-residual', 'test-experiments', 'test-legal-geometry', 'test-legal-learning'}
# Families that gate tests in each target; test-core belongs to both.
TARGET_FAMILIES = {
    'lib': {'test-core', 'test-residual', 'test-experiments'},
    'cli': {'test-core', 'test-legal-geometry', 'test-legal-learning'},
}
MIB = 1024 * 1024
# Raised by 300 MiB on 2026-11-19 by the owner (was 1024 / 768): the library
# test build peaks near 723 MiB from scratch. The 256 MiB stop margin is kept.
MEMORY_LIMIT = 1324 * MIB
STOP_MEMORY = 1068 * MIB
# Benchmark mode only (--benchmark), authorized by the owner on 2026-11-19:
# release builds may take this long. Every other compilation keeps 45 s, and
# the memory limits above are unchanged.
BENCHMARK_COMPILE_TIMEOUT = 600
# The pre-2026-11-19 pair. Binaries from before the raise refuse to run
# unless their cgroup has exactly this limit, so the benchmark runs them under
# it; it is stricter than the current one.
LEGACY_MEMORY_LIMIT = 1024 * MIB
LEGACY_STOP_MEMORY = 768 * MIB
HEAVY_FIXTURES = (
    'examples/experiments/peano_after.res',
    'examples/experiments/peano_multiplication.res',
    'examples/experiments/peano_polynomial_scenario.res',
    'examples/experiments/peano_polynomial_product_scenario.res',
    'examples/experiments/program_incremental_scaling.res',
    'examples/experiments/program_proof_scaling.res',
)


def group_path():
    for line in Path('/proc/self/cgroup').read_text().splitlines():
        if line.startswith('0::'):
            return Path('/sys/fs/cgroup') / line[3:].lstrip('/')
    raise RuntimeError('cgroup v2 is required; refusing unbounded execution')


def kill_process_group(process):
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass


def worker(report, index):
    request = json.loads((report / f'{index:02d}.request.json').read_text())
    group = group_path()
    memory_limit = request.get('memory_limit', MEMORY_LIMIT)
    stop_memory = request.get('stop_memory', STOP_MEMORY)
    if memory_limit > MEMORY_LIMIT or stop_memory > STOP_MEMORY:
        raise RuntimeError('requested limits exceed the runner limits; refusing execution')
    if ((group / 'memory.max').read_text().strip() != str(memory_limit)
            or (group / 'memory.swap.max').read_text().strip() != '0'):
        raise RuntimeError('RAM/swap limits are not enforced; refusing execution')
    samples = collections.deque()
    reason = None
    started = time.monotonic()
    with (report / f'{index:02d}.output.txt').open('w') as output:
        process = subprocess.Popen(request['command'], cwd=request.get('cwd', ROOT), stdout=output,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        try:
            while process.poll() is None:
                now = time.monotonic()
                peak = int((group / 'memory.peak').read_text())
                if now - started >= request['timeout']:
                    reason = 'timeout'
                elif peak >= stop_memory:
                    reason = 'near_memory_limit'
                rss = 0
                try:
                    for line in Path(f'/proc/{process.pid}/status').read_text().splitlines():
                        if line.startswith('VmRSS:'):
                            rss = int(line.split()[1]) * 1024
                            break
                except FileNotFoundError:
                    pass
                while samples and samples[0][0] < now - 1.0:
                    samples.popleft()
                if (request['stage'] in ('test', 'fixture') and rss >= 128 * MIB and samples
                        and rss - min(sample[1] for sample in samples) >= 64 * MIB):
                    reason = reason or 'abnormal_memory_growth'
                samples.append((now, rss))
                if reason:
                    kill_process_group(process)
                    break
                time.sleep(0.02)
            status = process.wait(timeout=2)
        except BaseException:
            kill_process_group(process)
            process.wait(timeout=2)
            raise
    events = dict(line.split() for line in (group / 'memory.events').read_text().splitlines())
    peak_group = int((group / 'memory.peak').read_text())
    if peak_group >= stop_memory:
        reason = reason or 'near_memory_limit'
    if int(events.get('oom', 0)) or int(events.get('oom_kill', 0)):
        reason = reason or 'cgroup_oom'
    if status != 0:
        reason = reason or 'nonzero_exit'
    if request['stage'] == 'test' and reason is None:
        output = (report / f'{index:02d}.output.txt').read_text()
        if 'test result: ok. 1 passed;' not in output:
            reason = 'expected_exactly_one_passing_test'
    row = dict(name=request['name'], stage=request['stage'], exit_status=status,
               elapsed_seconds=time.monotonic() - started,
               peak_rss_bytes=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss * 1024,
               cgroup_peak_bytes=peak_group, memory_events=events, stop_reason=reason)
    (report / f'{index:02d}.result.json').write_text(json.dumps(row, indent=2) + '\n')
    return 0 if reason is None else 1


def run_bounded(report, rows, stage, name, command, timeout, diagnostics=None,
                memory_limit=MEMORY_LIMIT, stop_memory=STOP_MEMORY, cwd=ROOT):
    # Callers may only tighten the limits; the worker checks this again.
    if memory_limit > MEMORY_LIMIT or stop_memory > STOP_MEMORY:
        raise RuntimeError('requested limits exceed the runner limits; refusing execution')
    index = len(rows) + 1
    request = dict(stage=stage, name=name, command=command, timeout=timeout,
                   memory_limit=memory_limit, stop_memory=stop_memory, cwd=str(cwd))
    (report / f'{index:02d}.request.json').write_text(json.dumps(request, indent=2) + '\n')
    unit = f'residuum-safe-{os.getpid()}-{index}'
    scope = ['/usr/bin/systemd-run', '--user', '--scope', '--quiet', f'--unit={unit}',
             f'--property=MemoryMax={memory_limit}', '--property=MemorySwapMax=0',
             '--property=CPUQuota=100%', sys.executable, str(Path(__file__).resolve()),
             '--worker', str(report), str(index)]
    with (report / f'{index:02d}.scope.txt').open('w') as output:
        try:
            completed = subprocess.run(scope, stdout=output, stderr=subprocess.STDOUT,
                                       timeout=timeout + 10)
        except subprocess.TimeoutExpired:
            subprocess.run(['/usr/bin/systemctl', '--user', 'kill', '--signal=SIGKILL',
                            '--kill-whom=all', f'{unit}.scope'], timeout=5, check=False,
                           stdout=output, stderr=subprocess.STDOUT)
            raise RuntimeError(f'{name}: scope timeout; no remaining tests executed')
    result_path = report / f'{index:02d}.result.json'
    if not result_path.exists():
        raise RuntimeError(f'{name}: isolation failed; see {report / f"{index:02d}.scope.txt"}')
    row = json.loads(result_path.read_text())
    if completed.returncode != 0:
        row['stop_reason'] = row['stop_reason'] or 'scope_nonzero_exit'
    rows.append(row)
    save_report(report, rows)
    print(f'{name} | {row["exit_status"]} | {row["elapsed_seconds"]:.4f}s | '
          f'{row["peak_rss_bytes"] / MIB:.2f} MiB RSS', flush=True, file=diagnostics)
    if row['stop_reason']:
        raise RuntimeError(f'{name}: {row["stop_reason"]}; no remaining tests executed. '
                           f'See {report / f"{index:02d}.output.txt"}')
    return report / f'{index:02d}.output.txt'


def release_binary(report, rows, label, cwd):
    # The only compilation allowed BENCHMARK_COMPILE_TIMEOUT; same memory limits.
    output = run_bounded(report, rows, 'compile', f'compile release {label}',
                         ['cargo', 'build', '--offline', '--locked', '--release', '--bin', 'residuum',
                          '--jobs', '1', '--message-format=json'], BENCHMARK_COMPILE_TIMEOUT, cwd=cwd)
    binaries = []
    for line in output.read_text().splitlines():
        try:
            message = json.loads(line)
        except json.JSONDecodeError:
            continue
        if (message.get('reason') == 'compiler-artifact' and message.get('executable')
                and message.get('target', {}).get('name') == 'residuum'
                and 'bin' in message.get('target', {}).get('kind', [])
                and not message.get('profile', {}).get('test')):
            binaries.append(Path(message['executable']))
    if len(binaries) != 1:
        raise RuntimeError(f'Expected one release binary for {label}; refusing execution')
    return binaries[0]


def benchmark(report, rows, baseline, repetitions):
    sha = subprocess.run(['git', 'rev-parse', '--verify', f'{baseline}^{{commit}}'], cwd=ROOT,
                         capture_output=True, text=True, check=True).stdout.strip()
    head = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=ROOT, capture_output=True,
                          text=True, check=True).stdout.strip()
    tree = ROOT / 'target' / 'benchmark' / sha[:12]
    if not tree.exists():
        subprocess.run(['git', 'worktree', 'add', '--detach', str(tree), sha], cwd=ROOT,
                       check=True, capture_output=True)
    # Binaries from before the limit raise insist on exactly the legacy cgroup
    # limit; read it from the baseline's own launcher check.
    source = subprocess.run(['git', 'show', f'{sha}:src/bin/residuum.rs'], cwd=ROOT,
                            capture_output=True, text=True, check=True).stdout
    legacy = f'"{LEGACY_MEMORY_LIMIT}"' in source
    versions = [
        ('baseline', release_binary(report, rows, 'baseline', tree), tree,
         LEGACY_MEMORY_LIMIT if legacy else MEMORY_LIMIT, LEGACY_STOP_MEMORY if legacy else STOP_MEMORY),
        ('current', release_binary(report, rows, 'current', ROOT), ROOT, MEMORY_LIMIT, STOP_MEMORY),
    ]
    results = []
    for fixture in HEAVY_FIXTURES:
        row = dict(fixture=fixture)
        for label, binary, cwd, memory_limit, stop_memory in versions:
            output = run_bounded(report, rows, 'benchmark', f'{label} {fixture}',
                                 [sys.executable, str(ROOT / 'scripts' / 'benchmark_helper.py'),
                                  str(binary), 'run', str(cwd / fixture), str(repetitions), '12'],
                                 15, memory_limit=memory_limit, stop_memory=stop_memory, cwd=cwd)
            row[label] = json.loads(output.read_text().strip().splitlines()[-1])
        results.append(row)
    summary = dict(baseline=sha, current=head, repetitions=repetitions, fixtures=results)
    (ROOT / 'target' / 'benchmark-results.json').write_text(json.dumps(summary, indent=2) + '\n')
    median = lambda values: sorted(values)[len(values) // 2]
    print(f'baseline {sha[:7]} vs current {head[:7]}; median of up to {repetitions} runs (s)')
    for row in results:
        b, c = row['baseline']['seconds'], row['current']['seconds']
        print(f'{row["fixture"]} | {median(b):.4f} [{min(b):.4f}-{max(b):.4f}] n={len(b)} | '
              f'{median(c):.4f} [{min(c):.4f}-{max(c):.4f}] n={len(c)} | '
              f'x{median(b) / median(c):.2f} | same output: '
              f'{row["baseline"]["output_sha256"] == row["current"]["output_sha256"]}')
    return 0


def save_report(report, rows):
    (report / 'results.json').write_text(json.dumps(rows, indent=2) + '\n')
    lines = ['| Nombre | Exit status | Tiempo (s) | Pico RSS (MiB) | Resultado |',
             '|---|---:|---:|---:|---|']
    for row in rows:
        lines.append(f'| {row["name"]} | {row["exit_status"]} | {row["elapsed_seconds"]:.4f} | '
                     f'{row["peak_rss_bytes"] / MIB:.2f} | {row["stop_reason"] or "passed"} |')
    (report / 'report.md').write_text('\n'.join(lines) + '\n')


def parse_names(output):
    return {line[:-6] for line in output.read_text().splitlines() if line.endswith(': test')}


def emit_output(path, stream):
    # Rendering happens inside the limited worker. Do not load a potentially
    # large result into the launcher process outside that cgroup.
    with path.open(encoding='utf-8') as output:
        while chunk := output.read(64 * 1024):
            stream.write(chunk)
    stream.flush()


def main():
    if len(sys.argv) == 4 and sys.argv[1] == '--worker':
        return worker(Path(sys.argv[2]), int(sys.argv[3]))
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--test', action='append', default=[], help='Exact active test name; repeatable')
    parser.add_argument('--test-target', choices=('lib', 'cli'), default='lib',
                        help='Compile only the selected test target (default: lib)')
    parser.add_argument('--features', default='',
                        help='Comma-separated test families (test-core, test-residual, test-experiments, test-legal-geometry, test-legal-learning); '
                             'default compiles every test')
    parser.add_argument('--binary', type=Path, help='Use an existing binary without compiling')
    parser.add_argument('--compile-only', action='store_true')
    parser.add_argument('--fmt-check', action='store_true')
    parser.add_argument('--format', action='store_true')
    parser.add_argument('--clippy', action='store_true',
                        help='Run cargo clippy on every target with warnings as errors, as CI does')
    parser.add_argument('--benchmark', action='store_true',
                        help='Time release builds of HEAD and --baseline on the heavy fixtures')
    parser.add_argument('--baseline', default='f3c8df3',
                        help='Commit to compare against in --benchmark (default: before the 2026-11-18 optimizations)')
    parser.add_argument('--repetitions', type=int, default=5,
                        help='Runs per fixture and version in --benchmark (1..20)')
    parser.add_argument('--fixture', type=Path, help='Run one source-defined Formal fixture with the bounded example runner')
    parser.add_argument('--cli', choices=('run', 'query', 'explain', 'execute'), help='Run one CLI command on --fixture under the same limits')
    parser.add_argument('--steps', type=int, help='Bounded stepwise CLI transitions (1..4096)')
    parser.add_argument('--trace', action='store_true', help='Show every stepwise CLI transition')
    parser.add_argument('--incremental', action='store_true', help='Forward incremental comparison of base/delta seed blocks; requires --fixture')
    parser.add_argument('--forward', action='store_true', help='Module-aware forward closure with active verb programs; requires --fixture')
    parser.add_argument('--library', type=Path, help='Compose one shared declaration fixture; requires --fixture and --incremental')
    args = parser.parse_args()
    if (args.steps is not None or args.trace) and not args.cli:
        parser.error('--steps and --trace require --cli')
    if args.steps is not None and not 1 <= args.steps <= 4096:
        parser.error('--steps must be in 1..4096')
    families = [f for f in args.features.split(',') if f]
    unknown = sorted(set(families) - TEST_FAMILIES)
    if unknown:
        parser.error(f'unknown test families: {", ".join(unknown)}')
    if families and (args.fixture or args.binary or args.fmt_check or args.format):
        parser.error('--features only selects test families for compilation')
    foreign = sorted(set(families) - TARGET_FAMILIES[args.test_target])
    if foreign:
        parser.error(f'test families not in --test-target {args.test_target}: {", ".join(foreign)}')
    if args.test_target != 'lib' and (args.fixture or args.fmt_check or args.format):
        parser.error('--test-target is only for test compilation/execution')
    if args.cli and (not args.fixture or args.forward or args.incremental or args.library):
        parser.error('--cli requires --fixture and cannot be combined with other fixture modes')
    if args.incremental and not args.fixture:
        parser.error('--incremental requires --fixture')
    if args.forward and not args.fixture:
        parser.error('--forward requires --fixture')
    if args.forward and args.incremental:
        parser.error('--forward and --incremental are separate experiment modes')
    if args.library and not (args.fixture and args.incremental):
        parser.error('--library requires --fixture and --incremental')
    if args.fixture and (args.test or args.binary or args.compile_only or args.fmt_check or args.format):
        parser.error('--fixture cannot be combined with test, binary, compile, or format options')
    if args.clippy and (args.fixture or args.test or args.binary or args.compile_only or families
                        or args.fmt_check or args.format or args.test_target != 'lib'):
        parser.error('--clippy runs alone: it checks every target and family')
    if args.benchmark and (args.clippy or args.fixture or args.test or args.binary or args.compile_only
                           or families or args.fmt_check or args.format or args.test_target != 'lib'
                           or args.cli or args.incremental or args.forward or args.library):
        parser.error('--benchmark runs alone')
    if not 1 <= args.repetitions <= 20:
        parser.error('--repetitions must be in 1..20')
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    report = ROOT / 'target' / 'test-diagnostics' / f'{stamp}-{os.getpid()}'
    report.mkdir(parents=True)
    diagnostics = sys.stderr if args.cli else sys.stdout
    print(f'Reports: {report}', flush=True, file=diagnostics)
    rows = []
    if args.benchmark:
        return benchmark(report, rows, args.baseline, args.repetitions)
    if args.fixture:
        fixture = args.fixture.resolve()
        if not fixture.is_file() or fixture.stat().st_size > 64 * 1024:
            raise RuntimeError('Expected one regular fixture file of at most 64 KiB')
        library = args.library.resolve() if args.library else None
        if library and (not library.is_file() or library.stat().st_size + fixture.stat().st_size > 64 * 1024):
            raise RuntimeError('Expected one regular library; combined fixtures must be at most 64 KiB')
        target = 'residuum' if args.cli else 'run_fixture'
        target_kind = 'bin' if args.cli else 'example'
        output = run_bounded(report, rows, 'compile', f'compile {target}',
                             ['cargo', 'build', '--offline', '--locked', f'--{target_kind}', target,
                              '--jobs', '1', '--message-format=json'], 45, diagnostics=diagnostics)
        binaries = []
        for line in output.read_text().splitlines():
            try:
                message = json.loads(line)
            except json.JSONDecodeError:
                continue
            if (message.get('reason') == 'compiler-artifact' and message.get('executable')
                    and message.get('target', {}).get('name') == target
                    and target_kind in message.get('target', {}).get('kind', [])):
                binaries.append(Path(message['executable']))
        if len(binaries) != 1:
            raise RuntimeError('Expected one compiled runner binary; refusing execution')
        try:
            output = run_bounded(report, rows, 'fixture', str(fixture.relative_to(ROOT))
                                 if fixture.is_relative_to(ROOT) else fixture.name,
                                 [str(binaries[0])] + ([args.cli] if args.cli else [])
                                 + (['--incremental'] if args.incremental else [])
                                 + (['--forward'] if args.forward else []) + [str(fixture)]
                                 + (['--library', str(library)] if library else [])
                                 + (['--steps', str(args.steps)] if args.steps is not None else [])
                                 + (['--trace'] if args.trace else []), 15,
                                 diagnostics=diagnostics)
        except RuntimeError:
            # Expose semantic errors to CLI callers as well as keeping the report.
            if args.cli and rows and rows[-1]['stage'] == 'fixture':
                emit_output(report / f'{len(rows):02d}.output.txt', sys.stderr)
            raise
        emit_output(output, sys.stdout)
        return 0
    if args.clippy:
        # Same cgroup, memory stop and compile timeout as any other compilation.
        run_bounded(report, rows, 'compile', 'cargo clippy',
                    ['cargo', 'clippy', '--offline', '--locked', '--all-targets', '--jobs', '1',
                     '--message-format=short', '--', '-D', 'warnings'], 45)
        return 0
    if args.fmt_check or args.format:
        command = ['cargo', 'fmt', '--all'] + (['--check'] if args.fmt_check else [])
        run_bounded(report, rows, 'format', 'cargo fmt', command, 30)
        return 0
    binary = args.binary.resolve() if args.binary else None
    if binary is None:
        target_args = ['--lib'] if args.test_target == 'lib' else ['--bin', 'residuum']
        target_kind = 'lib' if args.test_target == 'lib' else 'bin'
        output = run_bounded(report, rows, 'compile', 'compile only',
                             ['cargo', 'test', '--offline', '--locked', '--no-run'] + target_args +
                             (['--features', ','.join(families)] if families else []) + [
                              '--jobs', '1', '--message-format=json'], 45)
        binaries = []
        for line in output.read_text().splitlines():
            try:
                message = json.loads(line)
            except json.JSONDecodeError:
                continue
            if (message.get('reason') == 'compiler-artifact' and message.get('executable')
                    and message.get('profile', {}).get('test')
                    and message.get('target', {}).get('name') == 'residuum'
                    and target_kind in message.get('target', {}).get('kind', [])):
                binaries.append(Path(message['executable']))
        if len(binaries) != 1:
            raise RuntimeError('Expected one compiled test binary for the selected target; refusing execution')
        binary = binaries[0]
    if args.compile_only:
        return 0
    listed = run_bounded(report, rows, 'list', 'list tests',
                         [str(binary), '--list', '--format=terse'], 15)
    ignored = run_bounded(report, rows, 'list', 'list ignored tests',
                          [str(binary), '--list', '--ignored', '--format=terse'], 15)
    active = parse_names(listed) - parse_names(ignored)
    if not active:
        raise RuntimeError('No active tests found; refusing empty validation')
    selected = args.test or sorted(active)
    if len(selected) != len(set(selected)):
        raise RuntimeError('Duplicate test selection')
    for name in selected:
        if name not in active:
            raise RuntimeError(f'{name} is unknown or ignored; refusing execution')
    (report / 'tests.txt').write_text('\n'.join(selected) + '\n')
    for name in selected:
        run_bounded(report, rows, 'test', name,
                    [str(binary), '--exact', name, '--test-threads=1', '--nocapture'], 15)
    print(f'{len(selected)} tests passed individually; {len(parse_names(ignored))} tests ignored.', flush=True)
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (RuntimeError, OSError, subprocess.SubprocessError) as error:
        print(f'STOPPED: {error}', file=sys.stderr, flush=True)
        sys.exit(1)
