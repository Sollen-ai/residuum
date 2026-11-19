//! Release-mode timing harness for `scripts/test_safe.py --benchmark`.
//!
//! Usage: `benchmark_closure <fixture.res> <repetitions> <budget-seconds>`.
//! For every experiment of the fixture it runs the evaluators that the
//! 2026-11-18 optimizations changed, the same ones the equivalence sweeps
//! compare (`src/derive/known_index_tests.rs`): `close` and
//! `IncrementalClosure` (or `IncrementalProgramClosure` with Programs), and
//! `ForwardSession`, up to 64 rounds. Only evaluation is timed, not parsing.
//! It prints one JSON line: seconds per repetition for each evaluator, and a
//! digest of every resulting closure so two builds can be compared.
//!
//! It uses only API that also exists at the default baseline, so the runner
//! copies this same file into the baseline worktree and both are measured
//! with identical code.
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::time::Instant;

use residuum::typed::{Declaration, DerivationTime, Event, Module, Rule};
use residuum::{
    DerivationClock, ForwardSession, IncrementalClosure, IncrementalProgramClosure, close,
    load_formal_module,
};

#[derive(Default)]
struct Clock(usize);
impl DerivationClock for Clock {
    fn next_derivation_time(&mut self) -> DerivationTime {
        self.0 += 1;
        DerivationTime {
            name: format!("index-{}", self.0),
        }
    }
}

/// One pass over every experiment; returns (close, incremental, forward)
/// seconds and the closures' Debug text.
fn pass(module: &Module, rules: &[Rule], programs: bool) -> ([f64; 3], Vec<String>) {
    let mut seconds = [0.0; 3];
    let mut closures = Vec::new();
    for declaration in &module.declarations {
        let Declaration::Experiment(experiment) = declaration else {
            continue;
        };
        let seeds: &[Event] = &experiment.input;
        let split = seeds.len() / 2;
        if programs {
            let started = Instant::now();
            if let Ok(mut state) = IncrementalProgramClosure::new(
                seeds[..split].to_vec(),
                module,
                &mut Clock::default(),
            ) {
                state.update(seeds[split..].to_vec(), &mut Clock::default());
                seconds[1] += started.elapsed().as_secs_f64();
                closures.push(format!("{:?}", state.closure()));
            }
        } else {
            let started = Instant::now();
            let closure = close(seeds.to_vec(), rules, &mut Clock::default());
            seconds[0] += started.elapsed().as_secs_f64();
            closures.push(format!("{closure:?}"));
            let started = Instant::now();
            let mut state =
                IncrementalClosure::new(seeds[..split].to_vec(), rules, &mut Clock::default());
            state.update(seeds[split..].to_vec(), &mut Clock::default());
            seconds[1] += started.elapsed().as_secs_f64();
            closures.push(format!("{:?}", state.closure()));
        }
        let started = Instant::now();
        if let Ok(mut session) = ForwardSession::for_module(seeds.to_vec(), module) {
            let mut clock = Clock::default();
            let mut rounds = 0;
            while !session.is_complete() && rounds < 64 {
                session.step(&mut clock);
                rounds += 1;
            }
            seconds[2] += started.elapsed().as_secs_f64();
            closures.push(format!("{rounds} {:?}", session.closure()));
        }
    }
    (seconds, closures)
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let [fixture, repetitions, budget] = args.as_slice() else {
        eprintln!("usage: benchmark_closure <fixture.res> <repetitions> <budget-seconds>");
        std::process::exit(2);
    };
    let repetitions: usize = repetitions.parse().expect("repetitions");
    let budget: f64 = budget.parse().expect("budget");
    let module = load_formal_module(fixture).expect("fixture");
    let rules: Vec<Rule> = module
        .declarations
        .iter()
        .filter_map(|d| match d {
            Declaration::Rule(rule) => Some(rule.clone()),
            _ => None,
        })
        .collect();
    let programs = module
        .declarations
        .iter()
        .any(|d| matches!(d, Declaration::Program(_)));
    let started = Instant::now();
    let mut runs: Vec<[f64; 3]> = Vec::new();
    let mut digest = None;
    while runs.len() < repetitions {
        let pass_started = Instant::now();
        let (seconds, closures) = pass(&module, &rules, programs);
        let mut hasher = DefaultHasher::new();
        closures.hash(&mut hasher);
        let value = hasher.finish();
        assert!(
            digest.is_none_or(|d| d == value),
            "nondeterministic closure"
        );
        digest = Some(value);
        runs.push(seconds);
        // Stop early rather than reach the runner's 15 s stage timeout: the
        // next pass is predicted from this whole pass, formatting included.
        let pass_seconds = pass_started.elapsed().as_secs_f64();
        if started.elapsed().as_secs_f64() + pass_seconds > budget {
            break;
        }
    }
    let column = |i: usize| {
        runs.iter()
            .map(|r| format!("{:.6}", r[i]))
            .collect::<Vec<_>>()
            .join(",")
    };
    println!(
        "{{\"close\":[{}],\"incremental\":[{}],\"forward\":[{}],\"digest\":\"{:016x}\"}}",
        column(0),
        column(1),
        column(2),
        digest.unwrap_or(0)
    );
}
