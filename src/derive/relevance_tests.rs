//! Skipping rules the frontier cannot pivot into changes no result: every
//! example fixture, with ordinary and program closures, batch and single-event
//! updates, compared with examining every rule.
use super::*;
use crate::typed::HornClause;
use std::path::{Path, PathBuf};

#[derive(Default)]
struct Clock(usize);
impl DerivationClock for Clock {
    fn next_derivation_time(&mut self) -> DerivationTime {
        self.0 += 1;
        DerivationTime {
            name: format!("relevance-{}", self.0),
        }
    }
}

fn fixtures(directory: &Path, output: &mut Vec<PathBuf>) {
    let mut entries: Vec<_> = std::fs::read_dir(directory)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            fixtures(&path, output);
        } else if path.extension().is_some_and(|e| e == "res") {
            output.push(path);
        }
    }
}

/// Workloads too slow for the runner's per-test timeout with every rule
/// examined; the product scenario is compared in profile_tests.
const SLOW: [&str; 6] = [
    "peano_after.res",
    "peano_multiplication.res",
    "peano_polynomial_scenario.res",
    "peano_polynomial_product_scenario.res",
    "program_incremental_scaling.res",
    "program_proof_scaling.res",
];

fn only_unit(antecedent: &Antecedent) -> bool {
    match antecedent {
        Antecedent::Unit => true,
        Antecedent::Event(_) => false,
        Antecedent::And(a, b) => only_unit(a) && only_unit(b),
    }
}
fn has_negative(antecedent: &Antecedent) -> bool {
    match antecedent {
        Antecedent::Unit => false,
        Antecedent::Event(event) => event.polarity == Polarity::EvidentialNot,
        Antecedent::And(a, b) => has_negative(a) || has_negative(b),
    }
}

#[derive(Default, Debug)]
struct Coverage {
    residual: usize,
    unit_only: usize,
    negative: usize,
    batches: usize,
    skipped: usize,
    unbuilt: usize,
}

/// Deltas and closures as Debug text, with `rules_examined` zeroed: it is the
/// one counter that the filter is meant to change.
fn run(module: &Module, rules: &[Rule], seeds: &[Event], programs: bool) -> (String, usize) {
    let split = seeds.len() / 2;
    let mut clock = Clock::default();
    let mut text = String::new();
    let mut examined = 0;
    if programs {
        let Ok(mut state) =
            IncrementalProgramClosure::new(seeds[..split].to_vec(), module, &mut clock)
        else {
            return (text, 0);
        };
        let mut delta = state.update(seeds[split..].to_vec(), &mut clock);
        examined += delta.stats.rules_examined;
        delta.stats.rules_examined = 0;
        text.push_str(&format!("{delta:?}\n{:?}\n", state.closure()));
        let Ok(mut single) = IncrementalProgramClosure::new(Vec::new(), module, &mut clock) else {
            return (text, examined);
        };
        for seed in seeds {
            let mut delta = single.update(vec![seed.clone()], &mut clock);
            examined += delta.stats.rules_examined;
            delta.stats.rules_examined = 0;
            text.push_str(&format!("{delta:?}\n"));
        }
        text.push_str(&format!("{:?}\n", single.closure()));
    } else {
        let mut batch = IncrementalClosure::new(seeds[..split].to_vec(), rules, &mut clock);
        let mut delta = batch.update(seeds[split..].to_vec(), &mut clock);
        examined += delta.stats.rules_examined;
        delta.stats.rules_examined = 0;
        text.push_str(&format!("{delta:?}\n{:?}\n", batch.closure()));
        let mut single = IncrementalClosure::new(Vec::new(), rules, &mut clock);
        for seed in seeds {
            let mut delta = single.update(vec![seed.clone()], &mut clock);
            examined += delta.stats.rules_examined;
            delta.stats.rules_examined = 0;
            text.push_str(&format!("{delta:?}\n"));
        }
        text.push_str(&format!("{:?}\n", single.closure()));
    }
    (text, examined)
}

fn examples() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("examples")
}

/// Split in two by directory so each half stays well inside the runner's
/// per-test timeout; together they cover every fixture under `examples/`.
#[test]
fn relevant_rules_keep_experiment_fixtures_equal_to_examining_every_rule() {
    let (compared, coverage) = sweep(|path| path.starts_with(examples().join("experiments")));
    assert!(compared > 150, "{compared}");
    assert!(
        coverage.residual > 0
            && coverage.unit_only > 0
            && coverage.negative > 0
            && coverage.batches > 40
            && coverage.skipped > 0,
        "{coverage:?}"
    );
}
#[test]
fn relevant_rules_keep_other_example_fixtures_equal_to_examining_every_rule() {
    let (compared, coverage) = sweep(|path| !path.starts_with(examples().join("experiments")));
    assert!(
        compared > 50 && coverage.skipped > 0,
        "{compared} {coverage:?}"
    );
}

fn sweep(select: impl Fn(&Path) -> bool) -> (usize, Coverage) {
    let mut paths = Vec::new();
    fixtures(&examples(), &mut paths);
    paths.retain(|path| select(path));
    let mut coverage = Coverage::default();
    let mut compared = 0;
    for path in &paths {
        if SLOW.iter().any(|name| path.ends_with(name)) {
            continue;
        }
        let Ok(module) = crate::load_formal_module(path) else {
            continue;
        };
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
        let bodies: Vec<HornClause> = rules
            .iter()
            .map(|rule| match &rule.body {
                RuleBody::HornClause(clause) => clause.clone(),
                RuleBody::ResidualClause(clause) => clause.unresiduate(),
            })
            .collect();
        for declaration in &module.declarations {
            let Declaration::Experiment(experiment) = declaration else {
                continue;
            };
            let (filtered, examined) = run(&module, &rules, &experiment.input, programs);
            let (every, examined_every) = {
                let _all = profile::every_rule();
                run(&module, &rules, &experiment.input, programs)
            };
            assert_eq!(filtered, every, "{} {}", path.display(), experiment.name);
            // A program closure that cannot be built compares nothing.
            if filtered.is_empty() {
                coverage.unbuilt += 1;
                continue;
            }
            assert!(examined <= examined_every);
            let skipped = examined_every - examined;
            coverage.skipped += skipped;
            // Experiments where the filter skipped work in a module with each
            // kind of rule; not proof that a rule of that kind was skipped.
            if skipped > 0 {
                let kinds = [
                    rules
                        .iter()
                        .any(|r| matches!(r.body, RuleBody::ResidualClause(_))),
                    bodies.iter().any(|b| only_unit(&b.antecedent)),
                    bodies.iter().any(|b| has_negative(&b.antecedent)),
                ];
                coverage.residual += usize::from(kinds[0]);
                coverage.unit_only += usize::from(kinds[1]);
                coverage.negative += usize::from(kinds[2]);
            }
            coverage.batches +=
                usize::from(experiment.input.len() - experiment.input.len() / 2 > 1);
            compared += 1;
        }
    }
    eprintln!("{compared} experiments compared; {coverage:?}");
    (compared, coverage)
}
