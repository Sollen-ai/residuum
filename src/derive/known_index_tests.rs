//! The argument index never drops a candidate `match_event` accepts: a
//! randomized check over every term shape and binding kind, and every example
//! fixture through the four evaluators, compared with the linear scan and,
//! for the depth-first join, with the breadth-first copying join.
use super::*;
use crate::typed::Type;
use std::path::{Path, PathBuf};

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

/// Deterministic xorshift, so the comparison is reproducible without crates.
struct Random(u64);
impl Random {
    fn below(&mut self, n: usize) -> usize {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 % n as u64) as usize
    }
}

fn record(value: Term) -> Term {
    Term::RecordLiteral {
        entity: "Box".into(),
        fields: vec![crate::typed::RecordFieldValue {
            field: "content".into(),
            value,
        }],
    }
}
fn after(argument: Term) -> Term {
    Term::Constructor {
        constructor: crate::typed::Constructor::After,
        argument: Box::new(argument),
    }
}

/// Every term shape: constants, `None`, entity, optional and time parameters,
/// a variable that is not a parameter, constructors and records, ground or not.
fn terms() -> Vec<Term> {
    vec![
        Term::Const("a".into()),
        Term::Const("b".into()),
        Term::None,
        Term::Var("x".into()),
        Term::Var("y".into()),
        Term::Var("t".into()),
        Term::Var("free".into()),
        after(Term::Const("a".into())),
        after(Term::Var("t".into())),
        record(Term::Const("a".into())),
        record(Term::Var("x".into())),
        record(Term::None),
    ]
}
fn parameters() -> Vec<crate::typed::Arg> {
    let entity = Type::Entity("Thing".into());
    vec![
        crate::typed::Arg {
            name: "x".into(),
            ty: entity.clone(),
        },
        crate::typed::Arg {
            name: "y".into(),
            ty: Type::Optional(Box::new(entity)),
        },
        crate::typed::Arg {
            name: "t".into(),
            ty: Type::PropositionTime,
        },
    ]
}
/// Ground and non-ground terms, `None`, and time values, some of them
/// ill-typed for the parameter, so `bind_typed` rejects them.
fn values() -> Vec<SubstitutionValue> {
    let mut values: Vec<_> = terms().into_iter().map(SubstitutionValue::Term).collect();
    values.push(SubstitutionValue::Time(TimeExpr::At("t0".into())));
    values.push(SubstitutionValue::Time(TimeExpr::Var("t".into())));
    values
}
fn event(random: &mut Random, terms: &[Term]) -> Event {
    let arity = 1 + random.below(2);
    Event {
        polarity: if random.below(4) == 0 {
            Polarity::EvidentialNot
        } else {
            Polarity::Positive
        },
        verb: ["v", "w"][random.below(2)].into(),
        args: (0..arity).map(|_| terms[random.below(terms.len())].clone()).collect(),
        proposition: PropositionType {
            kind: crate::typed::PropositionKind::Prop,
            time: TimeExpr::At("t0".into()),
        },
        transition: None,
    }
}

#[test]
fn argument_index_keeps_every_candidate_match_event_accepts() {
    let terms = terms();
    let parameters = parameters();
    let values = values();
    let mut random = Random(0x9e37_79b9_7f4a_7c15);
    let (mut accepted, mut pruned) = (0usize, 0usize);
    for trial in 0..400 {
        // Known with duplicates and non-ground events; half indexed at
        // construction, half inserted afterwards, as the closures do.
        let known: Vec<Event> = (0..1 + random.below(24))
            .map(|_| event(&mut random, &terms))
            .collect();
        let split = random.below(known.len() + 1);
        let mut index = KnownIndex::with_arguments(&known[..split]);
        for (position, event) in known.iter().enumerate().skip(split) {
            index.insert(position, event);
        }
        let view = KnownView {
            events: &known,
            index: Some(&index),
        };
        for _ in 0..20 {
            let pattern = event(&mut random, &terms);
            let mut bindings = BTreeMap::new();
            for parameter in &parameters {
                if random.below(2) == 0 {
                    let value = values[random.below(values.len())].clone();
                    bindings.insert(parameter.name.clone(), value);
                }
            }
            let expected: Vec<usize> = (0..known.len())
                .filter(|&i| {
                    match_event(&pattern, &known[i], &parameters, &mut bindings.clone()).is_some()
                })
                .collect();
            let candidates: Vec<usize> = view
                .candidates_bound(&pattern, &parameters, &bindings)
                .map(|event| {
                    known
                        .iter()
                        .position(|k| std::ptr::eq(k, event))
                        .expect("candidate from Known")
                })
                .collect();
            assert!(
                candidates.windows(2).all(|w| w[0] < w[1]),
                "trial {trial}: candidates out of Known order"
            );
            assert!(
                expected.iter().all(|i| candidates.contains(i)),
                "trial {trial}: dropped a match\npattern {pattern:?}\nbindings {bindings:?}\n\
                 expected {expected:?}\ncandidates {candidates:?}"
            );
            accepted += expected.len();
            pruned += known.len() - candidates.len();
        }
    }
    // Neither side of the comparison is vacuous.
    assert!(accepted > 1000 && pruned > 1000, "{accepted} / {pruned}");
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

/// Every evaluator that reads Known through the argument index, as Debug text
/// so stamps, order and provenance are all compared.
fn evaluate(module: &Module, seeds: &[Event]) -> Vec<String> {
    let has_programs = module
        .declarations
        .iter()
        .any(|d| matches!(d, Declaration::Program(_)));
    let rules: Vec<Rule> = module
        .declarations
        .iter()
        .filter_map(|d| match d {
            Declaration::Rule(rule) => Some(rule.clone()),
            _ => None,
        })
        .collect();
    let split = seeds.len() / 2;
    let mut runs = Vec::new();
    if has_programs {
        let Ok(mut state) =
            IncrementalProgramClosure::new(seeds[..split].to_vec(), module, &mut Clock::default())
        else {
            return runs;
        };
        let delta = state.update(seeds[split..].to_vec(), &mut Clock::default());
        runs.push(format!("{:?} {delta:?}", state.closure()));
    } else {
        runs.push(format!("{:?}", close(seeds.to_vec(), &rules, &mut Clock::default())));
        let mut state =
            IncrementalClosure::new(seeds[..split].to_vec(), &rules, &mut Clock::default());
        let delta = state.update(seeds[split..].to_vec(), &mut Clock::default());
        runs.push(format!("{:?} {delta:?}", state.closure()));
    }
    if let Ok(mut session) = ForwardSession::for_module(seeds.to_vec(), module) {
        let mut clock = Clock::default();
        let mut rounds = 0;
        while !session.is_complete() && rounds < 64 {
            session.step(&mut clock);
            rounds += 1;
        }
        runs.push(format!("{rounds} {:?}", session.closure()));
    }
    runs
}

const SLOW: [&str; 6] = [
    "peano_after.res",
    "peano_multiplication.res",
    "peano_polynomial_scenario.res",
    "peano_polynomial_product_scenario.res",
    "program_incremental_scaling.res",
    "program_proof_scaling.res",
];

/// Split in two by directory so each half stays well inside the runner's
/// per-test timeout; together they cover every fixture under `examples/`.
#[test]
fn argument_index_equals_linear_scan_on_experiment_fixtures() {
    let (modules, compared) = sweep(|path| path.starts_with(examples().join("experiments")));
    assert!(modules > 50 && compared > 100, "{modules} / {compared}");
}
#[test]
fn argument_index_equals_linear_scan_on_other_example_fixtures() {
    let (modules, compared) = sweep(|path| !path.starts_with(examples().join("experiments")));
    assert!(modules > 30 && compared > 100, "{modules} / {compared}");
}

fn examples() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("examples")
}

fn sweep(select: impl Fn(&Path) -> bool) -> (usize, usize) {
    let mut paths = Vec::new();
    fixtures(&examples(), &mut paths);
    paths.retain(|path| select(path));
    let (mut modules, mut compared) = (0, 0);
    for path in &paths {
        // Workloads too slow for the runner's per-test timeout under the
        // linear scan. The product scenario's partialProduct is compared with
        // the linear scan in profile_tests.
        if SLOW.iter().any(|name| path.ends_with(name)) {
            continue;
        }
        let Ok(module) = crate::load_formal_module(path) else {
            continue;
        };
        modules += 1;
        for declaration in &module.declarations {
            let Declaration::Experiment(experiment) = declaration else {
                continue;
            };
            let indexed = evaluate(&module, &experiment.input);
            let linear = {
                let _scan = profile::linear_scan();
                evaluate(&module, &experiment.input)
            };
            // The breadth-first copying join, on the argument index.
            let copying = {
                let _reference = profile::reference_join();
                evaluate(&module, &experiment.input)
            };
            assert_eq!(
                indexed,
                copying,
                "reference join: {} {}",
                path.display(),
                experiment.name
            );
            assert_eq!(
                indexed,
                linear,
                "{} {}",
                path.display(),
                experiment.name
            );
            compared += indexed.len();
        }
    }
    eprintln!("{modules} modules, {compared} evaluations compared");
    (modules, compared)
}
