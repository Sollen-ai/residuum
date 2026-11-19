//! Fixtures provide all semantics and inputs. Rust only observes and compares.
use super::*;
use std::path::Path;

#[derive(Default)]
struct Clock(usize);
impl DerivationClock for Clock {
    fn next_derivation_time(&mut self) -> DerivationTime {
        self.0 += 1;
        DerivationTime {
            name: format!("profile-{}", self.0),
        }
    }
}
fn load(file: &str) -> Module {
    crate::load_formal_module(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("examples/experiments")
            .join(file),
    )
    .unwrap()
}
fn input(module: &Module, name: &str) -> Vec<Event> {
    module
        .declarations
        .iter()
        .find_map(|d| match d {
            Declaration::Experiment(e) if e.name == name => Some(e.input.clone()),
            _ => None,
        })
        .unwrap()
}
fn product(name: &str) -> (Module, Vec<Event>) {
    let module = load("peano_polynomial_product_scenario.res");
    let seeds = input(&module, name);
    (module, seeds)
}

#[test]
fn profiling_preserves_full_closure_and_stamps() {
    let (module, seeds) = product("unitProduct");
    let original = {
        let _scan = profile::linear_scan();
        close_program_reference(seeds.clone(), &module, &mut Clock::default()).unwrap()
    };
    let session = profile::Session::new("unitProduct");
    let measured = close_program_reference(seeds, &module, &mut Clock::default()).unwrap();
    let stats = session.finish();
    // Debug includes proposition types, transitions, witness order, substitutions,
    // clocks and multiplicity, which logical Event equality deliberately ignores.
    assert_eq!(format!("{original:?}"), format!("{measured:?}"));
    assert!(stats.probes > 0 && stats.duplicates > 0);
}

#[test]
fn profile_polynomial_product_fixture() {
    // Normal verification always uses the completed small fixture. The larger
    // diagnostic is explicitly opt-in and still uses the runner's same timeout.
    let name =
        std::env::var("RESIDUUM_PROFILE_PRODUCT").unwrap_or_else(|_| "partialProduct".into());
    assert!(["partialProduct", "principalProduct"].contains(&name.as_str()));
    let (module, seeds) = product(&name);
    let label = if name == "partialProduct" {
        "partialProduct"
    } else {
        "principalProduct"
    };
    let session = profile::Session::new(label);
    let closure = close_program_reference(seeds, &module, &mut Clock::default()).unwrap();
    let stats = session.finish();
    if name == "partialProduct" {
        assert_eq!((closure.known.len(), closure.derivations.len()), (223, 244));
        assert!(stats.associated_evaluations > stats.activated);
    }
    let goal = module
        .declarations
        .iter()
        .find_map(|d| match d {
            Declaration::Experiment(e) if e.name == name => Some(&e.goal),
            _ => None,
        })
        .unwrap();
    assert!(closure.known.contains(goal));
    if name == "principalProduct" {
        fn natural(term: &Term) -> usize {
            fn count(time: TimeExpr) -> usize {
                match time {
                    TimeExpr::At(name) if name == "zeroTime" => 0,
                    TimeExpr::After(inner) => 1 + count(*inner),
                    _ => panic!("not a ground Peano natural"),
                }
            }
            count(TimeExpr::from_term(term).unwrap())
        }
        let output = closure
            .known
            .iter()
            .filter(|e| e.verb == "coefficient" && e.args[0] == Term::Const("r".into()))
            .map(|e| (natural(&e.args[1]), natural(&e.args[2])))
            .collect::<Vec<_>>();
        assert_eq!(output.len(), 7, "exactly one result per output exponent");
        assert_eq!(
            output.into_iter().collect::<BTreeMap<_, _>>(),
            [5, 10, 18, 26, 9, 12, 0].into_iter().enumerate().collect()
        );
        // The expected result is only an assertion; no coefficient of r was seeded.
        assert!(
            input(&module, "principalProduct")
                .iter()
                .all(|e| !(e.verb == "inputCoefficient" && e.args[0] == Term::Const("r".into())))
        );
    }
}

fn semantic_proofs(closure: &Closure) -> BTreeMap<Event, Vec<String>> {
    let mut proofs: BTreeMap<Event, Vec<String>> = BTreeMap::new();
    for d in &closure.derivations {
        proofs
            .entry(d.event.clone())
            .or_default()
            .push(format!("{:?}", d.record));
    }
    for p in proofs.values_mut() {
        p.sort();
    }
    proofs
}

#[test]
fn profile_fixed_rules_incremental_preserves_events_and_provenance() {
    let module = load("forward_incremental.res");
    let base = input(&module, "base");
    let delta = input(&module, "delta");
    let rules = module
        .declarations
        .iter()
        .filter_map(|d| match d {
            Declaration::Rule(r) => Some(r.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    let mut incremental = IncrementalClosure::new(base.clone(), &rules, &mut Clock::default());
    let session = profile::Session::new("fixed-rules incremental update");
    let change = incremental.update(delta.clone(), &mut Clock::default());
    let update = session.finish();
    let session = profile::Session::new("fixed-rules full recomputation");
    let recomputed = close(
        base.into_iter().chain(delta.clone()).collect(),
        &rules,
        &mut Clock::default(),
    );
    let full = session.finish();
    assert_eq!(
        incremental.closure().known.iter().collect::<BTreeSet<_>>(),
        recomputed.known.iter().collect()
    );
    assert_eq!(
        semantic_proofs(incremental.closure()),
        semantic_proofs(&recomputed)
    );
    assert_eq!(change.derivations.len(), 2);
    println!(
        "INCREMENTAL COMPARISON update_probes={} recompute_probes={} update_evaluations={} recompute_evaluations={} update_candidates={} recompute_candidates={}",
        update.probes,
        full.probes,
        update.evaluations,
        full.evaluations,
        update.candidates,
        full.candidates
    );
    // Observation, not a general speedup law. A duplicate delta must do no work.
    let session = profile::Session::new("fixed-rules duplicate update");
    let duplicate = incremental.update(delta, &mut Clock::default());
    let no_work = session.finish();
    assert!(duplicate.known.is_empty() && duplicate.derivations.is_empty());
    assert_eq!((no_work.probes, no_work.evaluations), (0, 0));
}

#[test]
fn indexed_known_matches_linear_product_with_identical_provenance() {
    let (module, seeds) = product("partialProduct");
    let (original, linear) = {
        let _scan = profile::linear_scan();
        let session = profile::Session::new("partialProduct linear");
        let closure =
            close_program_reference(seeds.clone(), &module, &mut Clock::default()).unwrap();
        (closure, session.finish())
    };
    let session = profile::Session::new("partialProduct indexed");
    let indexed = {
        let _header = profile::header_only_index();
        close_program_reference(seeds, &module, &mut Clock::default()).unwrap()
    };
    let stats = session.finish();
    assert_eq!(format!("{original:?}"), format!("{indexed:?}"));
    assert_eq!(linear.probes, 2_117_296);
    assert_eq!(linear.header_rejects, 2_023_990);
    assert_eq!(stats.probes, linear.probes - linear.header_rejects);
    assert_eq!(stats.header_rejects, 0);
    assert_eq!(stats.structural_rejects, linear.structural_rejects);
    assert_eq!(
        (
            stats.rounds,
            stats.evaluations,
            stats.activated,
            stats.candidates,
            stats.duplicates,
            stats.comparisons
        ),
        (
            linear.rounds,
            linear.evaluations,
            linear.activated,
            linear.candidates,
            linear.duplicates,
            linear.comparisons
        )
    );
}

#[test]
fn argument_index_matches_linear_product_with_identical_provenance() {
    // Item 1 of docs/semi-naive-pending-optimizations.md: the same closure, in
    // the same order with the same stamps, and fewer events probed than with
    // the header-only index, because bound arguments narrow the candidates.
    let (module, seeds) = product("partialProduct");
    let (original, linear) = {
        let _scan = profile::linear_scan();
        let session = profile::Session::new("partialProduct linear");
        let closure =
            close_program_reference(seeds.clone(), &module, &mut Clock::default()).unwrap();
        (closure, session.finish())
    };
    let header = {
        let _header = profile::header_only_index();
        let session = profile::Session::new("partialProduct header");
        close_program_reference(seeds.clone(), &module, &mut Clock::default()).unwrap();
        session.finish()
    };
    let session = profile::Session::new("partialProduct arguments");
    let indexed = close_program_reference(seeds, &module, &mut Clock::default()).unwrap();
    let stats = session.finish();
    assert_eq!(format!("{original:?}"), format!("{indexed:?}"));
    assert_eq!(stats.header_rejects, 0);
    assert!(
        stats.probes < header.probes,
        "{} / {}",
        stats.probes,
        header.probes
    );
    assert!(stats.structural_rejects <= header.structural_rejects);
    // Every probe the argument index skips was a structural reject before.
    assert_eq!(
        header.probes - stats.probes,
        header.structural_rejects - stats.structural_rejects
    );
    assert_eq!(
        (
            stats.rounds,
            stats.evaluations,
            stats.activated,
            stats.candidates,
            stats.duplicates,
            stats.comparisons
        ),
        (
            linear.rounds,
            linear.evaluations,
            linear.activated,
            linear.candidates,
            linear.duplicates,
            linear.comparisons
        )
    );
    eprintln!(
        "probes: linear {} header {} arguments {}; structural rejects: header {} arguments {}",
        linear.probes,
        header.probes,
        stats.probes,
        header.structural_rejects,
        stats.structural_rejects
    );
}

#[test]
fn argument_index_keeps_incremental_updates_equal_to_linear_scan() {
    // The incremental join reads Known through the argument index; compare a
    // base plus delta against the same update with the linear scan.
    let (module, seeds) = product("partialProduct");
    let rules = module
        .declarations
        .iter()
        .filter_map(|d| match d {
            Declaration::Rule(r) => Some(r.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    let split = seeds.len() / 2;
    let run = || {
        let mut state =
            IncrementalClosure::new(seeds[..split].to_vec(), &rules, &mut Clock::default());
        let delta = state.update(seeds[split..].to_vec(), &mut Clock::default());
        (format!("{:?}", state.closure()), format!("{delta:?}"))
    };
    let linear = {
        let _scan = profile::linear_scan();
        run()
    };
    assert_eq!(linear, run());
}

#[test]
fn depth_first_join_matches_copying_join_with_identical_provenance() {
    // Item 5 of docs/semi-naive-pending-optimizations.md: the same closure, in
    // the same order with the same stamps, and the same matching counters.
    let (module, seeds) = product("partialProduct");
    let (original, copying) = {
        let _reference = profile::reference_join();
        let session = profile::Session::new("partialProduct copying join");
        let closure =
            close_program_reference(seeds.clone(), &module, &mut Clock::default()).unwrap();
        (closure, session.finish())
    };
    let session = profile::Session::new("partialProduct depth-first join");
    let closure = close_program_reference(seeds, &module, &mut Clock::default()).unwrap();
    let stats = session.finish();
    assert_eq!(format!("{original:?}"), format!("{closure:?}"));
    assert_eq!(
        (
            stats.rounds,
            stats.evaluations,
            stats.candidates,
            stats.duplicates,
            stats.comparisons,
            stats.probes,
            stats.header_rejects,
            stats.structural_rejects
        ),
        (
            copying.rounds,
            copying.evaluations,
            copying.candidates,
            copying.duplicates,
            copying.comparisons,
            copying.probes,
            copying.header_rejects,
            copying.structural_rejects
        )
    );
}

#[test]
fn depth_first_delta_join_keeps_incremental_updates() {
    // The delta join with pivots, frontier exclusion and initial bindings:
    // ordinary rules, then the module closure with program activations.
    let module = load("peano_polynomial_product_scenario.res");
    let rules = module
        .declarations
        .iter()
        .filter_map(|d| match d {
            Declaration::Rule(r) => Some(r.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    for name in ["unitProduct", "gapsProduct", "partialProduct"] {
        let seeds = input(&module, name);
        let split = seeds.len() / 2;
        let run = || {
            let mut clock = Clock::default();
            let mut ordinary = IncrementalClosure::new(seeds[..split].to_vec(), &rules, &mut clock);
            let mut programs =
                IncrementalProgramClosure::new(seeds[..split].to_vec(), &module, &mut clock)
                    .unwrap();
            let mut trace = String::new();
            for seed in &seeds[split..] {
                let a = ordinary.update(vec![seed.clone()], &mut clock);
                let b = programs.update(vec![seed.clone()], &mut clock);
                trace.push_str(&format!("{a:?}\n{b:?}\n"));
            }
            format!("{trace}{:?}\n{:?}", ordinary.closure(), programs.closure())
        };
        let expected = {
            let _reference = profile::reference_join();
            run()
        };
        assert_eq!(expected, run(), "{name}");
    }
}

#[test]
fn depth_first_delta_join_keeps_batch_updates_and_temporal_boundaries() {
    // Batches put several events in the first frontier, so a match can have
    // several frontier witnesses and the exclusion before the pivot is used.
    // Every self-contained base/delta fixture, the temporal boundary one
    // included (owns_consumer and protection* need a shared library), plus
    // the product seeds in one batch and in two.
    let fixtures = [
        "dynamic_incremental_temporal_boundary.res",
        "forward_incremental.res",
        "forward_provenance.res",
        "owns_program.res",
    ];
    let mut cases: Vec<(String, Module, Vec<Event>, Vec<Vec<Event>>)> = Vec::new();
    for file in fixtures {
        let module = load(file);
        let (base, delta) = (input(&module, "base"), input(&module, "delta"));
        cases.push((file.to_string(), module, base, vec![delta]));
    }
    let module = load("peano_polynomial_product_scenario.res");
    for name in ["unitProduct", "gapsProduct", "partialProduct"] {
        let seeds = input(&module, name);
        let (third, half) = (seeds.len() / 3, seeds.len() / 2);
        cases.push((
            format!("{name} one batch"),
            module.clone(),
            seeds[..third].to_vec(),
            vec![seeds[third..].to_vec()],
        ));
        cases.push((
            format!("{name} two batches"),
            module.clone(),
            seeds[..third].to_vec(),
            vec![seeds[third..half].to_vec(), seeds[half..].to_vec()],
        ));
    }
    let mut multiple = 0;
    for (name, module, base, batches) in &cases {
        let rules = module
            .declarations
            .iter()
            .filter_map(|d| match d {
                Declaration::Rule(r) => Some(r.clone()),
                _ => None,
            })
            .collect::<Vec<_>>();
        let run = || {
            let mut clock = Clock::default();
            let mut ordinary = IncrementalClosure::new(base.clone(), &rules, &mut clock);
            let mut programs =
                IncrementalProgramClosure::new(base.clone(), module, &mut clock).unwrap();
            let mut trace = String::new();
            for batch in batches {
                let a = ordinary.update(batch.clone(), &mut clock);
                let b = programs.update(batch.clone(), &mut clock);
                trace.push_str(&format!("{a:?}\n{b:?}\n"));
            }
            format!("{trace}{:?}\n{:?}", ordinary.closure(), programs.closure())
        };
        let expected = {
            let _reference = profile::reference_join();
            run()
        };
        assert_eq!(expected, run(), "{name}");
        multiple += batches.iter().filter(|b| b.len() > 1).count();
    }
    // At least the nine product batches carry several events each.
    assert!(multiple >= 9, "{multiple}");
}

#[test]
fn indexed_known_preserves_negative_cycles_unit_and_new_justifications() {
    let module = load("discrete_derivative.res");
    let rules = module
        .declarations
        .iter()
        .filter_map(|d| match d {
            Declaration::Rule(r) => Some(r.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    let events = module
        .declarations
        .iter()
        .find_map(|d| match d {
            Declaration::Experiment(e) if e.name == "universe" => Some(e.input.clone()),
            _ => None,
        })
        .unwrap();
    // Every finite seed subset, including empty evidence, both polarities,
    // duplicate seeds, Unit, a cycle and alternative witnesses for old events.
    for mask in 0..(1 << events.len()) {
        let mut seeds = events
            .iter()
            .enumerate()
            .filter(|(i, _)| mask & (1 << i) != 0)
            .map(|(_, e)| e.clone())
            .collect::<Vec<_>>();
        if let Some(first) = seeds.first().cloned() {
            seeds.push(first);
        }
        let original = {
            let _scan = profile::linear_scan();
            close(seeds.clone(), &rules, &mut Clock::default())
        };
        let indexed = close(seeds, &rules, &mut Clock::default());
        assert_eq!(
            format!("{original:?}"),
            format!("{indexed:?}"),
            "seed mask {mask}"
        );
    }
}

#[test]
fn known_header_index_preserves_order_identity_and_all_three_keys() {
    let (module, mut events) = product("unitProduct");
    // Index a mixed-arity typed fixture, both explicit polarities and a duplicate
    // representation. The index itself must preserve the supplied Vec exactly.
    let mut negative = events[0].clone();
    negative.polarity = Polarity::EvidentialNot;
    events.insert(1, negative);
    events.push(events[0].clone());
    let index = KnownIndex::new(&events);
    for pattern in &events {
        let expected = events
            .iter()
            .filter(|e| {
                e.verb == pattern.verb
                    && e.polarity == pattern.polarity
                    && e.args.len() == pattern.args.len()
            })
            .collect::<Vec<_>>();
        let actual = KnownView {
            events: &events,
            index: Some(&index),
        }
        .candidates(pattern)
        .collect::<Vec<_>>();
        assert_eq!(actual.len(), expected.len());
        assert!(
            actual
                .iter()
                .zip(expected)
                .all(|(a, b)| std::ptr::eq(*a, b))
        );
    }
    let mut missing = events[0].clone();
    missing.verb = "absentFromKnown".into();
    assert_eq!(
        KnownView {
            events: &events,
            index: Some(&index)
        }
        .candidates(&missing)
        .count(),
        0
    );
    // The same header is indexed immediately when a new fact is appended.
    let next = input(&module, "unitProduct").pop().unwrap();
    let mut updated = index;
    updated.insert(events.len(), &next);
    events.push(next.clone());
    assert!(std::ptr::eq(
        KnownView {
            events: &events,
            index: Some(&updated)
        }
        .candidates(&next)
        .last()
        .unwrap(),
        events.last().unwrap()
    ));
}

#[test]
fn semi_naive_product_preserves_exact_provenance_and_reports_matching_cost() {
    let (module, seeds) = product("partialProduct");
    let reference_session = profile::Session::new("partialProduct indexed reference");
    let reference = close_program_reference(seeds.clone(), &module, &mut Clock::default()).unwrap();
    let full = reference_session.finish();
    let delta_session = profile::Session::new("partialProduct semi-naive");
    let incremental = close_program(seeds, &module, &mut Clock::default()).unwrap();
    let inc = delta_session.finish();
    let observations = |c: &Closure| {
        let known = c
            .known
            .iter()
            .map(|e| format!("{e:?}"))
            .collect::<BTreeSet<_>>();
        let mut proofs = c
            .derivations
            .iter()
            .map(|d| format!("{:?} {:?}", d.event, d.record))
            .collect::<Vec<_>>();
        proofs.sort();
        (known, proofs)
    };
    assert_eq!(observations(&incremental), observations(&reference));
    assert_eq!(
        (incremental.known.len(), incremental.derivations.len()),
        (223, 244)
    );
    assert_eq!(inc.activated, full.activated);
    println!(
        "FIXED POINT comparison: probes {} -> {}, raw candidates {} -> {}, repeated justifications {} -> {}; timing is an observation, not a general bound",
        full.probes, inc.probes, full.candidates, inc.candidates, full.duplicates, inc.duplicates
    );
}

#[test]
fn profile_semi_naive_polynomial_product_fixture() {
    let name =
        std::env::var("RESIDUUM_PROFILE_PRODUCT").unwrap_or_else(|_| "partialProduct".into());
    assert!(["partialProduct", "principalProduct"].contains(&name.as_str()));
    let (module, seeds) = product(&name);
    let session = profile::Session::new("semi-naive product fixture");
    let c = close_program(seeds.clone(), &module, &mut Clock::default()).unwrap();
    let _stats = session.finish();
    let goal = module
        .declarations
        .iter()
        .find_map(|d| match d {
            Declaration::Experiment(e) if e.name == name => Some(&e.goal),
            _ => None,
        })
        .unwrap();
    assert!(c.known.contains(goal));
    if name == "partialProduct" {
        assert_eq!((c.known.len(), c.derivations.len()), (223, 244));
    }
    if name == "principalProduct" {
        fn natural(t: &Term) -> usize {
            match t {
                Term::Const(n) if n == "zeroTime" => 0,
                Term::Constructor {
                    constructor: crate::typed::Constructor::After,
                    argument,
                } => 1 + natural(argument),
                _ => panic!("ground Peano natural required"),
            }
        }
        let coefficients = c
            .known
            .iter()
            .filter(|e| e.verb == "coefficient" && e.args[0] == Term::Const("r".into()))
            .map(|e| (natural(&e.args[1]), natural(&e.args[2])))
            .collect::<Vec<_>>();
        assert_eq!(coefficients.len(), 7);
        assert_eq!(
            coefficients.into_iter().collect::<BTreeMap<_, _>>(),
            [5, 10, 18, 26, 9, 12, 0].into_iter().enumerate().collect()
        );
        assert!(
            seeds
                .iter()
                .all(|e| !(e.verb == "inputCoefficient" && e.args[0] == Term::Const("r".into())))
        );
    }
    println!(
        "FIXED POINT: {name}, {} events / {} justifications; no evidence supplied for output coefficients",
        c.known.len(),
        c.derivations.len()
    );
}

#[test]
fn bounded_program_scaling_observes_work_without_changing_evaluation() {
    let name = std::env::var("RESIDUUM_SCALING_CASE").unwrap_or_else(|_| "depth0".into());
    assert!(
        [
            "depth0",
            "depth2",
            "depth4",
            "jobs4",
            "jobs9",
            "jobs25",
            "multiplications",
            "proofs1",
            "proofs4",
            "proofs16",
        ]
        .contains(&name.as_str())
    );
    let evaluator =
        std::env::var("RESIDUUM_SCALING_EVALUATOR").unwrap_or_else(|_| "incremental".into());
    assert!(["incremental", "reference"].contains(&evaluator.as_str()));
    let module = load(if name.starts_with("proofs") {
        "program_proof_scaling.res"
    } else {
        "program_incremental_scaling.res"
    });
    let e = module
        .declarations
        .iter()
        .find_map(|d| match d {
            Declaration::Experiment(e) if e.name == name => Some(e),
            _ => None,
        })
        .unwrap();
    let session = profile::Session::new("bounded-program-scaling");
    let c = if evaluator == "incremental" {
        close_program(e.input.clone(), &module, &mut Clock::default())
    } else {
        close_program_reference(e.input.clone(), &module, &mut Clock::default())
    }
    .unwrap();
    let stats = session.finish();
    assert!(c.known.contains(&e.goal));
    assert_eq!(stats.candidates - stats.duplicates, c.derivations.len());
    let requests = e
        .input
        .iter()
        .filter(|e| e.verb == "add" || e.verb == "multiply")
        .count();
    let completed = c
        .known
        .iter()
        .filter(|e| e.verb == "completed" || e.verb == "productCompleted")
        .count();
    // In multiplication, completed also observes nested addition invocations.
    assert!(completed >= requests);
    if name.starts_with("proofs") {
        let n: usize = name[6..].parse().unwrap();
        assert_eq!(
            (c.known.len(), c.derivations.len(), stats.activated),
            (2, n, n)
        );
    }
    println!(
        "SCALING case={name} evaluator={evaluator} seeds={} requests={requests} events={} proofs={} activated_rules={} probes={} candidates={} duplicates={} evaluations={}",
        e.input.len(),
        c.known.len(),
        c.derivations.len(),
        stats.activated,
        stats.probes,
        stats.candidates,
        stats.duplicates,
        stats.evaluations
    );
}
