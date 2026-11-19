//! Minimal proof costs against two references: plain relaxation until no
//! change (Bellman-Ford over the justification hypergraph) and, for stages,
//! the rounds of the synchronous Kleene iteration of `ForwardSession`.
use super::*;
use std::path::Path;

#[derive(Default)]
struct Clock(usize);
impl DerivationClock for Clock {
    fn next_derivation_time(&mut self) -> DerivationTime {
        self.0 += 1;
        DerivationTime {
            name: format!("cost-{}", self.0),
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
fn rules(module: &Module) -> Vec<Rule> {
    module
        .declarations
        .iter()
        .filter_map(|d| match d {
            Declaration::Rule(r) => Some(r.clone()),
            _ => None,
        })
        .collect()
}

/// Relax every justification until nothing improves. Independent of the
/// queue order and of the fixing argument used by `proof_cost`.
fn reference(
    closure: &Closure,
    seeds: &[Event],
    combine: impl Fn(&DerivedEvent, &[u64]) -> u64,
) -> ProofCosts {
    let position = |e: &Event| closure.known.iter().position(|k| k == e);
    let mut costs: Vec<Option<u64>> = vec![None; closure.known.len()];
    let seed: Vec<bool> = closure.known.iter().map(|e| seeds.contains(e)).collect();
    for (i, is_seed) in seed.iter().enumerate() {
        if *is_seed {
            costs[i] = Some(0);
        }
    }
    let value = |j: usize, costs: &[Option<u64>]| -> Option<u64> {
        let derived = &closure.derivations[j];
        let witnesses: Option<Vec<u64>> = derived
            .record
            .antecedents
            .iter()
            .map(|a| costs[position(a)?])
            .collect();
        Some(combine(derived, &witnesses?))
    };
    loop {
        let mut changed = false;
        for (j, derived) in closure.derivations.iter().enumerate() {
            let head = position(&derived.event).unwrap();
            if let Some(cost) = value(j, &costs) {
                if costs[head].is_none_or(|old| cost < old) {
                    costs[head] = Some(cost);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    let mut optimal = vec![Vec::new(); closure.known.len()];
    for (j, derived) in closure.derivations.iter().enumerate() {
        let head = position(&derived.event).unwrap();
        if !seed[head] && value(j, &costs).is_some() && value(j, &costs) == costs[head] {
            optimal[head].push(j);
        }
    }
    ProofCosts { costs, optimal }
}

fn size(derived: &DerivedEvent, witnesses: &[u64]) -> u64 {
    witnesses
        .iter()
        .fold(weight(derived), |total, cost| total.saturating_add(*cost))
}
/// A non-uniform weight, so ties and sums are not all equal by construction.
fn weight(derived: &DerivedEvent) -> u64 {
    1 + derived.record.rule.len() as u64 % 3
}
fn stage(_: &DerivedEvent, witnesses: &[u64]) -> u64 {
    1 + witnesses.iter().copied().max().unwrap_or(0)
}

#[test]
fn shared_has_two_minimal_proofs_and_the_axiom_has_stage_one() {
    let module = load("forward_provenance.res");
    let mut seeds = input(&module, "base");
    seeds.extend(input(&module, "delta"));
    let closure = close(seeds.clone(), &rules(&module), &mut Clock::default());
    let sizes = minimum_proof_sizes(&closure, &seeds, |_| 1);
    let stages = kleene_stages(&closure, &seeds);
    let by_verb = |costs: &ProofCosts, verb: &str| {
        let i = closure.known.iter().position(|e| e.verb == verb).unwrap();
        let rules: Vec<&str> = costs.optimal[i]
            .iter()
            .map(|&j| closure.derivations[j].record.rule.as_str())
            .collect();
        (costs.costs[i], rules)
    };
    assert_eq!(by_verb(&sizes, "A"), (Some(0), vec![]));
    assert_eq!(by_verb(&sizes, "B"), (Some(0), vec![]));
    // Two alternative one-step proofs; the tie is kept, not broken by order.
    let (cost, mut rules) = by_verb(&sizes, "shared");
    rules.sort();
    assert_eq!((cost, rules), (Some(1), vec!["fromA", "fromB"]));
    assert_eq!(by_verb(&sizes, "result"), (Some(2), vec!["consequence"]));
    assert_eq!(by_verb(&sizes, "ready"), (Some(1), vec!["axiom"]));
    assert_eq!(by_verb(&stages, "result").0, Some(2));
    assert_eq!(by_verb(&stages, "ready").0, Some(1));
}

#[test]
fn proof_costs_equal_relaxation_on_products_and_cycles() {
    let product = load("peano_polynomial_product_scenario.res");
    let cycles = load("discrete_derivative.res");
    let mut cases = Vec::new();
    for name in [
        "unitProduct",
        "gapsProduct",
        "partialProduct",
        "computedProductThenSum",
    ] {
        let seeds = input(&product, name);
        let closure =
            close_program_reference(seeds.clone(), &product, &mut Clock::default()).unwrap();
        cases.push((name.to_string(), closure, seeds));
    }
    // Every seed subset of the cyclic fixture, both polarities and Unit.
    let events = input(&cycles, "universe");
    for mask in 0..(1 << events.len()) {
        let seeds: Vec<Event> = events
            .iter()
            .enumerate()
            .filter(|(i, _)| mask & (1 << i) != 0)
            .map(|(_, e)| e.clone())
            .collect();
        let closure = close(seeds.clone(), &rules(&cycles), &mut Clock::default());
        cases.push((format!("cycles mask {mask}"), closure, seeds));
    }
    let mut ties = 0;
    for (name, closure, seeds) in &cases {
        let sizes = minimum_proof_sizes(closure, seeds, weight);
        assert_eq!(sizes, reference(closure, seeds, size), "{name} sizes");
        let unit = minimum_proof_sizes(closure, seeds, |_| 1);
        assert_eq!(
            unit,
            reference(closure, seeds, |_, w| 1 + w.iter().sum::<u64>()),
            "{name}"
        );
        let stages = kleene_stages(closure, seeds);
        assert_eq!(stages, reference(closure, seeds, stage), "{name} stages");
        // A closure only holds events with a proof from the seeds.
        assert!(stages.costs.iter().all(Option::is_some), "{name}");
        ties += unit.optimal.iter().filter(|o| o.len() > 1).count();
    }
    assert!(ties > 0, "no tie was exercised");
}

#[test]
fn kleene_stages_equal_rounds_of_the_synchronous_iteration() {
    // The stage of an event is the round of ForwardSession that adds it.
    let product = load("peano_polynomial_product_scenario.res");
    let provenance = load("forward_provenance.res");
    let mut compared = 0;
    for (module, name) in [
        (&product, "unitProduct"),
        (&product, "gapsProduct"),
        (&product, "partialProduct"),
        (&provenance, "base"),
    ] {
        let seeds = input(module, name);
        let mut session = ForwardSession::for_module(seeds.clone(), module).unwrap();
        let mut round_of: BTreeMap<Event, u64> = seeds.iter().map(|e| (e.clone(), 0)).collect();
        let mut clock = Clock::default();
        while !session.is_complete() {
            let step = session.step(&mut clock);
            for event in &step.added {
                round_of.entry(event.clone()).or_insert(step.round as u64);
            }
        }
        let closure = session.closure();
        let stages = kleene_stages(closure, &seeds);
        for (i, event) in closure.known.iter().enumerate() {
            assert_eq!(
                stages.costs[i],
                round_of.get(event).copied(),
                "{name} {event:?}"
            );
            compared += 1;
        }
    }
    assert!(compared > 100, "{compared}");
}

/// The cases of `proof_costs_equal_relaxation_on_products_and_cycles`.
fn cases() -> Vec<(String, Closure, Vec<Event>)> {
    let product = load("peano_polynomial_product_scenario.res");
    let cycles = load("discrete_derivative.res");
    let mut cases = Vec::new();
    for name in ["unitProduct", "partialProduct"] {
        let seeds = input(&product, name);
        let closure =
            close_program_reference(seeds.clone(), &product, &mut Clock::default()).unwrap();
        cases.push((name.to_string(), closure, seeds));
    }
    let events = input(&cycles, "universe");
    for mask in 0..(1 << events.len()) {
        let seeds: Vec<Event> = events
            .iter()
            .enumerate()
            .filter(|(i, _)| mask & (1 << i) != 0)
            .map(|(_, e)| e.clone())
            .collect();
        let closure = close(seeds.clone(), &rules(&cycles), &mut Clock::default());
        cases.push((format!("cycles mask {mask}"), closure, seeds));
    }
    cases
}

/// Following reported justifications from any event reaches only seeds:
/// the graph event → witness of an optimal justification has no cycle.
fn assert_well_founded(name: &str, closure: &Closure, costs: &ProofCosts) {
    fn visit(event: usize, closure: &Closure, costs: &ProofCosts, state: &mut [u8], name: &str) {
        match state[event] {
            2 => return,
            1 => panic!(
                "{name}: cyclic optimal proof through {:?}",
                closure.known[event]
            ),
            _ => {}
        }
        state[event] = 1;
        for &j in &costs.optimal[event] {
            for witness in &closure.derivations[j].record.antecedents {
                let w = closure.known.iter().position(|k| k == witness).unwrap();
                visit(w, closure, costs, state, name);
            }
        }
        state[event] = 2;
    }
    let mut state = vec![0u8; closure.known.len()];
    for event in 0..closure.known.len() {
        visit(event, closure, costs, &mut state, name);
    }
}

#[test]
fn zero_weights_keep_costs_and_report_only_well_founded_proofs() {
    let mut dropped = 0;
    for (name, closure, seeds) in cases() {
        let zero = minimum_proof_sizes(&closure, &seeds, |_| 0);
        let expected = reference(&closure, &seeds, |_, w| w.iter().sum());
        assert_eq!(zero.costs, expected.costs, "{name}");
        for (i, optimal) in zero.optimal.iter().enumerate() {
            assert!(
                optimal.iter().all(|j| expected.optimal[i].contains(j)),
                "{name}: reported a justification that does not attain the cost"
            );
            let is_seed = seeds.contains(&closure.known[i]);
            assert_eq!(
                optimal.is_empty(),
                is_seed || zero.costs[i].is_none(),
                "{name} {:?}",
                closure.known[i]
            );
            dropped += expected.optimal[i].len() - optimal.len();
        }
        assert_well_founded(&name, &closure, &zero);
        // Positive weights drop nothing, and are well-founded as well.
        let unit = minimum_proof_sizes(&closure, &seeds, |_| 1);
        assert_well_founded(&name, &closure, &unit);
        assert_well_founded(&name, &closure, &kleene_stages(&closure, &seeds));
    }
    assert!(
        dropped > 0,
        "no cyclic zero-cost justification was exercised"
    );
}

#[test]
fn events_without_proof_and_foreign_seeds() {
    // Closed from the whole universe, costed from a subset: the other
    // universe events and what depends only on them have no proof.
    let cycles = load("discrete_derivative.res");
    let universe = input(&cycles, "universe");
    let closure = close(universe.clone(), &rules(&cycles), &mut Clock::default());
    let seeds = vec![universe[0].clone()];
    let sizes = minimum_proof_sizes(&closure, &seeds, |_| 1);
    assert_eq!(
        sizes,
        reference(&closure, &seeds, |_, w| 1 + w.iter().sum::<u64>())
    );
    let unproved: Vec<usize> = (0..closure.known.len())
        .filter(|&i| sizes.costs[i].is_none())
        .collect();
    assert!(!unproved.is_empty());
    assert!(unproved.iter().all(|&i| sizes.optimal[i].is_empty()));
    assert_eq!(sizes.cost(&closure, &universe[0]), Some(0));
    // A seed that is not in Known changes nothing.
    let mut foreign = seeds.clone();
    let mut outside = universe[0].clone();
    outside.verb = "notInTheClosure".to_string();
    assert!(!closure.known.contains(&outside));
    foreign.push(outside.clone());
    assert_eq!(minimum_proof_sizes(&closure, &foreign, |_| 1), sizes);
    assert_eq!(
        kleene_stages(&closure, &foreign),
        kleene_stages(&closure, &seeds)
    );
    assert_eq!(sizes.cost(&closure, &outside), None);
}

#[test]
fn saturated_sizes_tie_at_the_maximum_without_overflow() {
    for (name, closure, seeds) in cases() {
        let sizes = minimum_proof_sizes(&closure, &seeds, |_| u64::MAX);
        for (i, event) in closure.known.iter().enumerate() {
            if seeds.contains(event) {
                assert_eq!(sizes.costs[i], Some(0), "{name}");
                continue;
            }
            assert_eq!(sizes.costs[i], Some(u64::MAX), "{name} {event:?}");
            assert!(!sizes.optimal[i].is_empty(), "{name} {event:?}");
        }
        assert_well_founded(&name, &closure, &sizes);
    }
}
