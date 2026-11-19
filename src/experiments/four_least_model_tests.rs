//! The knowledge-least model against the finite enumeration, which stays the
//! oracle on its domain of at most four ground atoms.

use super::four::{entailment, meet_of_models};
use super::*;
use crate::parse_formal_to_typed;
use crate::typed::{Antecedent, Event, ExperimentQueryKind, HornClause, Polarity, RuleBody};

const FOUR: &str = include_str!("../../examples/experiments/four_counterexample.res");

/// Every source fixture that declares a fourFusion query.
const FIXTURES: [&str; 11] = [
    "examples/experiments/theory_bridge.res",
    "examples/experiments/theory_bridge_tensor.res",
    "examples/experiments/composition_domain.res",
    "examples/experiments/discrete_derivative.res",
    "examples/experiments/dynamic_incremental_programs.res",
    "examples/experiments/four_counterexample.res",
    "examples/experiments/legal_geometry/general.res",
    "examples/experiments/legal_geometry/identifiability_cases.res",
    "examples/experiments/legal_geometry/patrimonial.res",
    "examples/experiments/legal_geometry/reference.res",
    "examples/experiments/legal_geometry/region_revision.res",
];

fn rules_of(module: &crate::typed::Module) -> Vec<Rule> {
    module
        .declarations
        .iter()
        .filter_map(|d| match d {
            Declaration::Rule(rule) => Some(rule.clone()),
            _ => None,
        })
        .collect()
}

#[test]
fn least_model_matches_enumeration_on_every_four_fixture() {
    let mut compared = 0;
    let mut beyond_enumeration = 0;
    let mut rejected = std::collections::BTreeMap::<String, usize>::new();
    for path in FIXTURES {
        let module = crate::load_formal_module(path).unwrap();
        let rules = rules_of(&module);
        for declaration in &module.declarations {
            let Declaration::Experiment(experiment) = declaration else {
                continue;
            };
            if experiment.query_kind != ExperimentQueryKind::FourFusion {
                continue;
            }
            let program = match GroundProgram::from_ground_rules(experiment, &rules) {
                Ok(program) => program,
                Err(error) => {
                    *rejected.entry(error.to_string()).or_default() += 1;
                    continue;
                }
            };
            let least = four_least_model(&program);
            match entailment(&program) {
                Ok(oracle) => {
                    assert_eq!(
                        least.entailed, oracle.entailed,
                        "{path} {}",
                        experiment.name
                    );
                    let (meet, _) = meet_of_models(&program);
                    assert_eq!(least.values, meet, "{path} {}", experiment.name);
                    compared += 1;
                }
                Err(error) => {
                    assert!(error.to_string().contains("at most four"), "{error}");
                    beyond_enumeration += 1;
                }
            }
        }
    }
    // The counts reported in docs/semi-naive-pending-optimizations.md §12.
    let by_reason = |needle: &str| {
        rejected
            .iter()
            .filter(|(reason, _)| reason.contains(needle))
            .map(|(_, count)| count)
            .sum::<usize>()
    };
    assert_eq!(
        (
            compared,
            beyond_enumeration,
            by_reason("requires ground rules"),
            by_reason("constant arguments"),
            rejected.values().sum::<usize>()
        ),
        (8, 0, 30, 1, 31),
        "{rejected:?}"
    );
}

#[test]
fn least_model_of_the_contraposition_counterexample() {
    let module = parse_formal_to_typed(FOUR).unwrap();
    let Some(Declaration::Experiment(experiment)) = module
        .declarations
        .iter()
        .find(|d| matches!(d, Declaration::Experiment(_)))
    else {
        panic!("experiment");
    };
    let program = GroundProgram::from_ground_rules(experiment, &rules_of(&module)).unwrap();
    let least = four_least_model(&program);
    // Premise ~Q gives n(Q); P <= Q carries n back to P. Nothing gives p.
    assert_eq!(least.values, vec![(false, true), (false, true)]);
    assert!(least.entailed);
    assert_eq!(least.clauses, 3);
}

#[test]
fn least_model_lifts_the_four_atom_bound() {
    // A chain of six atoms: enumeration refuses, the least model propagates.
    let source = format!(
        "{FOUR}\nderived verb R()\nderived verb S()\nderived verb T()\nderived verb U()\n\
         rule r() = R() @ tau <= P() @ tau\nrule s() = S() @ tau <= R() @ tau\n\
         rule t() = T() @ tau <= S() @ tau\nrule u() = U() @ tau <= T() @ tau\n\
         experiment chain {{\n    premises {{\n        ~Q() @ tau,\n    }}\n    query fourFusion ~U() @ tau\n}}\n"
    );
    let module = parse_formal_to_typed(&source).unwrap();
    let rules = rules_of(&module);
    let chain = module
        .declarations
        .iter()
        .find_map(|d| match d {
            Declaration::Experiment(e) if e.name == "chain" => Some(e),
            _ => None,
        })
        .unwrap();
    let program = GroundProgram::from_ground_rules(chain, &rules).unwrap();
    assert!(
        entailment(&program)
            .unwrap_err()
            .to_string()
            .contains("at most four")
    );
    let least = four_least_model(&program);
    assert_eq!(least.atoms.len(), 6);
    // Premise, then a forward and a backward clause for each of the five rules.
    assert_eq!(least.clauses, 11);
    assert!(least.entailed);
    assert!(least.values.iter().all(|&(p, n)| !p && n));
}

/// Deterministic xorshift, so the comparison is reproducible without crates.
struct Random(u64);
impl Random {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn chance(&mut self, percent: u64) -> bool {
        self.next() % 100 < percent
    }
}

fn literal(atoms: &[Event], random: &mut Random, positive_percent: u64) -> Event {
    let mut event = atoms[random.below(atoms.len())].clone();
    if !random.chance(positive_percent) {
        event.polarity = Polarity::EvidentialNot;
    }
    event
}

fn antecedent(atoms: &[Event], random: &mut Random, depth: usize) -> Antecedent {
    let roll = random.below(100);
    if depth == 0 || roll < 40 {
        Antecedent::Event(literal(atoms, random, 60))
    } else if roll < 47 {
        Antecedent::Unit
    } else {
        Antecedent::And(
            Box::new(antecedent(atoms, random, depth - 1)),
            Box::new(antecedent(atoms, random, depth - 1)),
        )
    }
}

#[test]
fn least_model_matches_enumeration_on_random_ground_programs() {
    // Templates from the fixture: four atoms with constant arguments and one time.
    let base = format!("{FOUR}\nderived verb R()\nderived verb S()\n");
    let module = parse_formal_to_typed(&base).unwrap();
    let Some(Declaration::Experiment(template)) = module
        .declarations
        .iter()
        .find(|d| matches!(d, Declaration::Experiment(_)))
    else {
        panic!("experiment");
    };
    let rule_template = rules_of(&module).remove(0);
    let mut atoms: Vec<Event> = ["P", "Q", "R", "S"]
        .iter()
        .map(|verb| {
            let mut event = template.goal.clone();
            event.verb = verb.to_string();
            event.polarity = Polarity::Positive;
            event
        })
        .collect();
    atoms.sort();
    let mut random = Random(0x9e37_79b9_7f4a_7c15);
    let (mut entailed, mut refuted) = (0, 0);
    for trial in 0..3000 {
        let universe = &atoms[..1 + random.below(atoms.len())];
        let mut experiment = template.clone();
        experiment.input = (0..random.below(3))
            .map(|_| literal(universe, &mut random, 70))
            .collect();
        experiment.goal = literal(universe, &mut random, 60);
        let rules: Vec<Rule> = (0..random.below(5))
            .map(|i| {
                let mut rule = rule_template.clone();
                rule.name = format!("r{i}");
                rule.body = RuleBody::HornClause(HornClause {
                    antecedent: antecedent(universe, &mut random, 3),
                    consequent: literal(universe, &mut random, 60),
                });
                rule
            })
            .collect();
        let program = GroundProgram::from_ground_rules(&experiment, &rules).unwrap();
        let oracle = entailment(&program).unwrap();
        let least = four_least_model(&program);
        assert_eq!(least.entailed, oracle.entailed, "trial {trial}: {rules:?}");
        let (meet, _) = meet_of_models(&program);
        assert_eq!(least.values, meet, "trial {trial}: {rules:?}");
        if oracle.entailed {
            entailed += 1;
        } else {
            refuted += 1;
        }
    }
    // Both outcomes occur, so the comparison is not vacuous.
    assert!(entailed > 100 && refuted > 100, "{entailed} / {refuted}");
}

#[test]
fn least_model_equals_the_meet_of_models_beyond_four_atoms() {
    // Five or six atoms, where `entailment` refuses: the oracle is the
    // unbounded enumeration (at most 4^6 interpretations per trial).
    let verbs = ["P", "Q", "R", "S", "T", "U"];
    let mut base = format!("{FOUR}\n");
    for verb in &verbs[2..] {
        base.push_str(&format!("derived verb {verb}()\n"));
    }
    let module = parse_formal_to_typed(&base).unwrap();
    let Some(Declaration::Experiment(template)) = module
        .declarations
        .iter()
        .find(|d| matches!(d, Declaration::Experiment(_)))
    else {
        panic!("experiment");
    };
    let rule_template = rules_of(&module).remove(0);
    let mut atoms: Vec<Event> = verbs
        .iter()
        .map(|verb| {
            let mut event = template.goal.clone();
            event.verb = verb.to_string();
            event.polarity = Polarity::Positive;
            event
        })
        .collect();
    atoms.sort();
    let mut random = Random(0x2545_f491_4f6c_dd1d);
    let (mut entailed, mut refuted, mut beyond) = (0, 0, 0);
    for trial in 0..150 {
        let universe = &atoms[..5 + random.below(2)];
        let mut experiment = template.clone();
        experiment.input = (0..1 + random.below(3))
            .map(|_| literal(universe, &mut random, 70))
            .collect();
        experiment.goal = literal(universe, &mut random, 60);
        let rules: Vec<Rule> = (0..2 + random.below(6))
            .map(|i| {
                let mut rule = rule_template.clone();
                rule.name = format!("r{i}");
                rule.body = RuleBody::HornClause(HornClause {
                    antecedent: antecedent(universe, &mut random, 3),
                    consequent: literal(universe, &mut random, 60),
                });
                rule
            })
            .collect();
        let program = GroundProgram::from_ground_rules(&experiment, &rules).unwrap();
        let least = four_least_model(&program);
        let (meet, oracle) = meet_of_models(&program);
        assert_eq!(least.values, meet, "trial {trial}: {rules:?}");
        assert_eq!(least.entailed, oracle, "trial {trial}: {rules:?}");
        if least.atoms.len() > 4 {
            beyond += 1;
        }
        if oracle {
            entailed += 1;
        } else {
            refuted += 1;
        }
    }
    assert!(beyond > 50, "{beyond}");
    assert!(entailed > 10 && refuted > 10, "{entailed} / {refuted}");
}
