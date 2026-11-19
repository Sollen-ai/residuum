//! fourFusion over an explicit `using` scope with `with` bindings: the same
//! scope selection and binding checks as residual queries, then every rule in
//! scope instantiated, with the enumeration as the oracle.

use super::four::{entailment, meet_of_models};
use super::*;
use std::path::Path;

const FIXTURE: &str = "examples/experiments/four_scoped_bindings.res";

fn load(file: &str) -> Module {
    crate::load_formal_module(Path::new(env!("CARGO_MANIFEST_DIR")).join(file)).unwrap()
}
fn experiment<'a>(m: &'a Module, name: &str) -> &'a Experiment {
    m.declarations
        .iter()
        .find_map(|d| match d {
            Declaration::Experiment(e) if e.name == name => Some(e),
            _ => None,
        })
        .unwrap()
}

#[test]
fn bound_rules_and_programs_give_contraposition_that_horn_misses() {
    let m = load(FIXTURE);
    let results = run_experiments(&m).unwrap();
    let by_name = |name: &str| results.iter().find(|r| r.experiment.name == name).unwrap();
    for name in ["contraposition", "program"] {
        let result = by_name(name);
        let four = result.four.as_ref().unwrap();
        assert!(four.scoped, "{name}");
        assert!(four.entailed(), "{name}");
        assert!(!result.horn_goal, "{name}");
        // Two atoms, so the enumeration ran and agrees.
        assert_eq!(
            four.enumeration,
            Some(FourEntailment {
                interpretations: 16,
                models: 3,
                entailed: true
            }),
            "{name}"
        );
        let program = GroundProgram::for_experiment(&m, &result.experiment).unwrap();
        assert_eq!(four.least_model.values, meet_of_models(&program).0);
    }
    // bob's instance does not mention alice's Served: false within the scope.
    let other = by_name("otherInstance").four.as_ref().unwrap();
    assert!(other.scoped && !other.entailed());
    assert_eq!(other.enumeration.as_ref().map(|e| e.entailed), Some(false));
    let output = render_results(&results);
    assert!(
        output.contains("FOUR least model: true (goal T; 2 atoms, 3 clauses; explicit scope)\n")
    );
    // ~Served(alice) is N: nothing constrains alice's Served in bob's instance.
    assert!(
        output.contains("FOUR least model: false (goal N; 4 atoms, 3 clauses; explicit scope)\n")
    );
}

#[test]
fn unbound_parameters_are_errors_naming_the_binding_that_fixes_them() {
    let m = load(FIXTURE);
    let mut e = experiment(&m, "contraposition").clone();
    e.query_options.bindings.retain(|b| b.parameter != "t");
    let error = GroundProgram::for_experiment(&m, &e)
        .unwrap_err()
        .to_string();
    assert!(error.contains("`rule service.t` is not"), "{error}");
    let mut e = experiment(&m, "program").clone();
    e.query_options.bindings.retain(|b| b.parameter != "person");
    let error = GroundProgram::for_experiment(&m, &e)
        .unwrap_err()
        .to_string();
    assert!(error.contains("`program Service.person` is not"), "{error}");
    // Bindings without a scope are rejected, not ignored, also from the API.
    let mut e = experiment(&m, "contraposition").clone();
    e.query_options.scope = None;
    let error = GroundProgram::for_experiment(&m, &e)
        .unwrap_err()
        .to_string();
    assert!(
        error.contains("require an explicit search scope"),
        "{error}"
    );
    // Without a scope the rule keeps its parameters: the existing rejection.
    let mut e = experiment(&m, "contraposition").clone();
    e.query_options = Default::default();
    let rules: Vec<_> = m
        .declarations
        .iter()
        .filter_map(|d| match d {
            Declaration::Rule(r) => Some(r.clone()),
            _ => None,
        })
        .collect();
    assert!(
        GroundProgram::from_ground_rules(&e, &rules)
            .unwrap_err()
            .to_string()
            .contains("requires ground rules")
    );
}

#[test]
fn source_options_reject_active_mode_and_scope_violations() {
    let source =
        std::fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join(FIXTURE)).unwrap();
    for (from, to, message) in [
        (
            "query fourFusion ~Served(alice) @ tau\n    using rules { service }\n    with {\n        rule service.person = alice,",
            "query active fourFusion ~Served(alice) @ tau\n    using rules { service }\n    with {\n        rule service.person = alice,",
            "fourFusion does not accept active mode",
        ),
        (
            "    using rules { service }\n    with {\n        rule service.person = alice,",
            "    with {\n        rule service.person = alice,",
            "explicit query bindings require an explicit search scope",
        ),
        (
            "rule service.person = alice,\n        rule service.t = tau",
            "rule service.person = alice,\n        rule service.t = tau,\n        rule service.person = bob",
            "duplicate query binding",
        ),
        (
            "rule service.person = alice,\n        rule service.t = tau",
            "rule service.person = tau,\n        rule service.t = tau",
            "has type",
        ),
    ] {
        assert_eq!(source.matches(from).count(), 1, "{from}");
        let text = source.replacen(from, to, 1);
        let error = crate::parse_formal_to_typed(&text).unwrap_err().to_string();
        assert!(error.contains(message), "{message}: {error}");
    }
}

#[test]
fn scoped_and_unscoped_ground_programs_agree_on_ground_rules() {
    // On the counterexample fixture, scoping its only (ground) rule changes
    // nothing but the flag.
    let source = format!(
        "{}\nexperiment scoped {{\n    premises {{\n        ~Q() @ tau,\n    }}\n    query fourFusion ~P() @ tau\n    using rules {{ implication }}\n}}\n",
        include_str!("../../examples/experiments/four_counterexample.res")
    );
    let m = crate::parse_formal_to_typed(&source).unwrap();
    let results = run_experiments(&m).unwrap();
    let (legacy, scoped) = (&results[0], &results[1]);
    let (a, b) = (legacy.four.as_ref().unwrap(), scoped.four.as_ref().unwrap());
    assert!(!a.scoped && b.scoped);
    assert_eq!(a.least_model, b.least_model);
    assert_eq!(a.enumeration, b.enumeration);
    let program = GroundProgram::for_experiment(&m, &scoped.experiment).unwrap();
    assert_eq!(
        entailment(&program).unwrap(),
        a.enumeration.clone().unwrap()
    );
}

fn fixture_source() -> String {
    std::fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join(FIXTURE)).unwrap()
}

#[test]
fn unbound_parameters_are_rejected_when_the_source_is_elaborated() {
    let source = fixture_source().replacen(
        "        rule service.person = alice,\n        rule service.t = tau\n",
        "        rule service.person = alice\n",
        1,
    );
    let error = crate::parse_formal_to_typed(&source)
        .unwrap_err()
        .to_string();
    assert!(error.contains("`rule service.t` is not"), "{error}");
}

#[test]
fn shared_parameters_that_a_use_never_mentions_need_no_binding() {
    // Two::0::service carries q and Two::1::logging carries p, as every
    // compiled rule carries all shared parameters; neither body mentions them.
    let source = format!(
        "{}\nderived verb Logged(person : Person)\nrule logging(other, t) =\n    Logged(other) @ t <= Notified(other) @ t\n\
         program Two(p : Person, q : Person, t : PropositionTime) {{\n    use service {{ person = p, t = t }}\n    use logging {{ other = q, t = t }}\n}}\n\
         experiment two {{\n    premises {{\n        ~Notified(alice) @ tau,\n    }}\n    query fourFusion ~Served(alice) @ tau\n    using program Two\n    with {{\n        program Two.p = alice,\n        program Two.q = bob,\n        program Two.t = tau\n    }}\n}}\n",
        fixture_source()
    );
    let m = crate::parse_formal_to_typed(&source).unwrap();
    let result = run_experiments(&m)
        .unwrap()
        .into_iter()
        .find(|r| r.experiment.name == "two")
        .unwrap();
    assert!(result.four.unwrap().entailed());
    // Leaving out q, which logging does mention, is still an error.
    let without_q = source.replacen("        program Two.q = bob,\n", "", 1);
    let error = crate::parse_formal_to_typed(&without_q)
        .unwrap_err()
        .to_string();
    assert!(error.contains("`program Two.q` is not"), "{error}");
}

#[test]
fn horn_observes_the_same_instances_that_four_evaluates() {
    // Served(alice) with only bob's instance in scope: neither Horn nor FOUR
    // may use alice's instance, which the bindings leave out.
    let source = fixture_source().replacen(
        "experiment otherInstance {\n    premises {\n        ~Notified(alice) @ tau,\n    }\n    query fourFusion ~Served(alice) @ tau",
        "experiment otherInstance {\n    premises {\n        Served(alice) @ tau,\n    }\n    query fourFusion Notified(alice) @ tau",
        1,
    );
    let m = crate::parse_formal_to_typed(&source).unwrap();
    let results = run_experiments(&m).unwrap();
    let other = results
        .iter()
        .find(|r| r.experiment.name == "otherInstance")
        .unwrap();
    assert!(!other.horn_goal);
    assert!(!other.four.as_ref().unwrap().entailed());
    assert_eq!(other.closure.known, other.experiment.input);
    // With alice's instance both see the forward step.
    let alice = source.replacen(
        "rule service.person = bob,",
        "rule service.person = alice,",
        1,
    );
    let m = crate::parse_formal_to_typed(&alice).unwrap();
    let results = run_experiments(&m).unwrap();
    let other = results
        .iter()
        .find(|r| r.experiment.name == "otherInstance")
        .unwrap();
    assert!(other.horn_goal && other.four.as_ref().unwrap().entailed());
}

#[test]
fn scoped_reports_print_their_scope_and_bindings() {
    let output = render_results(&run_experiments(&load(FIXTURE)).unwrap());
    let other = &output[output.find("experiment otherInstance").unwrap()..];
    let other = &other[..other.find("experiment program").unwrap()];
    assert!(
        other.contains("  search scope: rules {service}\n"),
        "{other}"
    );
    assert!(
        other.contains("  query bindings: {rule service.person = bob, rule service.t = tau}\n"),
        "{other}"
    );
    assert!(output.contains("  search scope: program Service\n"));
}
