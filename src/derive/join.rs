//! Depth-first conjunctive join (docs/semi-naive-pending-optimizations.md §5).
//!
//! One bindings map is shared along the search and restored after each
//! attempt from an undo log of the parameters the pattern can bind, so no map
//! is cloned per candidate. Witnesses are references into Known until a match
//! is complete. Visiting atoms in order and candidates in Known order yields
//! the matches in the same order as the breadth-first join it replaces.
use super::{AntecedentMatch, KnownView, match_event};
use crate::typed::{Antecedent, Arg, Event, SubstitutionValue, Term, TimeExpr};
use std::collections::{BTreeMap, BTreeSet};

type Bindings = BTreeMap<String, SubstitutionValue>;
type Undo<'b> = Vec<&'b str>;

pub(super) fn leaves<'a>(antecedent: &'a Antecedent, atoms: &mut Vec<&'a Event>) {
    match antecedent {
        Antecedent::Unit => {}
        Antecedent::Event(event) => atoms.push(event),
        Antecedent::And(a, b) => {
            leaves(a, atoms);
            leaves(b, atoms);
        }
    }
}

/// Parameter names a pattern can bind, each once.
fn binders(pattern: &Event, parameters: &[Arg]) -> Vec<String> {
    fn parameter(name: &str, parameters: &[Arg], output: &mut BTreeSet<String>) {
        if parameters.iter().any(|p| p.name == name) {
            output.insert(name.to_string());
        }
    }
    fn term(t: &Term, parameters: &[Arg], output: &mut BTreeSet<String>) {
        match t {
            Term::Var(name) => parameter(name, parameters, output),
            Term::Constructor { argument, .. } => term(argument, parameters, output),
            Term::RecordLiteral { fields, .. } => {
                for field in fields {
                    term(&field.value, parameters, output);
                }
            }
            Term::Const(_) | Term::None => {}
        }
    }
    fn time(t: &TimeExpr, parameters: &[Arg], output: &mut BTreeSet<String>) {
        match t {
            TimeExpr::Var(name) => parameter(name, parameters, output),
            TimeExpr::After(inner) => time(inner, parameters, output),
            TimeExpr::At(_) => {}
        }
    }
    let mut output = BTreeSet::new();
    for arg in &pattern.args {
        term(arg, parameters, &mut output);
    }
    time(&pattern.proposition.time, parameters, &mut output);
    output.into_iter().collect()
}

/// Matches `pattern` against `event` in place. On success returns the
/// binders it added, to undo it; on failure the map is already restored.
///
/// Undoing an attempt only removes the binders that were absent before it.
/// That restores the map: `bind_typed` inserts canonical values, and when it
/// meets a binder that is already present it writes back the canonical form
/// of an equal value. Values inserted during the join are canonical already,
/// so the write-back is the same value. An initial value may not be (program
/// activation bindings are canonicalized with the program source's parameter
/// types, not the rule's); only a `PropositionTime` binder can then change
/// representation, from a term to the equal time. Such a rewrite survives
/// the undo, but is not observable: every complete match binds every binder
/// of every atom, so the output holds the canonical form either way, and the
/// argument index only reads values of non-time parameters, whose canonical
/// form is the value itself.
fn bind<'b>(
    pattern: &Event,
    event: &Event,
    parameters: &[Arg],
    binders: &'b [String],
    bindings: &mut Bindings,
) -> Option<Undo<'b>> {
    let absent: Undo<'b> = binders
        .iter()
        .map(String::as_str)
        .filter(|name| !bindings.contains_key(*name))
        .collect();
    if match_event(pattern, event, parameters, bindings).is_some() {
        Some(absent)
    } else {
        undo(absent, bindings);
        None
    }
}

fn undo(added: Undo<'_>, bindings: &mut Bindings) {
    for name in added {
        bindings.remove(name);
    }
}

struct Join<'a, 'k> {
    atoms: Vec<&'a Event>,
    binders: Vec<Vec<String>>,
    parameters: &'a [Arg],
    known: KnownView<'k>,
}
impl<'a, 'k> Join<'a, 'k> {
    fn new(antecedent: &'a Antecedent, parameters: &'a [Arg], known: KnownView<'k>) -> Self {
        let mut atoms = Vec::new();
        leaves(antecedent, &mut atoms);
        let binders = atoms.iter().map(|a| binders(a, parameters)).collect();
        Self {
            atoms,
            binders,
            parameters,
            known,
        }
    }
}

/// All matches of the atoms of `antecedent` in Known, after the `prefix`
/// witnesses, starting from `bindings`.
pub(super) fn match_antecedents(
    antecedent: &Antecedent,
    known: KnownView<'_>,
    parameters: &[Arg],
    mut bindings: Bindings,
    prefix: Vec<Event>,
) -> Vec<AntecedentMatch> {
    let join = Join::new(antecedent, parameters, known);
    let mut witnesses = Vec::with_capacity(join.atoms.len());
    let mut result = Vec::new();
    full(&join, &mut bindings, &mut witnesses, &prefix, &mut result);
    result
}

fn full<'k>(
    join: &Join<'_, 'k>,
    bindings: &mut Bindings,
    witnesses: &mut Vec<&'k Event>,
    prefix: &[Event],
    result: &mut Vec<AntecedentMatch>,
) {
    let position = witnesses.len();
    let Some(&pattern) = join.atoms.get(position) else {
        let mut antecedents = prefix.to_vec();
        antecedents.extend(witnesses.iter().map(|&e| e.clone()));
        result.push(AntecedentMatch {
            antecedents,
            substitutions: bindings.clone(),
        });
        return;
    };
    for event in join
        .known
        .candidates_bound(pattern, join.parameters, bindings)
    {
        let Some(saved) = bind(
            pattern,
            event,
            join.parameters,
            &join.binders[position],
            bindings,
        ) else {
            continue;
        };
        witnesses.push(event);
        full(join, bindings, witnesses, prefix, result);
        witnesses.pop();
        undo(saved, bindings);
    }
}

/// Matches with at least one frontier witness, each produced once at its first
/// frontier position, with the same bindings, witnesses and order as the
/// breadth-first delta join (see `match_delta_antecedents`).
pub(super) fn match_delta<'v>(
    antecedent: &Antecedent,
    parameters: &[Arg],
    known: KnownView<'v>,
    delta: KnownView<'v>,
    initial: &Bindings,
    pivot_matches: &mut usize,
) -> Vec<AntecedentMatch> {
    let join = Join::new(antecedent, parameters, known);
    let mut result = Vec::new();
    let mut fresh_keys: Option<BTreeSet<&Event>> = None;
    let mut bindings = initial.clone();
    for (pivot, &pattern) in join.atoms.iter().enumerate() {
        let fresh = if pivot > 0 {
            Some(&*fresh_keys.get_or_insert_with(|| delta.events.iter().collect()))
        } else {
            None
        };
        for event in delta.candidates(pattern) {
            let Some(saved) = bind(
                pattern,
                event,
                parameters,
                &join.binders[pivot],
                &mut bindings,
            ) else {
                continue;
            };
            *pivot_matches += 1;
            let mut witnesses: Vec<Option<&Event>> = vec![None; join.atoms.len()];
            witnesses[pivot] = Some(event);
            let pivoted = Pivot { pivot, fresh };
            around(
                &join,
                &pivoted,
                0,
                &mut bindings,
                &mut witnesses,
                &mut result,
            );
            undo(saved, &mut bindings);
        }
    }
    result
}

struct Pivot<'f, 'e> {
    pivot: usize,
    /// Frontier membership, excluded at positions before the pivot.
    fresh: Option<&'f BTreeSet<&'e Event>>,
}

fn around<'w>(
    join: &Join<'_, 'w>,
    pivoted: &Pivot<'_, '_>,
    position: usize,
    bindings: &mut Bindings,
    witnesses: &mut Vec<Option<&'w Event>>,
    result: &mut Vec<AntecedentMatch>,
) {
    if position == pivoted.pivot {
        return around(join, pivoted, position + 1, bindings, witnesses, result);
    }
    let Some(&pattern) = join.atoms.get(position) else {
        result.push(AntecedentMatch {
            substitutions: bindings.clone(),
            antecedents: witnesses
                .iter()
                .map(|event| event.expect("complete witness").clone())
                .collect(),
        });
        return;
    };
    for candidate in join
        .known
        .candidates_bound(pattern, join.parameters, bindings)
    {
        if position < pivoted.pivot && pivoted.fresh.is_some_and(|f| f.contains(&candidate)) {
            #[cfg(test)]
            super::profile::fresh_exclusion();
            continue;
        }
        let Some(saved) = bind(
            pattern,
            candidate,
            join.parameters,
            &join.binders[position],
            bindings,
        ) else {
            continue;
        };
        witnesses[position] = Some(candidate);
        around(join, pivoted, position + 1, bindings, witnesses, result);
        witnesses[position] = None;
        undo(saved, bindings);
    }
}
