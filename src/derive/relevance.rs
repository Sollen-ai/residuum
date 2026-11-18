//! Rules a frontier can pivot into (docs/semi-naive-pending-optimizations.md §2).
//!
//! A delta match needs one antecedent atom matched against a frontier event,
//! and `match_event` rejects any pair whose verb, polarity or arity differ. So
//! a rule whose atom headers are all absent from the frontier yields no delta
//! match and can be skipped without changing any result or its order.
use super::{Event, Polarity};
use crate::typed::{Antecedent, Rule, RuleBody};
use std::collections::{BTreeMap, BTreeSet};

type Header = (String, Polarity, usize);

#[derive(Debug, Clone, Default)]
pub(super) struct RuleHeaders {
    /// Antecedent atom header -> indexes of the rules containing it, ascending.
    rules: BTreeMap<Header, Vec<usize>>,
    len: usize,
}

impl RuleHeaders {
    pub fn new<'a>(rules: impl IntoIterator<Item = &'a Rule>) -> Self {
        let mut headers = Self::default();
        for (index, rule) in rules.into_iter().enumerate() {
            headers.len = index + 1;
            let mut atoms = BTreeSet::new();
            match &rule.body {
                RuleBody::HornClause(clause) => collect(&clause.antecedent, &mut atoms),
                RuleBody::ResidualClause(clause) => {
                    collect(&clause.unresiduate().antecedent, &mut atoms)
                }
            }
            for header in atoms {
                headers.rules.entry(header).or_default().push(index);
            }
        }
        headers
    }

    /// One flag per rule, in rule order: whether some atom shares a header with
    /// a frontier event. Rules with only `I` are never relevant to a delta.
    pub fn relevant(&self, frontier: &[Event]) -> Vec<bool> {
        let mut relevant = vec![false; self.len];
        let headers: BTreeSet<Header> = frontier.iter().map(header).collect();
        for header in &headers {
            for &index in self.rules.get(header).into_iter().flatten() {
                relevant[index] = true;
            }
        }
        relevant
    }
}

fn header(event: &Event) -> Header {
    (event.verb.clone(), event.polarity, event.args.len())
}

fn collect(antecedent: &Antecedent, atoms: &mut BTreeSet<Header>) {
    match antecedent {
        Antecedent::Unit => {}
        Antecedent::Event(event) => {
            atoms.insert(header(event));
        }
        Antecedent::And(a, b) => {
            collect(a, atoms);
            collect(b, atoms);
        }
    }
}
