//! Header index over Known, optionally refined by ground argument values.
//! Positions preserve the order and representation of Known.
use super::{Event, Polarity};
use crate::typed::{Arg, SubstitutionValue, Term, Type};
use std::collections::BTreeMap;

#[derive(Debug, Clone, Default)]
struct Bucket {
    positions: Vec<usize>,
    /// Per argument position: exact ground term -> ascending positions.
    /// Only built for indexes created with `with_arguments`.
    arguments: Vec<BTreeMap<Term, Vec<usize>>>,
}

#[derive(Debug, Clone, Default)]
pub(super) struct KnownIndex {
    buckets: BTreeMap<String, BTreeMap<(Polarity, usize), Bucket>>,
    arguments: bool,
}
impl KnownIndex {
    /// Header-only index, for short-lived frontiers.
    pub fn new(known: &[Event]) -> Self {
        Self::build(known, false)
    }
    /// Header index plus one map per argument position, for the closure-level
    /// Known that joins probe with bindings already fixed by earlier atoms.
    pub fn with_arguments(known: &[Event]) -> Self {
        Self::build(known, true)
    }
    fn build(known: &[Event], arguments: bool) -> Self {
        let mut index = Self {
            buckets: BTreeMap::new(),
            arguments,
        };
        for (position, event) in known.iter().enumerate() {
            index.insert(position, event);
        }
        index
    }
    pub fn insert(&mut self, position: usize, event: &Event) {
        let bucket = self
            .buckets
            .entry(event.verb.clone())
            .or_default()
            .entry((event.polarity, event.args.len()))
            .or_default();
        bucket.positions.push(position);
        if self.arguments {
            bucket
                .arguments
                .resize_with(event.args.len(), BTreeMap::new);
            for (slot, arg) in bucket.arguments.iter_mut().zip(&event.args) {
                if arg.is_ground() {
                    slot.entry(arg.clone()).or_default().push(position);
                }
            }
        }
    }
    fn bucket(&self, pattern: &Event) -> Option<&Bucket> {
        self.buckets
            .get(&pattern.verb)
            .and_then(|bucket| bucket.get(&(pattern.polarity, pattern.args.len())))
    }
    fn positions(&self, pattern: &Event) -> &[usize] {
        self.bucket(pattern)
            .map(|bucket| bucket.positions.as_slice())
            .unwrap_or(&[])
    }
    /// The smallest position list among the argument positions whose value
    /// is already fixed. Every event `match_event` can accept is in it: a
    /// fixed value only matches an exactly equal ground term (see `bound`).
    fn bound_positions(
        &self,
        pattern: &Event,
        parameters: &[Arg],
        bindings: &BTreeMap<String, SubstitutionValue>,
    ) -> &[usize] {
        let Some(bucket) = self.bucket(pattern) else {
            return &[];
        };
        if !self.arguments || bucket.arguments.is_empty() {
            return &bucket.positions;
        }
        let mut best: &[usize] = &bucket.positions;
        for (slot, arg) in bucket.arguments.iter().zip(&pattern.args) {
            let Some(value) = bound(arg, parameters, bindings) else {
                continue;
            };
            let positions = slot.get(value).map(Vec::as_slice).unwrap_or(&[]);
            if positions.len() < best.len() {
                best = positions;
                if best.is_empty() {
                    break;
                }
            }
        }
        best
    }
}

/// The exact term an event argument must equal for `bind_term` to accept it,
/// when that is known before matching: a constant or `None` (compared by
/// equality), or a parameter of a non-time type already bound to a term
/// (`bind_typed` compares the canonical values, which for those types are the
/// terms themselves). Time parameters, constructors and records keep the
/// header path, because their canonical comparison is not plain equality.
fn bound<'a>(
    arg: &'a Term,
    parameters: &[Arg],
    bindings: &'a BTreeMap<String, SubstitutionValue>,
) -> Option<&'a Term> {
    match arg {
        Term::Const(_) | Term::None => Some(arg),
        Term::Var(name) => {
            let parameter = parameters.iter().find(|p| p.name == *name)?;
            if parameter.ty == Type::PropositionTime {
                return None;
            }
            match bindings.get(name)? {
                SubstitutionValue::Term(term) if term.is_ground() => Some(term),
                _ => None,
            }
        }
        Term::Constructor { .. } | Term::RecordLiteral { .. } => None,
    }
}

#[derive(Clone, Copy)]
pub(super) struct KnownView<'a> {
    pub events: &'a [Event],
    pub index: Option<&'a KnownIndex>,
}
impl<'a> KnownView<'a> {
    pub fn linear(events: &'a [Event]) -> Self {
        Self {
            events,
            index: None,
        }
    }
    pub fn candidates(self, pattern: &Event) -> Candidates<'a> {
        match self.index {
            Some(index) => Candidates::Indexed {
                events: self.events,
                positions: index.positions(pattern).iter(),
            },
            None => Candidates::Linear(self.events.iter()),
        }
    }
    /// Like `candidates`, narrowed by the argument values `bindings` fixes.
    /// Same events `match_event` accepts, in Known order.
    pub fn candidates_bound(
        self,
        pattern: &Event,
        parameters: &[Arg],
        bindings: &BTreeMap<String, SubstitutionValue>,
    ) -> Candidates<'a> {
        #[cfg(test)]
        if super::profile::header_only() {
            return self.candidates(pattern);
        }
        match self.index {
            Some(index) => Candidates::Indexed {
                events: self.events,
                positions: index.bound_positions(pattern, parameters, bindings).iter(),
            },
            None => Candidates::Linear(self.events.iter()),
        }
    }
}
pub(super) enum Candidates<'a> {
    Linear(std::slice::Iter<'a, Event>),
    Indexed {
        events: &'a [Event],
        positions: std::slice::Iter<'a, usize>,
    },
}
impl<'a> Iterator for Candidates<'a> {
    type Item = &'a Event;
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Linear(events) => events.next(),
            Self::Indexed { events, positions } => positions.next().map(|p| &events[*p]),
        }
    }
}
