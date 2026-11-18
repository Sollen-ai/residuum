//! Minimal proofs over retained justifications
//! (docs/semi-naive-pending-optimizations.md §9).
//!
//! A pass after the closure: events and justifications are not changed. Each
//! event gets the least value over its justifications of a combination of the
//! rule's weight and the values of its witnesses, with seeds at 0:
//!
//! - tropical (min, +): `w(j) + Σ c(a)`, the size of the smallest proof tree
//!   when every rule weighs 1 (a shared subproof counts once per use);
//! - (min, max): `1 + max d(a)`, the Kleene stage, the least round n with the
//!   event in Tⁿ; an axiom `I <= C` has stage 1.
//!
//! Both combinations are at least the largest witness value, so Knuth's (1977)
//! generalization of Dijkstra to hypergraphs fixes each event once, in
//! increasing order, also with cycles. Ties are kept: every justification that
//! attains the minimum is reported, in the order of `closure.derivations`.
use crate::typed::{Closure, DerivedEvent, Event};
use std::cmp::Reverse;
use std::collections::{BTreeMap, BinaryHeap};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofCosts {
    /// Aligned with `closure.known`. `None` when no proof from the seeds exists.
    pub costs: Vec<Option<u64>>,
    /// Aligned with `closure.known`: indexes into `closure.derivations` of the
    /// justifications attaining the cost. Empty for seeds.
    pub optimal: Vec<Vec<usize>>,
}

impl ProofCosts {
    pub fn cost(&self, closure: &Closure, event: &Event) -> Option<u64> {
        let index = closure.known.iter().position(|known| known == event)?;
        self.costs[index]
    }
}

/// Size of the smallest proof tree of each event, with `weight` per
/// justification (for instance 1 for every rule).
pub fn minimum_proof_sizes(
    closure: &Closure,
    seeds: &[Event],
    weight: impl Fn(&DerivedEvent) -> u64,
) -> ProofCosts {
    least(closure, seeds, |derived, witnesses| {
        witnesses
            .iter()
            .fold(weight(derived), |total, cost| total.saturating_add(*cost))
    })
}

/// Kleene stage of each event: seeds 0, otherwise the least `1 + max` over
/// its justifications of the stages of their witnesses.
pub fn kleene_stages(closure: &Closure, seeds: &[Event]) -> ProofCosts {
    least(closure, seeds, |_, witnesses| {
        1 + witnesses.iter().copied().max().unwrap_or(0)
    })
}

type Queue = BinaryHeap<Reverse<(u64, usize)>>;

fn relax(event: usize, cost: u64, best: &mut [Option<u64>], queue: &mut Queue) {
    if best[event].is_none_or(|old| cost < old) {
        best[event] = Some(cost);
        queue.push(Reverse((cost, event)));
    }
}

fn least(
    closure: &Closure,
    seeds: &[Event],
    combine: impl Fn(&DerivedEvent, &[u64]) -> u64,
) -> ProofCosts {
    let index: BTreeMap<&Event, usize> = closure
        .known
        .iter()
        .enumerate()
        .map(|(i, event)| (event, i))
        .collect();
    let events = closure.known.len();
    // Per justification: head, witnesses with multiplicity, distinct witnesses
    // still unfixed. Justifications naming events outside Known are ignored.
    let mut heads = Vec::with_capacity(closure.derivations.len());
    let mut witnesses: Vec<Vec<usize>> = Vec::with_capacity(closure.derivations.len());
    let mut missing = Vec::with_capacity(closure.derivations.len());
    let mut watchers: Vec<Vec<usize>> = vec![Vec::new(); events];
    for (j, derived) in closure.derivations.iter().enumerate() {
        let head = index.get(&derived.event).copied();
        let list: Option<Vec<usize>> = derived
            .record
            .antecedents
            .iter()
            .map(|a| index.get(a).copied())
            .collect();
        let (Some(head), Some(list)) = (head, list) else {
            heads.push(None);
            witnesses.push(Vec::new());
            missing.push(usize::MAX);
            continue;
        };
        let mut distinct = list.clone();
        distinct.sort_unstable();
        distinct.dedup();
        for &a in &distinct {
            watchers[a].push(j);
        }
        heads.push(Some(head));
        missing.push(distinct.len());
        witnesses.push(list);
    }

    let mut best: Vec<Option<u64>> = vec![None; events];
    let mut fixed = vec![false; events];
    let mut seed = vec![false; events];
    let mut queue = Queue::new();
    for event in seeds {
        if let Some(&i) = index.get(event) {
            seed[i] = true;
            relax(i, 0, &mut best, &mut queue);
        }
    }
    let value = |j: usize, best: &[Option<u64>]| {
        let costs: Vec<u64> = witnesses[j]
            .iter()
            .map(|&a| best[a].expect("fixed witness"))
            .collect();
        combine(&closure.derivations[j], &costs)
    };
    for j in 0..closure.derivations.len() {
        if missing[j] == 0 {
            let head = heads[j].expect("valid justification");
            let cost = value(j, &best);
            relax(head, cost, &mut best, &mut queue);
        }
    }
    while let Some(Reverse((cost, event))) = queue.pop() {
        if fixed[event] || best[event] != Some(cost) {
            continue;
        }
        fixed[event] = true;
        for &j in &watchers[event] {
            missing[j] -= 1;
            if missing[j] == 0 {
                let head = heads[j].expect("valid justification");
                if !fixed[head] {
                    let cost = value(j, &best);
                    relax(head, cost, &mut best, &mut queue);
                }
            }
        }
    }

    let mut optimal = vec![Vec::new(); events];
    for j in 0..closure.derivations.len() {
        let Some(head) = heads[j] else { continue };
        if seed[head] || missing[j] != 0 {
            continue;
        }
        if Some(value(j, &best)) == best[head] {
            optimal[head].push(j);
        }
    }
    ProofCosts {
        costs: best,
        optimal,
    }
}
