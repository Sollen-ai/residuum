//! Finite reference evaluator: FOUR fusion and the unit filter {T,B}.
//! This is a query layer; it never augments the Horn closure.

use super::{Error, FourEntailment, horn};
use crate::typed::{Antecedent, Event, Experiment, HornClause, Polarity, Rule, Term};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy)]
struct Value {
    p: bool,
    n: bool,
}
impl Value {
    fn tensor(self, other: Self) -> Self {
        Self {
            p: self.p && other.p,
            n: (!other.p || self.n) && (!self.p || other.n),
        }
    }
    fn le(self, other: Self) -> bool {
        (!self.p || other.p) && (!other.n || self.n)
    }
}

fn key(event: &Event) -> Event {
    let mut key = event.clone();
    key.polarity = Polarity::Positive;
    key
}
fn collect(antecedent: &Antecedent, atoms: &mut BTreeSet<Event>) {
    match antecedent {
        Antecedent::Unit => {}
        Antecedent::Event(event) => {
            atoms.insert(key(event));
        }
        Antecedent::And(a, b) => {
            collect(a, atoms);
            collect(b, atoms);
        }
    }
}
fn value(event: &Event, world: &BTreeMap<Event, Value>) -> Value {
    let value = world[&key(event)];
    if event.polarity == Polarity::Positive {
        value
    } else {
        Value {
            p: value.n,
            n: value.p,
        }
    }
}
fn evaluate(antecedent: &Antecedent, world: &BTreeMap<Event, Value>) -> Value {
    match antecedent {
        Antecedent::Unit => Value { p: true, n: true },
        Antecedent::Event(event) => value(event, world),
        Antecedent::And(a, b) => evaluate(a, world).tensor(evaluate(b, world)),
    }
}
/// A ground FOUR problem: premises, ground Horn clauses labelled by the rule
/// each came from, the goal, and the sorted atoms they mention.
///
/// Only the constructors build it, and they check that every argument is a
/// constant and every atom shares the goal's time, so the evaluators below
/// never see a parameter. Bindings and scopes are resolved before this point.
#[derive(Debug, Clone)]
pub struct GroundProgram {
    facts: Vec<Event>,
    clauses: Vec<(String, HornClause)>,
    goal: Event,
    atoms: Vec<Event>,
}
impl GroundProgram {
    /// The premises and goal of `experiment` with rules that have no parameters.
    pub fn from_ground_rules(experiment: &Experiment, rules: &[Rule]) -> Result<Self, Error> {
        if rules.iter().any(|rule| !rule.parameters.is_empty()) {
            return Err(Error::new(
                "fourFusion fixture comparison requires ground rules",
            ));
        }
        Self::new(
            &experiment.input,
            &experiment.goal,
            rules
                .iter()
                .map(|rule| (rule.name.clone(), horn(rule)))
                .collect(),
        )
    }

    fn new(
        facts: &[Event],
        goal: &Event,
        clauses: Vec<(String, HornClause)>,
    ) -> Result<Self, Error> {
        let mut atoms: BTreeSet<Event> = facts.iter().chain([goal]).map(key).collect();
        for (_, clause) in &clauses {
            collect(&clause.antecedent, &mut atoms);
            atoms.insert(key(&clause.consequent));
        }
        // This finite comparison retains its single-index experimental domain.
        // The scoped forward matcher itself also supports other literal indices.
        if atoms.iter().any(|atom| {
            atom.proposition.time != goal.proposition.time
                || atom.args.iter().any(|arg| !matches!(arg, Term::Const(_)))
        }) {
            return Err(Error::new(
                "fourFusion comparison requires constant arguments and one shared proposition time",
            ));
        }
        Ok(Self {
            facts: facts.to_vec(),
            clauses,
            goal: goal.clone(),
            atoms: atoms.into_iter().collect(),
        })
    }

    /// Positive-polarity keys of the ground atoms, in sorted order.
    pub fn atoms(&self) -> &[Event] {
        &self.atoms
    }

    fn is_model(&self, world: &BTreeMap<Event, Value>) -> bool {
        self.facts.iter().all(|fact| value(fact, world).p)
            && self.clauses.iter().all(|(_, clause)| {
                evaluate(&clause.antecedent, world).le(value(&clause.consequent, world))
            })
    }
}

/// The largest program the enumeration accepts: 4^4 = 256 interpretations.
pub(super) const ENUMERATION_ATOMS: usize = 4;

/// Counts the models among all `4^n` interpretations. The reference oracle,
/// bounded to [`ENUMERATION_ATOMS`].
pub(super) fn entailment(program: &GroundProgram) -> Result<FourEntailment, Error> {
    check_enumerable(program)?;
    let interpretations = 1 << (2 * program.atoms.len());
    let mut models = 0;
    let mut entailed = true;
    for mask in 0..interpretations {
        let world = world(&program.atoms, mask);
        if program.is_model(&world) {
            models += 1;
            entailed &= value(&program.goal, &world).p;
        }
    }
    Ok(FourEntailment {
        interpretations,
        models,
        entailed,
    })
}

fn check_enumerable(program: &GroundProgram) -> Result<(), Error> {
    if program.atoms.len() > ENUMERATION_ATOMS {
        return Err(Error::new(
            "fourFusion fixture comparison supports at most four ground atoms",
        ));
    }
    Ok(())
}

fn world(atoms: &[Event], mask: usize) -> BTreeMap<Event, Value> {
    atoms
        .iter()
        .enumerate()
        .map(|(i, atom)| {
            (
                atom.clone(),
                Value {
                    p: mask & (1 << (2 * i)) != 0,
                    n: mask & (1 << (2 * i + 1)) != 0,
                },
            )
        })
        .collect()
}

/// Test oracle without the four-atom bound: the knowledge meet of every model
/// found by enumeration, and whether the goal holds in all of them. Atoms in
/// the order of [`GroundProgram::atoms`]. Exponential; for small tests only.
#[cfg(all(test, family_experiments))]
pub(super) fn meet_of_models(program: &GroundProgram) -> (Vec<(bool, bool)>, bool) {
    let mut meet = vec![(true, true); program.atoms.len()];
    let mut entailed = true;
    for mask in 0..1usize << (2 * program.atoms.len()) {
        let world = world(&program.atoms, mask);
        if program.is_model(&world) {
            for (slot, atom) in meet.iter_mut().zip(&program.atoms) {
                let value = world[atom];
                *slot = (slot.0 && value.p, slot.1 && value.n);
            }
            entailed &= value(&program.goal, &world).p;
        }
    }
    (meet, entailed)
}

/// The knowledge-least model of the premises and rules
/// (docs/semi-naive-pending-optimizations.md §12).
///
/// Every model condition is a Horn clause over the 2n bits `p(a)`, `n(a)`, so
/// the models are closed under the componentwise conjunction, which is the
/// knowledge meet, and B is always a model. `p` is knowledge-monotone, so the
/// goal holds in every model exactly when it holds in this one. Unlike
/// [`entailment`], this does not count models and has no bound on the atoms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FourLeastModel {
    /// Positive-polarity keys of the ground atoms, in sorted order.
    pub atoms: Vec<Event>,
    /// `(p, n)` of each atom in the least model, aligned with `atoms`.
    pub values: Vec<(bool, bool)>,
    /// Compiled Horn clauses over the bits, including premises.
    pub clauses: usize,
    pub entailed: bool,
}

/// A bit of the compiled problem: `2 * atom` is p, `2 * atom + 1` is n.
type Bit = usize;

struct Compiler<'a> {
    atoms: &'a [Event],
    clauses: Vec<(Vec<Bit>, Bit)>,
}
impl Compiler<'_> {
    /// Bit of component p (or n) of a literal; a negative literal swaps them.
    fn bit(&self, event: &Event, positive_component: bool) -> Bit {
        let index = self
            .atoms
            .binary_search(&key(event))
            .expect("prepared atom");
        let p = positive_component == (event.polarity == Polarity::Positive);
        2 * index + usize::from(!p)
    }
    fn p_bits(&self, antecedent: &Antecedent, output: &mut Vec<Bit>) {
        match antecedent {
            Antecedent::Unit => {}
            Antecedent::Event(event) => output.push(self.bit(event, true)),
            Antecedent::And(a, b) => {
                self.p_bits(a, output);
                self.p_bits(b, output);
            }
        }
    }
    /// Backward half of `le`: `guard => n(antecedent)`, where
    /// `n(x * y) = (p(y) => n(x)) and (p(x) => n(y))`.
    fn n_clauses(&mut self, antecedent: &Antecedent, guard: Vec<Bit>) {
        match antecedent {
            Antecedent::Unit => {}
            Antecedent::Event(event) => {
                let head = self.bit(event, false);
                self.clauses.push((guard, head));
            }
            Antecedent::And(a, b) => {
                let mut left = guard.clone();
                self.p_bits(b, &mut left);
                let mut right = guard;
                self.p_bits(a, &mut right);
                self.n_clauses(a, left);
                self.n_clauses(b, right);
            }
        }
    }
}

pub fn four_least_model(program: &GroundProgram) -> FourLeastModel {
    let atoms = &program.atoms;
    let mut compiler = Compiler {
        atoms,
        clauses: Vec::new(),
    };
    for fact in &program.facts {
        let head = compiler.bit(fact, true);
        compiler.clauses.push((Vec::new(), head));
    }
    for (_, clause) in &program.clauses {
        // Forward half of `le`: p(antecedent) => p(consequent); I has p = 1.
        let mut body = Vec::new();
        compiler.p_bits(&clause.antecedent, &mut body);
        let head = compiler.bit(&clause.consequent, true);
        compiler.clauses.push((body, head));
        let guard = vec![compiler.bit(&clause.consequent, false)];
        compiler.n_clauses(&clause.antecedent, guard);
    }
    let bits = propagate(2 * atoms.len(), &mut compiler.clauses);
    let goal = compiler.bit(&program.goal, true);
    FourLeastModel {
        values: (0..atoms.len())
            .map(|i| (bits[2 * i], bits[2 * i + 1]))
            .collect(),
        clauses: compiler.clauses.len(),
        entailed: bits[goal],
        atoms: atoms.clone(),
    }
}

/// Least model of definite Horn clauses by counter-based unit propagation,
/// linear in the total size of the (deduplicated) bodies.
fn propagate(bits: usize, clauses: &mut [(Vec<Bit>, Bit)]) -> Vec<bool> {
    let mut watchers: Vec<Vec<usize>> = vec![Vec::new(); bits];
    let mut missing = Vec::with_capacity(clauses.len());
    let mut queue = Vec::new();
    let mut on = vec![false; bits];
    for (index, (body, head)) in clauses.iter_mut().enumerate() {
        body.sort_unstable();
        body.dedup();
        for bit in body.iter() {
            watchers[*bit].push(index);
        }
        missing.push(body.len());
        if body.is_empty() && !on[*head] {
            on[*head] = true;
            queue.push(*head);
        }
    }
    while let Some(bit) = queue.pop() {
        for &index in &watchers[bit] {
            missing[index] -= 1;
            let head = clauses[index].1;
            if missing[index] == 0 && !on[head] {
                on[head] = true;
                queue.push(head);
            }
        }
    }
    on
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FourStep {
    pub round: usize,
    pub constraint: Option<String>,
    /// Interpretation IDs use two bits per atom in atoms(), in sorted order.
    pub eliminated: Vec<usize>,
    pub surviving: Vec<usize>,
    pub interpretations: usize,
    /// None while any theory constraint is still pending.
    pub entailed: Option<bool>,
    pub complete: bool,
}

#[derive(Debug, Clone)]
pub struct FourSession {
    program: GroundProgram,
    remaining: Vec<usize>,
    cursor: usize,
    round: usize,
    result: Option<FourEntailment>,
}
impl FourSession {
    pub fn new(experiment: &Experiment, rules: &[Rule]) -> Result<Self, Error> {
        Self::from_program(GroundProgram::from_ground_rules(experiment, rules)?)
    }
    pub fn from_program(program: GroundProgram) -> Result<Self, Error> {
        check_enumerable(&program)?;
        let remaining = (0..1 << (2 * program.atoms.len())).collect();
        Ok(Self {
            program,
            remaining,
            cursor: 0,
            round: 0,
            result: None,
        })
    }
    pub fn atoms(&self) -> &[Event] {
        &self.program.atoms
    }
    pub fn result(&self) -> Option<&FourEntailment> {
        self.result.as_ref()
    }
    pub fn step(&mut self) -> FourStep {
        let program = &self.program;
        let mut eliminated = Vec::new();
        let mut constraint = None;
        let facts = program.facts.len();
        let constraints = facts + program.clauses.len();
        if self.cursor < constraints {
            constraint = Some(if self.cursor < facts {
                format!(
                    "premise {}",
                    super::render_event(&program.facts[self.cursor])
                )
            } else {
                format!("rule {}", program.clauses[self.cursor - facts].0)
            });
            let mut next = Vec::new();
            for mask in &self.remaining {
                let world = world(&program.atoms, *mask);
                let satisfies = if self.cursor < facts {
                    value(&program.facts[self.cursor], &world).p
                } else {
                    let clause = &program.clauses[self.cursor - facts].1;
                    evaluate(&clause.antecedent, &world).le(value(&clause.consequent, &world))
                };
                if satisfies {
                    next.push(*mask);
                } else {
                    eliminated.push(*mask);
                }
            }
            self.remaining = next;
            self.cursor += 1;
        }
        let complete = self.cursor == constraints;
        let interpretations = 1 << (2 * program.atoms.len());
        if complete {
            let entailed = self
                .remaining
                .iter()
                .all(|mask| value(&program.goal, &world(&program.atoms, *mask)).p);
            self.result = Some(FourEntailment {
                interpretations,
                models: self.remaining.len(),
                entailed,
            });
        }
        self.round += 1;
        FourStep {
            round: self.round,
            constraint,
            eliminated,
            surviving: self.remaining.clone(),
            interpretations,
            entailed: self.result.as_ref().map(|r| r.entailed),
            complete,
        }
    }
    pub fn trace(&mut self, max_steps: usize) -> Vec<FourStep> {
        let mut steps = Vec::new();
        for _ in 0..max_steps {
            let step = self.step();
            let done = step.complete;
            steps.push(step);
            if done {
                break;
            }
        }
        steps
    }
}
