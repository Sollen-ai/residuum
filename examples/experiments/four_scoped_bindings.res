module FourScopedBindings

entity Person

const alice : Person
const bob : Person
const tau : PropositionTime

derived verb Notified(person : Person)
derived verb Served(person : Person)
derived verb Linked(a : Person, b : Person)

// Being served implies being notified (antecedent <= consequent).
rule service(person, t) =
    Served(person) @ t <= Notified(person) @ t

program Service(person : Person, t : PropositionTime) {
    use service { person = person, t = t }
}

// A link between two people requires the second one to be served.
rule link(a, b, t) =
    Linked(a, b) @ t <= Served(b) @ t

// One rule, two instances: each use of a Program compiles to its own rule,
// so its shared parameters can bind the same rule at different arguments.
program Both(a : Person, b : Person, t : PropositionTime) {
    use service { person = a, t = t }
    use service { person = b, t = t }
    use link { a = a, b = b, t = t }
}

// FOUR contraposition through a rule with parameters: Horn closure cannot
// derive ~Served(alice), every FOUR model of the bound instance satisfies it.
experiment contraposition {
    premises {
        ~Notified(alice) @ tau,
    }
    query fourFusion ~Served(alice) @ tau
    using rules { service }
    with {
        rule service.person = alice,
        rule service.t = tau
    }
}

// The same theory with the instance for bob: the answer is false within this
// scope, which says nothing about instances the scope leaves out.
experiment otherInstance {
    premises {
        ~Notified(alice) @ tau,
    }
    query fourFusion ~Served(alice) @ tau
    using rules { service }
    with {
        rule service.person = bob,
        rule service.t = tau
    }
}

// The shared parameters of a Program bind every use at once.
experiment program {
    premises {
        ~Notified(alice) @ tau,
    }
    query fourFusion ~Served(alice) @ tau
    using program Service
    with {
        program Service.person = alice,
        program Service.t = tau
    }
}

// Contraposition through bob's instance of service, then link: five atoms,
// so only the least model answers.
experiment twoInstances {
    premises {
        ~Notified(bob) @ tau,
    }
    query fourFusion ~Linked(alice, bob) @ tau
    using program Both
    with {
        program Both.a = alice,
        program Both.b = bob,
        program Both.t = tau
    }
}
