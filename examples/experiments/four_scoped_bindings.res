module FourScopedBindings

entity Person

const alice : Person
const bob : Person
const tau : PropositionTime

derived verb Notified(person : Person)
derived verb Served(person : Person)

// Being served implies being notified (antecedent <= consequent).
rule service(person, t) =
    Served(person) @ t <= Notified(person) @ t

program Service(person : Person, t : PropositionTime) {
    use service { person = person, t = t }
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
