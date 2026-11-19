module FourGroundValues

entity Thing
entity TimeBox { first : PropositionTime second : PropositionTime }

const x : Thing
const tau : PropositionTime

derived verb held(box : TimeBox, maybe : Thing?)
derived verb shown(box : TimeBox, maybe : Thing?)

// Ground records, none and times other than the goal's are ordinary atoms.
rule r(box, maybe, t) =
    held(box, maybe) @ t <= shown(box, maybe) @ after t

experiment e {
    premises {
        ~shown(TimeBox { second = after(tau), first = tau }, none) @ after tau,
    }
    query fourFusion ~held(TimeBox { first = tau, second = after(tau) }, none) @ tau
    using rules { r }
    with {
        rule r.box = TimeBox { second = after(tau), first = tau },
        rule r.maybe = none,
        rule r.t = tau
    }
}
