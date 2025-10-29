// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._

// ∀ x (Human(x) → Mortal(x)), ∃ x (Human(x)) ⊢ ∃ x (Mortal(x))

@pure def exists1[T](Human: T=>B @pure, Mortal: T=>B @pure): Unit = {
  Deduce(
    (
      ∀((x: T) => (Human(x) __>: Mortal(x))),
      ∃((x: T) => Human(x))
    )
    |-
    (
      ∃((x: T) => Mortal(x))
    )
    Proof(
      1 ( ∀((x: T) => (Human(x) __>: Mortal(x))) ) by Premise,
      2 ( ∃((x: T) => Human(x)) ) by Premise,
      
      //no pattern, use ExistsE
      3 Let ((alias: T) => SubProof(
        4 Assume ( Human(alias) ),
        5 ( Human(alias) __>: Mortal(alias) ) by AllE[T](1),
        6 ( Mortal(alias) ) by ImplyE(5, 4),
        7 ( ∃((x: T) => Mortal(x)) ) by ExistsI[T](6)

        //goal: ∃((x: T) => Mortal(x))
      )),
      8 ( ∃((x: T) => Mortal(x)) ) by ExistsE[T](2, 3)

      //∃((x: T) => Mortal(x))
    )
  )
}