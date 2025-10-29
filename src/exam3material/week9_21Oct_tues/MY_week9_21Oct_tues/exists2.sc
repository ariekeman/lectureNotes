// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._

// ∀ x (P(x) __>: ¬Q(x)) ⊢ !(∃ x (P(x) & Q(x)))

@pure def exists2[T](P: T=>B @pure, Q: T=>B @pure): Unit = {
  Deduce(
    (
      ∀((x: T) => (P(x)) __>: !Q(x))
    )
    |-
    (
      !(∃((x: T) => (P(x) & Q(x))))
    )
      Proof(
      1 ( ∀((x: T) => (P(x)) __>: !Q(x)) ) by Premise,

    )
  )
}