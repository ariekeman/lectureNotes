// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._

// ∀ x ¬P(x)   equivalent to   ¬(∃ x P(x))

//first direction is very similar to exists2.sc
@pure def demorgan1A[T](P: T=>B @pure): Unit = {
  Deduce(
    (
      ∀((x: T) => !P(x))
    )
    |-
    (
      !(∃((x: T) => P(x)))
    )
    Proof(
      1 ( ∀((x: T) => !P(x)) ) by Premise,
      //similar to exists2
    )
  )
}

@pure def demorgan1B[T](P: T=>B @pure): Unit = {
  Deduce(
    (
      !(∃((x: T) => P(x)))
    )
      |-
    (
      ∀((x: T) => !P(x))
    )
    Proof(
      1 (  !(∃((x: T) => P(x)))   ) by Premise,
      //we have proved this before
    )
  )
}