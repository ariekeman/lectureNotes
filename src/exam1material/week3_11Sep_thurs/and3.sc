// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//Prove the sequent:
//p ∧ q ∧ r ⊢ q


@pure def and3(p: B, q: B, r: B): Unit = {
  Deduce(
    (p & q & r) |- (q)
      Proof(
        //PROOF GOES HERE
        1 ( p & q & r ) by Premise,
        and
        
  )
}