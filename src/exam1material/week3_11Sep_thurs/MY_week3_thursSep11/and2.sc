// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//Prove the sequent:
//p, q, r ⊢ r ∧ (q ∧ p)


@pure def and2(p: B, q: B, r: B): Unit = {
  Deduce(
    (p, q, r) |- (r & (q & p))
      Proof(
        //PROOF GOES HERE
        
      )
  )
}