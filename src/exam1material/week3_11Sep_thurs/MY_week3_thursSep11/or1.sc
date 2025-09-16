// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//Prove OR is commutative


@pure def or1(p: B, q: B): Unit = {
  Deduce(
    (p | q) |- (q | p)
      Proof(
        //PROOF GOES HERE
        1 ( p | q ) by Premise,

        
    )
  )
}