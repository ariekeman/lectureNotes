// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def not2(p: B, q: B, r: B): Unit = {
  Deduce(
    ( !p & !q ) |- ( !(p | q)  )
      Proof(
        1 (  !p & !q ) by Premise,

        2 ( !p ) by AndE1(1),
        3 ( !q ) by AndE2(1),

        //use NegI to get conclusion
        4 SubProof(
          5 Assume ( p | q ),

          //use OrE on p | q to get F in both cases
          6 SubProof(
            7 Assume ( p ),
            8 ( F ) by NegE(7, 2)

            //goal: F
          ),
          9 SubProof(
            10 Assume ( q ),
            11 ( F ) by NegE(10, 3)
          ),
          12 ( F ) by OrE(5, 6, 9)
          //same thing with q

          //goal: F
        ),
        13 ( !(p | q) ) by NegI(4)
    )
  )
}