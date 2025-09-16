// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._



@pure def orDist2(p: B, q: B, r: B): Unit = {
  Deduce(
    ( (p | q ) & (p | r) ) |- ( p | (q & r) )
      Proof(
        //PROOF GOES HERE
        1 ( (p | q ) & (p | r) ) by Premise,
        2 ( p | q ) by AndE1(1),
        3 ( p | r ) by AndE2(1),
        4 SubProof(
          5 Assume (p),
          6 ( p | (q & r) ) by OrI1(5)
          //goal: p | (q & r)
        ),
        7 SubProof(
          8 Assume(q),

          //try OrE on p | r
          9 SubProof(
            10 Assume (p),
            11 ( p | (q & r) ) by OrI1(10)
            //goal: //p | (q & r)
          ),
          12 SubProof(
            13 Assume (r),
            14 ( q & r ) by AndI(8, 13),
            15 ( p | (q & r) ) by OrI2(14)

            //goal: p | (q & r)
          ),
          16 ( p | (q & r) ) by OrE(3, 9, 12)


          //goal: //p | (q & r)
        ),
        17 ( p | (q & r) ) by OrE(2, 4, 7)
        //another subproof, assume q
          //p | (q & r)
        //OrE refer to p | q
    )
  )
}