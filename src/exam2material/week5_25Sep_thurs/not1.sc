// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

@pure def not1(p: B, q: B, r: B): Unit = {
  Deduce(
    ( p __>: !q ) |- ( !(p & q)  )
      Proof(
      1 (  p __>: !q ) by Premise,

      //want to prove a NOT statement
      //assume the thing IS true, get a contradiction,
      //use NegI to conclude it is NOT true

      2 SubProof(
        3 Assume( p & q ),
        4 ( p ) by AndE1(3),
        5 ( q ) by AndE2(3),
        6 ( !q ) by ImplyE(1, 4),
        7 ( F ) by NegE(5, 6)

        //goal: F (contradiction)
      ),
      8 ( !(p & q) ) by NegI(2)
    )
  )
}