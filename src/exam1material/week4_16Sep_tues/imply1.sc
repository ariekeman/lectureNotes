// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._



@pure def imply1(p: B, q: B, r: B): Unit = {
  Deduce(
    ( p & q __>: r, p __>: q, p ) |- ( r )
      Proof(
        //PROOF GOES HERE
        1 ( p & q __>: r ) by Premise,
        2 ( p __>: q ) by Premise,
        3 ( p ) by Premise,
        4 ( q ) by ImplyE(2, 3),
        5 ( p & q ) by AndI(3, 4),
        6 ( r ) by ImplyE(1, 5)
    )
  )
}