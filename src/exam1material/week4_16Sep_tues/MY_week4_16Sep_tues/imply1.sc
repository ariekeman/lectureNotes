// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._



@pure def imply1(p: B, q: B, r: B): Unit = {
  Deduce(
    ( p & q __>: r, p __>: q, p ) |- ( r )
      Proof(
        //PROOF GOES HERE
        
    )
  )
}