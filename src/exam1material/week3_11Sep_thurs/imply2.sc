// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//p → r,  q → r,  p ∨ q  ⊢ r


@pure def imply2(p: B, q: B, r: B): Unit = {
  Deduce(
    ( p __>: r, q __>: r, p | q ) |- ( r )
      Proof(
        //PROOF GOES HERE
        
    )
  )
}