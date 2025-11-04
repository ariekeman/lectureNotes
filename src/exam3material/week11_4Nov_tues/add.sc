// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

val x: Z = 2

//What can we put in a proof block here?
//Do we need this step? 

Deduce(
  1 ( x == 2 ) by Premise
)


val y: Z = x + 2

Deduce(
  1 ( y == x + 2 ) by Premise,
  2 ( x == 2 ) by Premise,
  3 ( y == 4 ) by Algebra*(1,2),
  4 ( y > 0 ) by Algebra*(3),
  5 ( y == 4 & y > 0 ) by AndI(3,4)
)



//what can we put in a proof block here?

assert(y == 4 & y > 0)



