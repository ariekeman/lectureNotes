// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//just the code for finding the biggest of 3 numbers

val a: Z = Z.read()    //suppose a is 3
val b: Z = Z.read()    //suppose b is 5
val c: Z = Z.read()    //suppose c is 10
var max: Z = 0

/*
    mark where logic blocks would go
    finish the verification in the next file
*/

if (a >= b) {
  if (a >= c) {
    max = a

    //what do we need to show here?
  } else {
    max = c

    //what do we need to show here?
  }
  //what do we put here?
} else {
  if (b >= c) {
    max = b

    //what do we need to show here?
  } else {
    max = c

    //what do we need to show here?
  }

  //what goes here?
}

//what goes here?

println("Max between ", a, ", ", b, " and ", c, " is ", max)

//How do we know we have the max?
//what assert(s) do we want?

//where do we need to prove the asserts?