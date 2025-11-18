// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//want to return x * y, through repeated addition
//recursively compute x + x + ... + x (y times)
def mult(x: Z, y: Z): Z = {
  //what goes here?
  //what should we require?
  //what should we ensure?

  var answer: Z = 0

  if (y == 0) {
    answer = 0

    //what do we need to do here?
  } else {

    var temp: Z = mult(x, y-1)
    answer = x + temp

    //what do we need to show here?
  }

  //what do we need to do here?

  return answer
}

////////////// Test code //////////////

val a: Z = 5
val b: Z = 4

var ans: Z = mult(a, b)

//what do we want to assert that ans is?