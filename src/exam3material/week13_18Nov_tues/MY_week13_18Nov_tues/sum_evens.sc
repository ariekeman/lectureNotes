// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//sum of first n even numbers
def sumEvens(n: Z): Z = {
  //What can we use as the function contract?

  var sum: Z = 0
  var cur: Z = 0

  while (cur != n) {
    //what about our loop invariant?

    cur = cur + 1
    sum = sum + 2*cur
  }

  return sum
}

//////////// test code /////////

val num: Z = 5

var sum5evens: Z = sumEvens(num)

//sum of first 5 evens: ?
