// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

var num: Z = Z.prompt("Enter a number: ")
val numOrig : Z = num


if (num < 0) {
  num = num * -1

  Deduce(
    1 ( numOrig == Old(num) ) by Premise,
    2 ( Old(num) < 0 ) by Premise,
    3 ( num == Old(num) * -1 ) by Premise,
    4 ( num >= 0 ) by Algebra*(2, 3), //for the 1st assert
    5 ( num == numOrig * -1 ) by Algebra*(1, 3)
  )

  //want: num >= 0
  //want: num == numOrig*-1
} else {
  //no code, just for verification

  Deduce(
    1 ( !(num < 0) ) by Premise,
    2 ( numOrig == num ) by Premise,
    3 ( num >= 0 ) by Algebra*(1),
    4 ( num == numOrig ) by Algebra*(2)
  )

  //want: num >= 0
  //want: num == numOrig
}

Deduce(
  1 ( num >= 0 ) by Premise,
  2 ( num == numOrig * -1 | num == numOrig ) by Premise,
)


//How can we assert that num is the absolute value of the input?
//(what was the original input?)

assert(num >= 0)
assert(num == numOrig * -1 | num == numOrig)