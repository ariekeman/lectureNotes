// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

def absVal(numOrig: Z) : Z = {
  //what do we need here?
  Contract(
    //no requires needed
    Ensures(
      Res[Z] >= 0,
      Res[Z] == numOrig * -1 | Res[Z] == numOrig
    )
  )

  var num: Z = numOrig

  if (num < 0) {
    num = num * -1

    Deduce(
      1 ( Old(num) == numOrig ) by Premise,
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
      3 ( num >= 0 ) by Algebra*(1),
      4 ( num == numOrig ) by Premise
    )

    //want: num >= 0
    //want: num == numOrig
  }

  //this proves my postconditions
  Deduce(
    1 ( num >= 0 ) by Premise,
    2 ( num == numOrig * -1 | num == numOrig ) by Premise,
  )

  //what can we say here?
  //what do we need to prove by the end of the function?

  return num

}

////////////////// Test code //////////////

val x: Z = -4

//use function to get absolute value of x
//what *should* the absolute value be?

//no preconditions, nothing needed here

var answer: Z = absVal(x)

Deduce(
  1 (  answer >= 0 ) by Premise, //from 1st postcondition
  2 ( answer == x * -1 | answer == x ) by Premise, //2nd post
  3 ( x == -4 ) by Premise,

  //OrE
  4 SubProof(
    5 Assume (answer == x * -1),
    6 ( answer == 4 ) by Algebra*(3, 5)
    //goal: answer == 4
  ),
  7 SubProof(
    8 Assume (answer == x),
    9 ( answer == -4 ) by Algebra*(3,8),
    10 ( F ) by Algebra*(1,9),
    11 ( answer == 4 ) by BottomE(10)
    //goal: answer == 4
  ),
  12 ( answer == 4 ) by OrE(2,4,7)
)

//what should we be able to assert?
assert(answer == 4)