// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//finding x*y by doing x + x + x + ... + x (y times)
def mult(x: Z, y: Z): Z = {
  //What can we use as the function contract? same as recursive
  Contract(
    Requires(y >= 0),
    Ensures(Res[Z] == x*y)
  )

  var total: Z = 0
  var i: Z = 0

  //what goes here?

  //prove the invariant(s) is true before the loop begins
  Deduce(
    1 ( total == 0 ) by Premise, //from assignment
    2 ( i == 0 ) by Premise, //from assignment
    3 ( total == x*i ) by Algebra*(1,2), //proves invariant before loop

    4 ( y >= 0 ) by Premise, //from precondition
    5 ( i <= y ) by Algebra*(2, 4) //proves 2nd invariant

    //want: total == x*i
    //want: i <= y
  )

  while (i < y) {
    //what goes here?
    Invariant(
      Modifies(i, total),
      total == x*i,
      i <= y
    )

    //don't need this block (won't lose information)
    Deduce(
      1 ( total == x*i ) by Premise, //from invariant
    )

    //assume the invariant(s) are true here

    total = total + x

    Deduce(
      1 ( Old(total) == x*i ) by Premise, //from invariant, total has changed
      2 ( total == Old(total) + x ) by Premise, //from assignment
      3 ( total == x*i + x ) by Algebra*(1,2) //get rid of Old to summarize
    )

    i = i + 1

    Deduce(
      1 ( i == Old(i) + 1 ) by Premise, //from previous assignment
      2 ( total == x*Old(i) + x ) by Premise, //from previous blok, i has changed
      3 ( total == x*(i-1) + x ) by Algebra*(1,2),
      4 ( total == x*i - x + x ) by Algebra*(3),
      5 ( total == x*i ) by Algebra*(4), //proves invariant at end of iteration
    
      6 ( Old(i) < y ) by Premise, //from loop condition
      7 ( i <= y ) by Algebra*(1, 6) //proves 2nd invariant
    )

    //prove invariant(s) still true at the end of an iteration
    //want: total == x*i
    //want: i <= y

    //what should we be able to assert here?
  }

  //what do we need here?
  Deduce(
    1 ( !(i < y) ) by Premise, //condition is false
    2 ( i >= y ) by Algebra*(1),
    3 ( i <= y ) by Premise, //from 2nd invariant
    4 ( i == y ) by Algebra*(2,3),
    5 ( total == x*i ) by Premise, //invariants are true, we are at the end of an iteration
    6 ( total == x*y ) by Algebra*(4,5)
  )

  //need: total == x*y to prove the postcondition

  return total
}

//////////// test code /////////

val a: Z = 5
val b: Z = 4

//prove precondition
//b >= 0

Deduce(
  1 ( b == 4 ) by Premise,
  2 ( b >= 0 ) by Algebra*(1) //proves precondition
)

var ans: Z = mult(a, b)

Deduce(
  1 ( a == 5 ) by Premise, //from previous assignment
  2 ( b == 4 ) by Premise, //from previous assignment
  3 ( ans == a*b ) by Premise, //from postcondition
  4 ( ans == 20 ) by Algebra*(1,2,3)
)

//what do we want to assert that ans is?
//need: ans == 20

assert(ans == 20)