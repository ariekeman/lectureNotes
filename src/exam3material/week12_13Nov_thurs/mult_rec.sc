// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//want to return x * y, through repeated addition
//recursively compute x + x + ... + x (y times)
def mult(x: Z, y: Z): Z = {
  Contract(
    Requires(y >= 0),
    Ensures(Res[Z] == x*y)
  )

  //what goes here?
  //what should we require?
  //what should we ensure?

  var answer: Z = 0

  if (y == 0) {
    answer = 0

    Deduce(
      1 ( answer == 0 ) by Premise, //from previous assignment
      2 ( y == 0 ) by Premise, //from if condition
      3 ( answer == x*y ) by Algebra*(1,2)
    )

    //what do we need to do here?
    //need: answer == x*y
  } else {
    //must prove preconditions for mult recursive call

    //need: second parameter >= 0
    

    Deduce(
      1 ( !(y == 0) ) by Premise, //if condition is fales
      2 ( y != 0 ) by Algebra*(1),
      3 ( answer == 0 ) by Premise, //from assignment before if/else
      4 ( y >= 0 ) by Premise, //from precondition
      5 ( y-1 >= 0 ) by Algebra*(2,4) //proves precondition of recursive call
    )

    //specifically, need: y-1 >= 0

    //return x*(y-1)
    var temp: Z = mult(x, y-1)

    answer = x + temp

    Deduce(
      1 ( answer == x + temp ) by Premise, //from previous assignment
      2 ( temp == x*(y-1) ) by Premise, //from postcondition of recursive call
      3 ( temp == x*y - x ) by Algebra*(2),
      4 ( answer == x + x*y - x ) by Algebra*(1,3),
      5 ( answer == x*y ) by Algebra*(4) //establishes post condition
    )

    //what do we need to show here?
    //need: answer == x*y
  }

  Deduce(
    1 ( answer == x*y ) by Premise, //established in both if and else
                                  //proves postcondition
  )

  //what do we need to do here?

  //need: answer == x*y to satisfy the postcondition

  return answer
}

////////////// Test code //////////////

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