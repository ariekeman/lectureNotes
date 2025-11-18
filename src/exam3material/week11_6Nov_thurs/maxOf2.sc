// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._


val a: Z = Z.prompt("Enter first number: ")
val b: Z = Z.prompt("Enter second number: ")

var max: Z = 0

if (a > b) {
  max = a

  Deduce(
    1 ( a > b ) by Premise, //from condition
    2 ( max == a ) by Premise, //from assignment
    3 ( max >= a ) by Algebra*(2),
    4 ( max >= b ) by Algebra*(1,2)

    //goal: max >= a
    //goal: max >= b
  )
} else {
  max = b

  Deduce(
    1 ( !(a > b) ) by Premise, //condition is false
    2 ( max == b ) by Premise, //from assignment
    3 ( a <= b ) by Algebra*(1),
    4 ( max >= b ) by Algebra*(2),
    5 ( max >= a ) by Algebra*(2,3)

    //goal: max >= a
    //goal: max >= b
  )
}

Deduce(                                 //proves 2nd assert
  1 ( max == a | max == b ) by Premise, //LHS from if, RHS from else
  2 ( max >= a ) by Premise, //true in both branches
  3 ( max >= b ) by Premise, //true in both branches
  4 ( max >= a & max >= b ) by AndI(2,3) //proves 1st assert
  //goal: max == a | max == b
  //goal: max >= a & max >= b
)



//assert that we have found the max
assert(max >= a & max >= b)
assert(max == a | max == b)