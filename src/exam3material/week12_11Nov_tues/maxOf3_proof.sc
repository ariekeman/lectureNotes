// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

val a: Z = Z.read()    
val b: Z = Z.read()    
val c: Z = Z.read()    
var max: Z = 0


if (a >= b) {
  if (a >= c) {
    max = a

    Deduce(
      1 ( max == a ) by Premise,
      2 ( a >= b ) by Premise, //outer if is true
      3 (a >= c) by Premise, //inner if is true
      4 ( max >= a) by Algebra*(1),
      5 ( max >= b ) by Subst_>(1, 2),
      6 (max >= c) by Subst_>(1, 3),
      7 (max == a | max == b) by OrI1(1),
      8 (max == a | max == b | max == c) by OrI1(7)
    )
  } else {
    max = c

    Deduce(
      1 (max == c) by Premise,
      2 (a >= b) by Premise, //outer if condition is true
      3 (!(a >= c)) by Premise, //inner if condition is false
      4 (max >= c) by Algebra*(1),
      5 (max >= a)  by Algebra*(1, 3),
      6 (max >= b) by Algebra*(2, 5),
      7 ( max == a | max == b | max == c ) by OrI2(1)
    )
  }

  //summary logic block
  Deduce(
    //FILL IN
    //what can we state as premises?
    1 ( max >= a ) by Premise,
    2 ( max >= b ) by Premise,
    3 ( max >= c ) by Premise,
    4 ( max == a | max == b | max == c ) by Premise
  )
} else {
  if (b >= c) {
    max = b

    //block here
    Deduce(
      1 (!(a >= b)) by Premise,
      2 (b >= c) by Premise,
      3 (max == b) by Premise,
      4 (max >= a) by Algebra*(3, 1),
      5 (max >= b) by Algebra*(3),
      6 (max >= c) by Algebra*(2, 3)
    )
  } else {
    max = c

    //block here
    Deduce(
      1 (!(a >= b)) by Premise,
      2 (!(b >= c)) by Premise,
      3 (max == c) by Premise,
      4 (max >= a) by Algebra*(1, 2, 3),
      5 (max >= b) by Algebra*(2, 3),
      6 (max >= c) by Algebra*(3)
    )
  }
  //summary block
  Deduce(
    //what goes here?
    1 ( max >= a ) by Premise,
    2 ( max >= b ) by Premise,
    3 ( max >= c ) by Premise,
    4 ( max == b | max == c ) by Premise, //LHS from else/if, RHS from else/else

    5 SubProof(
      6 Assume (max == b),
      7 ( max == a | max == b ) by OrI2(6),
      8 ( max == a | max == b | max == c ) by OrI1(7)
    ),
    9 SubProof(
      10 Assume (max == c),
      11 ( max == a | max == b | max == c ) by OrI2(10)
    ),
    12 ( max == a | max == b | max == c ) by OrE(4,5,9)
  )
}

//overall summary here
//summarize both branches
Deduce(
  1 (max >= a) by Premise,
  2 (max >= b) by Premise,
  3 (max >= c) by Premise,
  4 (max == a | max == b | max == c) by Premise //true in outer if and else
)

println("Max between ", a, ", ", b, " and ", c, " is ", max)

assert(max >= a)
assert(max >= b)
assert(max >= c)
assert(max == a | max == b | max == c)