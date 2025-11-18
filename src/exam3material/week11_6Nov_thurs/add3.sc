// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

var x: Z = Z.prompt("Enter a positive number: ")

assume(x > 0)


//orig will always be the original user input value
val orig: Z = x

//do we need a proof block here? 

//this deduce block is unnecessary
Deduce(
    1 ( x > 0 ) by Premise, //from assume
    2 ( orig == x ) by Premise, //from assignment
)

x = x + 1

Deduce(
    1 ( x == Old(x) + 1 ) by Premise, //from previous assignment
    2 ( Old(x) > 0 ) by Premise,    //from previous assume
    3 ( orig == Old(x) ) by Premise, //from previous assignment
    4 ( x > 1 ) by Algebra*(1, 2), //progress towards 2nd assert
    5 ( x == orig + 1 ) by Subst_>(3, 1)    //progress towards 1st assert
)


//what can we put in a proof block here?
//what should we be able to assert about x and orig?

x = x + 2

Deduce(
    1 ( Old(x) > 1 ) by Premise, //from previous block
    2 ( x == Old(x) + 2 ) by Premise, //from assignment statement
    3 ( Old(x) == orig + 1 ) by Premise, //from previous block
    4 ( x == orig + 3 ) by Algebra*(2,3), //prove 1st assert
    5 ( x > 3 ) by Algebra*(1, 2) //prove 2nd assert
)


assert(x == orig + 3)
assert(x > 3)