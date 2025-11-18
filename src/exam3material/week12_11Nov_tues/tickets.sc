// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//adult tickets: $50
//kid tickets: $30
def getTicketCosts(adult: Z, kid: Z): Z = {
  //what do we want for our function contract?
  Contract(
    Requires(
      adult >= 0,
      kid >= 0
    ),
    Ensures(
      Res[Z] >= 0,
      Res[Z] == adult*50 + kid*30
    )
  )

  //what to do here? list preconditions (requires) as premises
  Deduce(
    1 ( adult >= 0 ) by Premise,
    2 ( kid >= 0 ) by Premise
  )


  //get the total ticket cost
  val overall: Z = adult*50 + kid*30

  //what to do here?
  Deduce(
      1 ( overall == adult*50 + kid* 30 ) by Premise, //from previous assignment
      2 ( adult >= 0 ) by Premise,
      3 ( kid >= 0 ) by Premise,
      4 ( overall >= 0 ) by Algebra*(1,2,3)
    //need: overall >= 0
    //need: overall == adult*50 + kid*30
  )

  return overall
}

////////////// Test code /////////////////

val k: Z = 3 //$30 each
val a: Z = 2 //$50 each

//what to do here?
//prove the preconditions based on the parameters I am passing

//a >= 0
//k >= 0

Deduce(
  1 ( k == 3 ) by Premise,
  2 ( a == 2 ) by Premise,
  3 ( a >= 0 ) by Algebra*(2),  //proves 1st precondition
  4 ( k-1 >= 0 ) by Algebra*(1) //proves 2nd precondition
)

val cost: Z = getTicketCosts(a, k-1)

//what to do here?
Deduce(
  1 ( cost == a*50 + (k-1)*30 ) by Premise, //from postcondition
  2 ( k == 3 ) by Premise,
  3 ( a == 2 ) by Premise,
  4 ( cost == 160) by Algebra*(1,2,3)
)

//what *should* cost be?
assert(cost == 160)