// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._

//sum of first n even numbers
def sumEvens(n: Z): Z = {
  //What can we use as the function contract?
  Contract(
	  Requires( n >= 0 ),
	  Ensures(Res[Z] == n*(n+1))
  )

  var sum: Z = 0
  var cur: Z = 0
  
  //need a Deduce block
  //premises: n >= 0, sum == 0, cur == 0
  //need to prove: sum == cur*(cur+1)

  while (cur != n) {
    //what about our loop invariant?
	Invariant(
		Modifies(cur, sum),
		sum == cur*(cur+1)
	)

    cur = cur + 1
	
    //need a Deduce block
    //premises: cur == Old(cur) + 1, sum == Old(cur)*(Old(cur)+1),
        //Old(cur) != n, n >= 0
    //need: statement about the invariant without an Old
      //(won't be able to prove exact invariant yet)
	
    sum = sum + 2*cur
	
    //premise: sum == Old(sum) + 2*cur, n >= 0
    //need: sum == cur*(cur+1)
  }
  
  //premises: sum == cur*(cur+1), !(cur != n), n >= 0
  //need: sum == n*(n+1)

  return sum
}

//////////// test code /////////

val num: Z = 5

//premise: num == 5
//need: num >= 0

var sum5evens: Z = sumEvens(num)

//premise: sum5evens == num*(num+1), num == 5
//need: sum5evens == 30

//sum of first 5 evens: 30
assert(sum5evens == 30)
