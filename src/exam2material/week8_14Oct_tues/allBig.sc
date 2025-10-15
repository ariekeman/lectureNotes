// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.pred._
import org.sireum.justification.natded.prop._



@pure def allBig[T](P: T=>B @pure, Q: T=>B @pure, R: T=>B @pure, B: T=>B @pure, C: T=>B @pure): Unit = {
  Deduce(
    (
        ∀((x: T) => (P(x) __>: B(x)  )),
        ∀((x: T) => (Q(x) __>: C(x)  )),
        ∀((x: T) => (R(x) __>: !B(x) & !C(x)  ))
    )
      |-
    (
      ∀((x: T) => (P(x) | Q(x) __>: !R(x)  ))
    )
    Proof(
      1 ( ∀((x: T) => (P(x) __>: B(x)  )) ) by Premise,
      2 ( ∀((x: T) => (Q(x) __>: C(x)  )) ) by Premise,
      3 ( ∀((x: T) => (R(x) __>: !B(x) & !C(x)  )) ) by Premise,

      //goal: for all statement, use AllI

      4 Let ((a: T) => SubProof(
        5 SubProof(
            6 Assume (P(a) | Q(a)),

            7 SubProof(
                8 Assume (R(a)),

                //plug a into all my premises
                9 ( P(a) __>: B(a) ) by AllE[T](1),
                10 ( Q(a) __>: C(a) ) by AllE[T](2),
                11 ( R(a) __>: !B(a) & !C(a) ) by AllE[T](3),
                12 ( !B(a) & !C(a) ) by ImplyE(11, 8),
                13 ( !B(a) ) by AndE1(12),
                14 ( !C(a) ) by AndE2(12),

                //use OrE to show contradiction with both P(a) and Q(a)
                15 SubProof(
                    16 Assume (P(a)),
                    17 ( B(a) ) by ImplyE(9, 16),
                    18 ( F ) by NegE(17, 13)

                    //goal: F
                ),
                19 SubProof(
                    20 Assume (Q(a)),
                    21 ( C(a) ) by ImplyE(10, 20),
                    22 ( F ) by NegE(21, 14)
                    //goal: F
                ),
                23 ( F ) by OrE(6, 15, 19)

                //goal: F
            ),
            24 ( !R(a) ) by NegI(7)
            //use NegI
            //goal: !R(a)
        ),
        //use ImplyI
        25 ( P(a) | Q(a) __>: !R(a) ) by ImplyI(5)

        //goal: P(a) | Q(a) __>: !R(a)
      )),
      //use AllI
      26 ( ∀((x: T) => (P(x) | Q(x) __>: !R(x)  )) ) by AllI[T](4)
    )
  )
}