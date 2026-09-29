---
title: JML Tutorial - Exercises - Old and Ordering of Clauses
---
# Old and Ordering Exercises Key:
## [Old and Ordering Tutorial](https://www.openjml.org/tutorial/OldAndOrdering)

## **Question 1**
No, the order of frame condition clauses does not matter, as the effective frame condition is the intersection of the frames mentioned in all of the frame conditions (within a given specification case). See the last topic in the [Frame Conditions Tutorial](https://www.openjml.org/tutorial/FrameConditions) for more details.

## **Question 2**
The problem is that to use the remainder (`%`) operator (in Java or JML) the second (right hand) argument must be non-zero.  So a solution to the exercise is to move the requires clause containing `0 < div` above the requires clause that uses `div` in the formula `n % div == 0`. In our solution below, we also put the requires clauses above the ensures clauses, but that is just a matter of style.
```
public class OldAndOrderingEx2 {
    private /*@ spec_public @*/ long number;
    private /*@ spec_public @*/ int aDivisor;

    //@ requires div > 0;
    //@ requires n >= 0;
    //@ requires n % div == 0;
    //@ ensures number == n && aDivisor == div;
    //@ ensures n % div == 0;
    public OldAndOrderingEx2(long n, int div) {
        number = n;
        aDivisor = div;
    }
}
```
## **Question 3**
The specification can be simplified by using several `old` clauses, as in the following.
```
public class Quadratic {
    /* factors are: (x + first) and (x + second) */
    private /*@ spec_public @*/ double first;
    private /*@ spec_public @*/ double second;

    //@ requires !Double.isNaN(f);
    //@ requires !Double.isNaN(s);
    //@ requires 0.0 < (f+s)*(f+s) - 4.0 * (f*s);
    /*@ ensures first == f && second == s; @*/
    public Quadratic(double f, double s) {
        first = f;
        second = s;
    }

    //@ old double fps = first+second;
    //@ old double discrim = fps*fps - 4.0 * (first*second);
    //@ requires 0.0 < discrim;
    //@ ensures \result.length == 2;
    //@ ensures Math.abs(\result[0] - (-fps + Math.sqrt(discrim) / 2.0)) < 0.1e-9;
    //@ ensures Math.abs(\result[1] - (-fps - Math.sqrt(discrim) / 2.0)) < 0.1e-9;
    //@ pure
    public double[] roots() {
        double res[] = new double[2];
        if (second > first) {
            res[0] = -first;
            res[1] = -second;
        } else {
            res[0] = -second;
            res[1] = first;
        }
        return res;
    }
}
```

**Explanation:**
With the current OpenJML implementation, the above does not verify, because the version of the SMT solver that OpenJML uses cannot handle complex formulas involving real numbers.
It is also not clear that the code in the method `roots()` is correct.

Furthermore, the repeated preconditions about the discriminant being strictly positive could be better handled by an invariant. See [the tutorial section on invariants](https://www.openjml.org/tutorial/Invariants) for details.

## **Resources:**
+ [Old and Ordering Exercises](OldAndOrderingEx)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)
