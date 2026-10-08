---
title: JML Tutorial - Exercises - Old and Ordering of Clauses
---
# Old and Ordering Exercises Key:
## [Old and Ordering Tutorial](https://www.openjml.org/tutorial/OldAndOrdering)

## **Question 1**
No, the order of frame condition clauses does not matter, as the effective frame condition is the intersection of the frames mentioned in all of the frame conditions (within a given specification case). See the last topic in the [Frame Conditions Tutorial](https://www.openjml.org/tutorial/FrameConditions) for more details.

## **Question 2**
The problem is that to use the remainder operator (`%` in Java and JML) the second (right hand) argument must be non-zero.  So a solution to the exercise is to move the requires clause containing `0 < div` above the requires clause that uses `div` in the formula `n % div == 0`. In our solution below, we also put the requires clauses above the ensures clauses, but that is just a matter of style.
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
    /** This class represents the quadratic formula
        first*x^2 + second*x + third **/
    private /*@ spec_public @*/ double first;
    private /*@ spec_public @*/ double second;
    private /*@ spec_public @*/ double third;

    //@ requires !Double.isNaN(a);
    //@ requires !Double.isNaN(b);
    //@ requires !Double.isNaN(c);
    //@ requires 0.0 < a < Double.POSITIVE_INFINITY;
    //@ requires 0.0 < (b*b) - 4.0 * (a*c) < Double.POSITIVE_INFINITY;
    /*@ ensures first == a && second == b && third == c; @*/
    public Quadratic(double a, double b, double c) {
        first = a;
        second = b;
        third = c;
    }

    //@ old double eps = 2E-6;
    //@ old double a = first;
    //@ old double b = second;
    //@ old double c = third;
    //@ old double b2 = b*b;
    //@ old double discrim = b2 - 4.0*a*c;
    //@ requires 0.0 < discrim < Double.POSITIVE_INFINITY;
    //@ ensures \result.length == 2;
    //@ ensures Math.abs(\result[0] - (-b + Math.sqrt(discrim)) / (2.0*a)) < eps;
    //@ ensures Math.abs(\result[1] - (-b - Math.sqrt(discrim)) / (2.0*a)) < eps;
    //@ pure
    public double[] roots() {
        //@ assume 0.0 < first < Double.POSITIVE_INFINITY;
        //@ assume second != Double.POSITIVE_INFINITY;
        //@ assume second != Double.NEGATIVE_INFINITY;
        //@ assume third != Double.POSITIVE_INFINITY;
        //@ assume third != Double.NEGATIVE_INFINITY;
        double eps = 2E-6;
        double a = first;
        double b = second;
        double c = third;
        double b2 = b*b;
        double discrim = b2 - 4.0*a*c;
        //@ assume 0.0 < discrim < Double.POSITIVE_INFINITY;

        double res[] = new double[2];
        res[0] = -b + Math.sqrt(-b + Math.sqrt(discrim) / (2.0*a));
        //@ assume Math.abs(res[0] - (-b + Math.sqrt(discrim)) / (2.0*a)) < eps;
        res[1] = -b - Math.sqrt(-b - discrim) / (2.0*a);
        //@ assume Math.abs(res[1] - (-b - Math.sqrt(discrim)) / (2.0*a)) < eps;
        return res;
    }
}
```

**Explanation:**
With the current OpenJML implementation (21.0.28), verification of the above times out, due to limitations of the SMT solvers handling of complex formulas involving floating-point (or real) numbers.
Furthermore, we have not independently verified that the code produces the correct approximations as results, so it could be that some of the formulas make the results inexact for some cases.

Furthermore, the repeated preconditions about the discriminant (`discrim` in the above) being strictly positive could be better handled by an invariant. See [the tutorial section on invariants](https://www.openjml.org/tutorial/Invariants) for details.

## **Resources:**
+ [Old and Ordering Exercises](OldAndOrderingEx)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)
