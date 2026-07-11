---
title: JML Tutorial - Exercises - Old and Ordering of Clauses
---
# Old and Ordering Exercises:
## [Old and Ordering Tutorial](https://www.openjml.org/tutorial/OldAndOrdering)

## **Question 1**
**Does the ordering of frame condition clauses (such as `assignable` or `assigns` clauses matter in JML?**

## **Question 2**
**The following class does not verify. What changes could be made to clause orderings (in the constructor's specification) to make it verify? (Note: no code or specifications should be changed, only the ordering of clauses in the specifications.)**
```Java
public class OldAndOrderingEx2 {
    private /*@ spec_public @*/ long number;
    private /*@ spec_public @*/ int aDivisor;

    //@ ensures number == n && aDivisor == div;
    //@ ensures n % div == 0;
    //@ requires n % div == 0;
    //@ requires div > 0;
    //@ requires n >= 0;
    public OldAndOrderingEx2(long n, int div) {
        number = n;
        aDivisor = div;
    }
}
```

## **Question 3**
**The following class has a lot of repeated formulas in the specification of the method `roots()`. Simplify the specification of that method using `old` clauses.**
```Java
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

    //@ requires 0.0 < (first+second)*(first+second) - 4.0 * (first*second);
    //@ ensures \result.length == 2;
    //@ ensures Math.abs(\result[0] - (- (first+second) + Math.sqrt((first+second)*(first+second) - 4.0 * (first*second))) / 2.0) < 0.1e-9;
    //@ ensures Math.abs(\result[1] - (- (first+second) - Math.sqrt((first+second)*(first+second) - 4.0 * (first*second))) / 2.0) < 0.1e-9;
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

**Learning Objectives:**
+ Understand how the order of clauses affects a specification.
+ Understand how to use `old` clauses to simplify a specification.

## **[Answer Key](OldAndOrderingExKey.md)**
+ [Question 2 Java](OldAndOrderingEx1.java)
+ [Question 3 Java](Quadratic.java)
## **[All exercises](https://www.openjml.org/tutorial/exercises/exercises)**
