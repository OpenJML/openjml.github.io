---
title: JML Tutorial - Exercises - Old and Ordering of Clauses
---
# Old and Ordering Exercises:
## [Old and Ordering Tutorial](https://www.openjml.org/tutorial/OldAndOrdering)

## **Question 1**
**Does the ordering of frame condition clauses (such as `assignable` or `assigns`) matter in JML?**

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

    //@ requires 0.0 < (second*second) - 4.0*first*third < Double.POSITIVE_INFINITY;
    //@ ensures \result.length == 2;
    //@ ensures Math.abs(\result[0] - ((-second + Math.sqrt((second*second) - 4.0*first*third)) / (2.0*first))) < 2E-6;

    //@ ensures Math.abs(\result[1] - ((-second - Math.sqrt((second*second) - 4.0*first*third)) / (2.0*first))) < 2E-6;
    //@ pure
    public double[] roots() {
        //@ assume 0.0 < first < Double.POSITIVE_INFINITY;
        //@ assume second != Double.POSITIVE_INFINITY;
        //@ assume second != Double.NEGATIVE_INFINITY;
        //@ assume third != Double.POSITIVE_INFINITY;
        //@ assume third != Double.NEGATIVE_INFINITY;
        double res[] = new double[2];
        res[0] = -second + Math.sqrt((second*second) - 4.0*first*third) / (2.0*first);
        //@ assume Math.abs(res[0] - ((-second + Math.sqrt((second*second) - 4.0*first*third)) / (2.0*first))) < 2E-6;
        res[1] = -second - Math.sqrt((second*second) - 4.0*first*third) / (2.0*first);
        //@ assume Math.abs(res[1] - ((-second - Math.sqrt((second*second) - 4.0*first*third)) / (2.0*first))) < 2E-6;
        return res;
    }
}
```

**Learning Objectives:**
+ Understand how the order of clauses affects a specification.
+ Understand how to use `old` clauses to simplify a specification.

## **[Answer Key](OldAndOrderingExKey.md)**
## **[All exercises](https://www.openjml.org/tutorial/exercises/exercises)**

## Resources
+ [Question 2 Java code](OldAndOrderingEx2.java)
+ [Question 3 Java code](Quadratic.java)
