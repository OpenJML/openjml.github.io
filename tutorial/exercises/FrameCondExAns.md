---
title: JML Tutorial - Exercises - Frame Condtions 
---
# Frame Condtions Exercises Key:
## [Frame Conditions Tutorial](https://www.openjml.org/tutorial/FrameConditions)

## **Question 1**
Adding a frame condition that says that maxValue can be assigned in the method `determineMax()` and one that says that `xGretaterThanY()` has no effects (or is pure), allows the program to be verified, as in the following.
```
public class FrameCondEx1 {
    private /*@ spec_public @*/ int maxValue;
    private /*@ spec_public @*/ int x;
    private /*@ spec_public @*/ int y;

    //@ ensures x == xv && y == yv;
    //@ pure
    public FrameCondEx1(int xv, int yv) {
        x = xv;
        y = yv;
    }

    //@ assignable maxValue;
    //@ ensures x == maxValue || y == maxValue;
    //@ ensures x <= maxValue && y <= maxValue;
    public void determineMax() {
        if (xGreaterThanY()) {
            maxValue = x;
        } else {
            maxValue = y;
        }
    }

    //@ ensures \result <==> (x > y);
    //@ pure
    public boolean xGreaterThanY() {
        return x > y;
    }

    public void test() {
        FrameCondEx1 fca12 = new FrameCondEx1(1,2);
        //@ assert fc12.x == 1;
        //@ assert fc12.y == 2;
        fca12.determineMax();
        //@ assert fc12.maxValue == 2;
        //@ assert fc12.x == 1;
        //@ assert fc12.y == 2;
    }
}

```
**Asnwer and Explanation:**
The problem, as one can see by running ESC on the code in the exercise (which gives the following output)
```
FrameCondEx1.java:36: verify: The prover cannot establish an assertion (Assert) in method test
        //@ assert fc12.x == 1;
            ^
FrameCondEx1.java:35: verify: The prover cannot establish an assertion (Assert) in method test
        //@ assert fc12.maxValue == 2;
            ^
2 verification failures
```

is that the specification of `determineMax()` does not prevent that method from changing either `x` or `y`.
So one should add to the specification of `determineMax()` the following frame condition.
```
    //@ assignable maxValue;
```
(or a synonym, such as `assigns maxValue`).

However, if one only makes that change, then call of `xGreaterThanY()` in `determineMax` also causes several verification errors, including the following.

```
FrameCondEx1.java:24: warning: Method xGreaterThanY() has 'assignable \everything', making its caller likely impossible to verify
    //@ ensures \result <==> (x > y);
        ^
```

The trouble is that the verification of the call to `xGreaterThanY()` assumes that it does not change the class's fields. However, since JML does verification method by method, the specification of `xGreaterThanY()` needs to say that, thus the `xGreaterThanY()` method needs to be declared as `assignable \nothing` or `pure`.

## **Question 2**
**The following class does verify.
```Java
public class Money {
    private /*@ spec_public @*/ int dollars, cents;

    //@ requires c < 100;
    //@ ensures dollars == d && cents == c;
    public Money(int d, int c) {
        dollars = d;
        cents = c;
    }

    //@ requires this != m;
    //@ requires dollars + cents/100 <= Integer.MAX_VALUE;
    //@ requires m.dollars + m.cents/100 <= Integer.MAX_VALUE;
    /*@ ensures \result <==> (this.dollars == m.dollars
      @                        && this.cents == m.cents); @*/
    public /*@ pure @*/ boolean equals(Money m) {
        return this.dollars == m.dollars && this.cents == m.cents;
    }
        

    //@ requires dollars + cents/100 <= Integer.MAX_VALUE;
    //@ assignable dollars, cents;
    //@ ensures cents < 100;
    public void normalize() {
        if (cents >= 100) {
            dollars += cents/100;
            cents = cents % 100;
        }
    }
}

```
The above solution adds a frame condition to the method `normalize()`, which limits the fields that can be changed to just the `dollars` and `cents` of the receiver (`this`).
This solution also declares the `equals` method to be `pure` (which is equivalent to `assignable \nothing`). And thus to verify it must removes the calls to the non-pure method `normalize()`, since those have effects. (With this change, the precondition `this != m` is no longer needed for the `equals` method, but the method cannot normalize the `Money` objects before making the comparison. One might require that the `Money` objects being compared be normalized before calling `equals` but a better solution might be to enforce an invariant that `cents < 100` for all `Money` objects;
see [the tutorial section on invariants](InitiallyConstraint).

**Learning Objective:** 
The goal of this exercise is to see if the student understands how to use frame clauses. We want to make sure that the student understands that we need to specify any occurrence of memory locations is being modified. 

## **Resources:**
+ [Frame Conditions Exercises](FrameCondEx.md)
+ [Question 1 Java](FrameCondEx1.java)
+ [Question 2 Java](Money.java)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)
