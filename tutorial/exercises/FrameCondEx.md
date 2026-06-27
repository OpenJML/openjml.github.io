---
title: JML Tutorial - Exercises - Frame Condtions 
---
# Frame Condtions Exercises:
## [Frame Conditions Tutorial](https://www.openjml.org/tutorial/FrameConditions)

## **Question 1**
**The class `FrameCondEx1` puts in `maxValue` the maximum of the fields `x` and `y`. However, the code is unable to be verified; determine what specifications are needed to verify the program. Hint: frame conditions should be specified for the methods `determineMax()` and `xGreaterThanY()`.**
```Java
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
    
    //@ ensures maxValue == x || maxValue == y;
    //@ ensures x <= maxValue;
    //@ ensures y <= maxValue;
    public void determineMax() {
        boolean xgty = xGreaterThanY();
        if (xgty) {
            maxValue = x;
        } else {
            maxValue = y;
        }
    }

    //@ ensures \result <==> (x > y);
    public boolean xGreaterThanY() {
        return x > y;
    }

    public void test() {
        FrameCondEx1 fc12 = new FrameCondEx1(1,2);
        //@ assert fc12.x == 1;
        //@ assert fc12.y == 2;
        fc12.determineMax();
        //@ assert fc12.maxValue == 2;
        //@ assert fc12.x == 1;
        //@ assert fc12.y == 2;
    }
}
```

## **Question 2**
**The following class does not verify. What frame conditions and code changes need to be made so that it will verify?**
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
        this.normalize();
        m.normalize();
        return this.dollars == m.dollars && this.cents == m.cents;
    }
        

    //@ requires dollars + cents/100 <= Integer.MAX_VALUE;
    //@ ensures cents < 100;
    public void normalize() {
        if (cents >= 100) {
            dollars += cents/100;
            cents = cents % 100;
        }
    }
}

```

**Learning Objectives:**
+ Gain more experience writing frame conditions and using the `assignable` clause
+ Understand how to use the `\old` designator 
+ Understand the importance of denoting when memory locations have been modified

## **[Answer Key](FrameCondExKey.md)**
+ [Question 1 Java](FrameCondEx1.java)
+ [Question 2 Java](Money.java)
## **[All exercises](https://www.openjml.org/tutorial/exercises/exercises)**
