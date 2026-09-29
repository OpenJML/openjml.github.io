---
title: JML Tutorial - Exercises - Invariant clauses
---
# Exercises
## [Invariants Tutorial](https://www.openjml.org/tutorial/Invariants)

## **Question 1**
**The following class does not verify. Add one or more `invariant` clauses and fix the specifications and the code so that it verifies and makes the assertions in method `test()` pass.** 

```Java
public class ScreenPoint {
    public static final int MAX_SIZE = 2048;
    
    private /*@ spec_public @*/ int x, y;

    //@ requires 0 <= xv < MAX_SIZE;
    //@ requires 0 <= yv < MAX_SIZE;
    //@ ensures x == xv && y == yv;
    public ScreenPoint(int xv, int yv) {
        x = xv;
        y = yv;
    }

    //@ requires Integer.MIN_VALUE <= x+mv <= Integer.MAX_VALUE;
    //@ assignable x;
    //@ ensures x == \old(x+mv);
    public void moveRight(int mv) {
        x += mv;
    }

    //@ requires Integer.MIN_VALUE <= y+mv <= Integer.MAX_VALUE;
    //@ assignable y;
    //@ ensures y == \old(y+mv);
    public void moveUp(int mv) {
        y += mv;
    }

    public static void test() {
        //@ assert 0 <= 5;
        ScreenPoint p = new ScreenPoint(5, 7);
        java.util.Random r = new java.util.Random();
        int mv = r.nextInt(-4096, 4096);

        p.moveRight(mv);
        //@ assert 0 <= p.x < MAX_SIZE;
        p.moveUp(mv);
        //@ assert 0 <= p.y < MAX_SIZE;
    }
}
```

In your solution, you must add one or more `invariant` clauses to the class. Doing that may make it necessary to change some method preconditions. However, changing those preconditions will also require changes in the code for the method `test()`, but you should make those without changing the calls to `moveRight` and `moveUp` and the assertions that follow those calls.

## **Question 2**
**Consider the following class that also does not verify. Write one or more `invariant` clauses and an `assume` statement to explain (to OpenJML) why the code in the `equals` method is correct.**

```
public class Rational {
    private /*@ spec_public @*/ long n, d;

    //@ requires dv != 0;
    //@ requires nv % dv != 0;
    public Rational(int nv, int dv) {
        n = nv;
        d = dv;
    }

    //@   requires oth == null;
    //@   ensures !\result;
    //@ also
    //@   requires oth != null;
    //@   ensures \result <==> d * oth.n == n * oth.d;
    public boolean equals(/*@ nullable @*/ Rational oth) {
        if (oth == null) {
            return false;
        }
        // whd would the following be correct? When would it be correct?
        return n == oth.n && d == oth.d;
    }
        
}
```

## **[Answer Key](InvariantsExKey)**

## Resources
+ [Question 1 Java](ScreenPoint.java)
+ [Question 2 Java](Rational.java)
+ [All exercises](exercises)
