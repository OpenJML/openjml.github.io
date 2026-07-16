---
title: JML Tutorial - Exercises - Invariant clauses
---
# Exercises
## [Invariants Tutorial](https://www.openjml.org/tutorial/Invariants)

## **Question 1**
**The following class does not verify. Fix the specifications and the code so that it verifies and makes the assertions in method `test()` pass.** 

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

In your solution, you will need to add one or more `invariant` clauses to the class and that may make it necessary to change some method preconditions. However, changing those preconditions will also require changes in the code for the method `test()`, but you should make those without changing the calls to `moveRight` and `moveUp` and the assertions that follow those calls.

## **Question 2**

## **[Answer Key](InvariantsExKey)**

## Resources
+ [Question 1 Java](ScreenPoint.java)
+ [Question 2 Java](.java)
+ [All exercises](exercises)
