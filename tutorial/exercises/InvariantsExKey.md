---
title: JML Tutorial - Exercises - Invariant clauses
---
# Invariant Clauses Exercises Key:
## [Invariants Tutorial](https://www.openjml.org/tutorial/Invariants)

## **Question 1**
One way to use invariants to make the code verify is the following.

```Java
public class ScreenPoint {
    public static final int MAX_SIZE = 2048;
    
    private /*@ spec_public @*/ int x, y;
    //@ public invariant 0 <= x < MAX_SIZE;  // key to the solution
    //@ public invariant 0 <= y < MAX_SIZE;  // key to the solution

    //@ requires 0 <= xv < MAX_SIZE;
    //@ requires 0 <= yv < MAX_SIZE;
    //@ ensures x == xv && y == yv;
    public ScreenPoint(int xv, int yv) {
        x = xv;
        y = yv;
    }

    //@ requires 0 <= x+mv < MAX_SIZE;  // changed
    //@ assignable x;
    //@ ensures x == \old(x+mv);
    public void moveRight(int mv) {
        x += mv;
    }

    //@ requires 0 <= y+mv < MAX_SIZE;  // changed
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

        if (0 <= p.x + mv && p.x + mv < MAX_SIZE) { // added
            p.moveRight(mv);
            //@ assert 0 <= p.x < MAX_SIZE;
        }                                           // added
        if (0 <= p.y + mv && p.y + mv < MAX_SIZE) { // added
            p.moveUp(mv);
            //@ assert 0 <= p.y < MAX_SIZE;
        }                                           // added
    }
}

```

**Explanation:**

As you can see in the above, the key point is adding an invariant that describes each of the fields `x` and `y`.  (One could also add a single invariant clause, which would have as its expression the conjunction of the two invariant expressions shown above, conjoined with `&&`; that would be equivalent to what is shown above.) However, if only such invariant clause(s) were added, then the methods `moveRight` and `moveUp` would no longer verify, because they would violate the invariant(s), so it would be necessary to change the preconditions of those two methods, so that the values put into the `x` or `y` fields would still satisfy the invariant(s). Then when the preconditions are changed, the `test()` method would longer verify, since the arguments to `moveRight` and `moveUp` might not satisfy the new preconditions for those methods; thus some code needs to be added to the `test()` method to only call those methods when their preconditions are satisfied.

However, something should also be said about the constructor's frame condition; the constructor has a default assignable clause of `assignable \everything;` (because no frame condition has been specified for it). Fortunately, the method `test()` is `static`, so the instance fields `x` and `y` (i.e., `this.x` and `this.y`) are _not_ part of that method's pre-state. If the `test()` method was not static, then the `x` and `y` fields would be part of the method's pre-state, and so they would be potentially assigned by the call to the constructor; thus the values of these fields might not satisfy the invariant(s) after the constructor call. After the constructor call the fields of `p` satisfy the class's invariant(s) and MAX_SIZE is unchanged (since it is `final`), but at the end of test(), as would be indicated by the mention of `InvariantExit` in the error message, the invariants of the `this` object (the instance fields `this.x` and `this.y` could have been changed (by the call of the constructor) to not satisfy their invariant. This could be prevented by writing an assignable clause for the constructor (such as `assignable \nothing`) or equivalently by declaring the constructor to be `pure`. In conclusion, either the `test()` method should be `static` (so that there are no instance fields available to assign in that method's pre-state) or the constructor should be declared to be `pure` (so that it cannot assign to the instance fields of the `test` method's receiver object's pre-state).

## **Question 2**

## **Resources:**
+ [Invariant Clauses Exercises](InvariantsEx)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)
