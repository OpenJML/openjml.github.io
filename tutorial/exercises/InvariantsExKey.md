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

As you can see in the above, the key point is adding an invariant that describes each of the fields `x` and `y`.  (One could also add a single invariant clause, which would have as its expression the conjunction of the two invariant expressions shown above, conjoined with `&&`; that would be equivalent to what is shown above.) However, if only such invariant clause(s) were added, then the methods `moveRight` and `moveUp` would no longer verify, because they could violate the invariant(s), so it would be necessary to change the preconditions of those two methods, so that the values put into the `x` or `y` fields would still satisfy the invariant(s). Then when the preconditions are changed, the `test()` method would longer verify, since the arguments to `moveRight` and `moveUp` might not satisfy the new preconditions for those methods; thus some code needs to be added to the `test()` method to only call those methods when their preconditions are satisfied.

However, something should also be said about the constructor's frame condition; the constructor has a default assignable clause of `assignable \everything;` (because no frame condition has been specified for it). Fortunately, the method `test()` is `static`, so the instance fields `x` and `y` (i.e., `this.x` and `this.y`) are _not_ part of that method's pre-state. If the `test()` method was not static (i.e., if it were an instance method), then the `x` and `y` fields would be part of the method's pre-state, and so they would be potentially assigned by the call to the constructor; thus the values of these fields might not satisfy the invariant(s) after the constructor call. After the constructor call the fields of `p` satisfy the class's invariant(s) and MAX_SIZE is unchanged (since it is `final`), but at the end of test(), as would be indicated by the mention of `InvariantExit` in error messages, the invariants of the `this` object (the instance fields `this.x` and `this.y` could have been changed (by the call of the constructor) to not satisfy their invariant(s). This could be prevented by writing an assignable clause for the constructor (such as `assignable \nothing`) or equivalently by declaring the constructor to be `pure`. In conclusion, either the `test()` method should be `static` (so that there are no instance fields available to assign in that method's pre-state) or the constructor should be declared to be `pure` (so that it cannot assign to the instance fields of the `test` method's receiver object's pre-state).

## **Question 2**
The reason why the equals method should work is that the class is maintaining an invariant that the fields `n` and `d` have no common divisors, as is required already in the precondition of the constructor. Thus when there are no common divisors, comparing the fields is equivalent to the mathematical definition of when rationals are equal, which is embodied in the postcondition of the `equals` method.  Thus one way to answer this question is as follows.

```
public class Rational {
    private /*@ spec_public @*/ long n, d;
    //@ public invariant d != 0;
    //@ public invariant n % d != 0;

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
    //@ spec_pure
    public boolean equals(/*@ nullable @*/ RationalAns oth) {
        if (oth == null) {
            return false;
        }
        /*@ assume (n == oth.n && d == oth.d && d != 0 && n%d == 0)
                   <==> (d*oth.n == n*oth.d); @*/
        return n == oth.n && d == oth.d;
    }
        
}
```

Although this code has two invriants, one could instead use a single invariant that would be the conjunction of these two, using `&&` and putting the assertion about `d` not being 0 first, to avoid trying to divide by 0.

The `assume` statement in the `equals` method is helping OpenJML's ESC by stating a fact about the integers, which could be proven, but which involves multiplication. Unfortunately the theory of arithmetic with multiplication is undecidable, so the SMT solvers that OpenJML uses (such as Z3) cannot prove such properties themselves.

One could try to do the cross multiplication called for in the specification of `equals` directly in the code, but one would run into several problems. First, one (or both) of the products might cause an arithmetic overflow. (Note that the specifications work with mathematical integers, so that is not a problem of specification.) If one tries to avoid that by using the class `java.math.BigInteger` one discovers that the `multiply` method that is needed is not pure, so it cannot be used in an assertion or in a pure method, and we would like the `equals` method to be pure so it can be used in specifications.

## **Resources:**
+ [Invariant Clauses Exercises](InvariantsEx)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)
