---
title: JML Tutorial - Exercises - Multiple Method Behavior
---
# Multiple Method Behavior Exercises:
## [Multiple Method Behavior Tutorial](https://www.openjml.org/tutorial/MultipleBehaviors)

## **Question 1**
One possible solution is the following.
```Java
//@   public normal_behavior
//@     requires 0 < totalNum;
//@	ensures \result == sum/totalNum;
//@ also
//@   public exceptional_behavior
//@	requires totalNum == 0;
//@     signals_only ArithmeticException;
public int mean(int sum, int totalNum) {
    if(totalNum == 0) {
        throw new ArithmeticException();
    }
    return sum/totalNum;
}
```
The function `mean()` takes in two integer variables `sum` and `totalNum` and returns the mean of the two (`sum/totalNum`).

The first specification case describes the "normal" behavior of the method (although it could be the second specification case instead). It says that the answer returned is `sum/totalNum`. Note that this case has a precondition, which is that `0 < totalNum`, and that this precondition prevents division by zero.

The second specification case (although it does not need to be second) describes what happens if the argument `totalNum` is zero, and says that if that is the case, then the method must throw an`ArithmeticException`.

Effectively the precondition of the entire method (which describes when the method can be called without a verification error) says that `totalNum` must be at least zero; that is `totalNum` must be non-negative for the call to not result in a precondition error during verification. Of course if `totalNum` is zero, then there will be a runtime exception thrown.

Also note that in neither case is it necessary to constrain `sum` to be a legal integer, since the type system of Java does that already.

## **Question 2**
One possible answer is the following, which verifies the code of `testMax`.
```
public class IntMax {
    /*@   requires y <= x;
      @   ensures \result == x;
      @ also
      @   requires x <= y;
      @   ensures \result == y;
      @*/
    //@ pure
    public static int max(int x, int y) {
        if (y <= x) {
            return x;
        } else {
            return y;
        }
    }

    public static void testMax() {
        int m1 = max(5, 7);
        //@ assert m1 == 7;
        int m2 = max(9, 7);
        //@ assert m2 == 9;
        int m3 = max(11,11);
        //@ assert m3 == 11;
    }
}
```

It would be fine to have the precondition of the second specification case be `x < y` instead of `x <= y`. However, the precondition `x <= y` also works, as when `x == y` then both `x <= y` and `y <= x` are true, and the code returns the value of `x`, which is also the value of `y`, and so both postconditions are satisfied.

Note that one could also write a specification, such as `ensures true;` for the method `testMax`, and if this was made a (public) normal behavior, then it would ensure that the method terminated normally (even under runtime assertion checking). However, that is not necessary in this example.

## **Resources:**
+ [Multiple Method Behavior tutorial](https://www.openjml.org/tutorial/MultMethodBehavior)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)
