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

Effectively the precondition of the method (which describes when it can be called without a verification error) says that `totalNum` must be at least zero; that is it must be non-negative.

Also note that in neither case is it necessary to constrain `sum` to be a legal integer, since the type system of Java does that already.

## **Resources:**
+ [Multiple Method Behavior tutorial](https://www.openjml.org/tutorial/MultMethodBehavior)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)
