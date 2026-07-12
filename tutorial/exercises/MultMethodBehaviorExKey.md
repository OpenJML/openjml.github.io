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
The first specification case describes the "normal" behavior of the method (although it could be the second specification case instead). It says that the answer returned is 

The function `mean()` takes in two integer variables `sum` and `totalNum` and returns the mean of the two (`sum/totalNum`). Within the function we check if `totalNum` is zero in which case we throw an exception since we cannot divide by zero. This gives the second specification case (although it does not need to be second).



First let’s tackle when `totalNum` is greater than zero and less than `Integer.MAX_VALUE`, and that `sum` is less than `Integer.MAX_VALUE`. These preconditions will apply when the function is acting how we would expect it to act normally, in which case we know that our function will return the result `sum/totalNum`. So let’s write this specification case:
```Java
//@ public normal_behavior
//@	requires 0 < totalNum < Integer.MAX_VALUE;
//@	requires sum < Integer.MAX_VALUE;
//@	ensures \result == sum/totalNum;
public int mean(int sum, int totalNum) {
	if(totalNum == 0) throw new ArithmeticException();
	
	return sum/totalNum;
}
```
But what about when ‘totalNum’ is equal to zero? We throw an arithmetic exception. So we can determine out exception behavior by stating that total must be equal to zero and signals_only `ArithmeticException()`. Recall that we use the `also` clause when dealing with multiple method behaviors. 
```Java
//@ public normal_behavior
//@	requires 0 < totalNum < Integer.MAX_VALUE;
//@ 	requires sum < Integer.MAX_VALUE;
//@	ensures \result == sum/totalNum;
//@ also public exceptional_behavior
//@	requires totalNum == 0;
//@ 	signals_only ArithmeticException;
public int mean(int sum, int totalNum) {
	if(totalNum == 0) throw new ArithmeticException();
	
	return sum/totalNum;	
 }
```
**Learning Objective:** 
The goal of this exercise is to task the student identifying all the specification cases for this program. The student should recongize that we have the case where `totalNum` is or isn’t equal to zero. The student should also understand how to use `normal_behavior` and `exceptional_behavior`.

## **Resources:**
+ [Multiple Method Behavior tutorial](https://www.openjml.org/tutorial/MultMethodBehavior)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)
