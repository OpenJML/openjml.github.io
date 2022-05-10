---
title: JML Tutorial - Exercises - Multiple Method Behavior
---
# Multiple Method Behavior Exercises:
## **Question 1**
**Given the function below, determine the strongest specifications needed to verify the function below.**
```Java
public int mean(int sum, int totalNum) {
	if(totalNum == 0) throw new ArithmeticException();
		
  	return sum/totalNum;
}
```
**Asnwer and Explanation:**
The function `mean()` above takes in two integer variables `sum` and `totalNum` and returns the mean of the two (`sum/totalNum`). Within the function we check if `totalNum` is zero in which case we throw an exception since we cannot divide by zero. Our second case is If `totalNum` is not equal to zero then we return `sum/totalNum`. To determine the specifications let's treat this like any other function and then determine our method behavior specifications. 

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
+ [Multiple Method Behavior Exercises](MultMethodBehaviorEx.md)
+ [Question 1 Java](MethodBehaviorsExample1.java)
