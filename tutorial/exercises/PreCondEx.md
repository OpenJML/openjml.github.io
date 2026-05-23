---
title: JML Tutorial - Exercises - Preconditions
---
# Precondition Exercises:
## [Preconditions Tutorial](https://www.openjml.org/tutorial/Preconditions)

## **Question 1**

**The function below will update a user's bank account after making a purchase of a certain number of items. We want to make sure that the user's bank account is never below $0.00. What specifications can we implement to ensure that the user's bank account is never negative?**
```Java
public double bankUpdate(double bankAccount, double price, int n) {
		bankAccount = bankAccount - (price*n);
		return bankAccount;
}
```
**Java's NaN** 

NaN stands for “not a number” and is used as the result of a floating point operation that results in an undefined answer. A common example of this would be trying to divide zero by zero or taking the square root of a negative number. It is helpful to use the `isNaN()` method from the Java class `Double` (or `Float`) when working with floating point numberss because it will check if the input is not a number. The `isNaN()` method will return _true_ if the input is not a number, else it will return _false_. However, every other floating point comparison involving NaN returns _false_; even if `x` and `y` are both NaN, then `x == y` is _false_, so testing arugments with `isNaN()` is the only reliable way to work with floating point numbers.

**Learning Objectives:** 
+ Gain more experience writing preconditions 
+ Be able to identify preconditions that will prevent errors
+ Be able to identify preconditions that won’t cause a warning in OpenJML but are logically important to the code

## **Question 2**
**Given an integer array, write a binary search function, and include any specifications needed to verify the function.**

**Learning Objectives:** 
+ Understand relationship between pre/postconditions and arrays
+ Introduction to the `\forall` clause
+ Understand the usefulness of using preconditions to check inputs to the code 

## **[Answer Key](PreConExKey.md)**
## **[All exercises](https://www.openjml.org/tutorial/exercises/exercises)**
