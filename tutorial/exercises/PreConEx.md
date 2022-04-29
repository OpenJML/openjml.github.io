---
title: JML Tutorial - Exercises - Preconditions
---
# Precondition Exercises:
## **Question 1**
**The function below will update a user's bank account after making a purchase of a certain number of items. We want to make sure that the user's bank account is never below $0.00. What specifications can we implement to ensure that the user's bank account is never negative?**
```Java
public double bankUpdate(double bankAccount, double price, int n) {
		bankAccount = bankAccount - (price*n);
		return bankAccount;
}
```
**On the subject of NaN:** 
NaN stands for “not a number” and occurs when a floating point operation has some input that results in an undefined answer. A very common example of this would be trying to divide zero by zero or taking the square root of a negative number. It is helpful to use the isNaN() function from the Java class Double when working with floating points because it will check if the input is a floating point or not a number. isNaN() will return true if the input is not a number, else it will return false. 

**Learning Objective:** 
+ Gain more experience writing preconditions 
+ Be able to identify preconditions that will prevent errors
+ Be able to identify preconditions that won’t cause a warning in OpenJML but are logically important to the code

## **Question 2**
**Given an integer array, write a binary search function, and include any specifications needed to verify the function.**

**Learning Objective:** 
+ Understand relationship between pre/postconditions and arrays
+ Introduction to the `\forall` clause
+ Understand the usefulness of using preconditions to check inputs to the code 

## **[Answer Key](PreConExKey.md)**
