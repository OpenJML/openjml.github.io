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

## **Question 2**
**What precondition would be needed for the following code in the method below to verify? If you can simplify your precondition while still making the code correct, do that.**

```Java
//@ ensures \result == a[0];
public int element0(int a[]) {
   return a[0];

}
```

## **Question 3**

** What precondition would be used in the strongest possible simple specification? What would a suitable be postcondition be?**

## **Question 4**

** What precondition would be used in the weakest possible simple specification? What would a suitable postcondition be?**


**Learning Objectives:** 
+ Gain more experience writing preconditions 
+ Be able to identify preconditions that will prevent errors
+ Be able to identify preconditions that won’t cause a warning in OpenJML but are logically important to the code


**Learning Objectives:** 
+ Understand relationship between pre/postconditions and arrays
+ Introduction to the `\forall` clause
+ Understand the usefulness of using preconditions to check inputs to the code 

## **[Answer Key](PreConExKey.md)**
## **[All exercises](https://www.openjml.org/tutorial/exercises/exercises)**
