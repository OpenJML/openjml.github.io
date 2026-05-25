---
title: JML Tutorial - Exercises - Preconditions
---
# Precondition Exercises:
## [Preconditions Tutorial](https://www.openjml.org/tutorial/Preconditions)

## **Question 1**
**What precondition would be needed for the following code in the method below to verify? If you can simplify your precondition while still making the code verify, do that.**

```Java
//@ ensures \result == a[0];
public int element0(int a[]) {
   return a[0];
}
```

## **Question 2**

**The function below will update a user's bank account after making a purchase of a certain number of items.
The goal of this function is to return the new balance in the user's account,
but also ensure that their bank account does not dip below zero dollars (as specified in the ensures clause).
What specifications can we write to ensure that the result is never negative?**

```Java
//@ ensures \result >= 0.0;
public double bankUpdate(double bankAccount, double price, int n) {
		bankAccount = bankAccount - (price*n);
		return bankAccount;
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

## **[Answer Key](PreCondExKey.md)**
## **[All exercises](https://www.openjml.org/tutorial/exercises/exercises)**
