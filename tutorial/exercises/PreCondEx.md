---
title: JML Tutorial - Exercises - Preconditions
---
# Precondition Exercises:
## [Preconditions Tutorial](https://www.openjml.org/tutorial/Preconditions)

## **Question 1**
**What precondition would be needed for the following code in the method below to verify? If you can simplify your precondition while still making the code verify, do that.**

```Java
    public int element0(int a[]) {
        return a[0];   // ERROR: a[0] may not be defined!
    }
```

## **Question 2**

**The method below will return a user's balance after making a purchase of a certain number of items.
The goal of this method is to return the new balance
and also ensure that their balance does not dip below zero or increase (as specified in the assertion).
What preconditions will ensure that the assertion always passes? (Although it may be best not to use doubles for amounts of money, this example does illustrate a point about preconditions and doubles that is more generally applicable.)**

```Java
    public double purchase(double balance, double price, int n) {
        double oldBalance = balance;
	balance = balance - (price*n);
        //@ assert 0.0 <= balance <= oldBalance;   // ERROR: may fail!
	return balance;
    }
```

## **Question 3**

**What precondition would be used in the strongest possible simple specification? What would a suitable be postcondition be?**

## **Question 4**

**What precondition would be used in the weakest possible simple specification? What would a suitable postcondition be?**

**Learning Objectives:** 
+ Gain more experience writing preconditions 
+ Be able to identify preconditions that will prevent errors
+ Be able to identify preconditions that won’t cause a warning in OpenJML but are logically important to the code

## **[Answer Key](PreCondExKey.md)**

## Resources
+ [Java code for question 1](PreCondEx1.java)
+ [Java code for question 2](PreCondEx2.java)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)
