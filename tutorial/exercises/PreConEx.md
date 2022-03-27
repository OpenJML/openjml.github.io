---
title: JML Tutorial - Exercises - ...
---
<i>Last Modified: <script type="text/javascript"> document.write(new Date(document.lastModified).toUTCString())</script></i>

# Precondition Exercises:
## **Question 1**
**The function below will update a user's bank account after making a purchase of a certain number of items. We want to make sure that the user's bank account is never below $0.00. What specifications can we implement to ensure that the user's bank account is never negative?**
```Java
public double bankUpdate(double bankAccount, double price, int n) {
		bankAccount = bankAccount - (price*n);
		return bankAccount;
}
```
## **Question 2**
**Given an integer array, write a binary search function, and include any specifications needed to verify the function.**

## **[Key](PreConExKey.md)**
