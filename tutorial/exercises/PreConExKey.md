---
title: JML Tutorial - Exercises - Preconditions
---
# Precondition Exercises Key:
## [Preconditions Tutorial](https://www.openjml.org/tutorial/Preconditions)

## **Question 1**
**The function below will update a user's bank account after making a purchase of a certain number of items. We want to make sure that the user's bank account is never below $0.00. What specifications can we implement to ensure that the user's bank account is never negative?**
```Java
public double bankUpdate(double bankAccount, double price, int n) {
	bankAccount = bankAccount - (price*n);
	return bankAccount;
}
```
**Asnwer and Explanation:**
Let's determine what we know; the function takes in three parameters, the current amount in the user's bank account, the price of an item, and the number of items to be purchased. The goal of this function is to update the user's bank account, but also ensure that their bank account does not dip below zero dollars. To ensure that this does not happen we need to check the following: the current amount in the user's bank account is greater to zero; the cost of one item is greater than or equal to zero; and that purchasing n items doesn't make the user's bank account negative. If all these requirements are met, we can ensure that the user's bank account will not be below $0.00. 

However, it is important to note that since we are dealing with floating points (doubles in this case) we need to ensure that the inputs passed into the function are not "not a number" AKA `NaN`. We can use the function `isNan()` of the class Double which checks if the input `bankAccount` or `price` in this case are `NaN`, and then require that the inputs are not `NaN`. By doing this we can avoid potential problems if a user were to pass in a `NaN` value. OpenJML will not check `NaN` inputs on its own, so it is important to include this requirement when working with floating points to avoid potential errors.

We can also include the following postcondition that uses the `\old` clause to check that the result is approximately equal to `balance-(price*n)`. It is safer to say that floating points are approximately equal and not equal to each other. We will talk more indepth about the `\old` clause, but for now just know that we can check that our output is what we expect it to be by using the `\old` clause. 
```Java
//@ requires !Double.isNaN(bankAccount);
//@ requires bankAccount > 0.0;
//@ requires !Double.isNaN(price);
//@ requires price >= 0;
//@ requires (price*n) <= bankAccount;
//@ ensures \result >= 0.0;
public double bankUpdate(double bankAccount, double price, int n) {
	bankAccount = bankAccount - (price*n);
	return bankAccount;
}
```

**Note that the following variations of the pre and postconditions might not cause errors, but it logically fails to meet the goal of the function:**

**Incorrect Version 1:**
```Java
//@ requires balance > 0.0;
//@ requires price >= 0;
//@ requires balance >= price * n;
//@ ensures Double.abs(\result - \old(balance-(price*n))) < 0.001;
//@ ensures \result >= 0.0;
public double balanceUpdate(double balance, double price, int n) {
	balance = balance - (price*n);
	return balance;
}
```
If we don't specify that bankAccount and price are not NaNs this could cause a potential error with the result down the line. As stated above, OpenJML will not check for NaN inputs on its own, so while not including this requirement will not cause a warning - it is important to include this precondition nonetheless to avoid problems down the line. It will also force OpenJML to check that inputs are no NaN if we do include the requirements.

**Incorrect Version 2:**
```Java
//@ requires !Double.isNaN(bankAccount);
//@ requires !Double.isNaN(price);
//@ requires price >= 0;
//@ requires balance >= price * n;
//@ ensures Double.abs(\result - \old(balance-(price*n))) < 0.001;
//@ ensures \result >= 0.0;
public double balanceUpdate(double balance, double price, int n) {
	balance = balance - (price*n);
	return balance;
}
```
If we don't specify that the current amount in the bank account is `>= 0.0` there is no way the user can purchase the items because they do not have the funds for it. Additionally, we say greater than equal to equal to 0.0 because it is valid for the user's bank account to have $0.00.

**Incorrect Version 3:**
```Java
//@ requires !Double.isNaN(bankAccount);
//@ requires balance > 0.0;
//@ requires !Double.isNaN(price);
//@ requires balance >= price * n;
//@ ensures Double.abs(\result - \old(balance-(price*n))) < 0.001;
//@ ensures \result >= 0.0;
public double balanceUpdate(double balance, double price, int n) {
	balance = balance - (price*n);
	return balance;
}
```
If the price of the item is negative, when we attempt to subtract it from the bank account a negative times a negative will create a positive, and will actually add money to the bank account. 

**Incorrect Version 4:**
```Java
//@ requires !Double.isNaN(bankAccount);
//@ requires balance > 0.0;
//@ requires !Double.isNaN(price);
//@ requires price >= 0;
//@ ensures Double.abs(\result - \old(balance-(price*n))) < 0.001;
//@ ensures \result >= 0.0;
public double balanceUpdate(double balance, double price, int n) {
	balance = balance - (price*n);
	return balance;
}
```
This is the only version shown that would cause a warning because price*n could potentially cost more than the user has in their bank account. This could then make the user's `balance < 0.0` which fails to meet the ensured clause that the `result >= 0.0`.

**Learning Objective:**
The goal of this exercise is to test if the student can identify any and all preconditions needed to ensure that the result of the function does not allow the user's bank account to dip below $0.00. We want to make sure that the student understands that OpenJML is not perfect and that we still need to think of all the possible inputs that could be passed in - which is why making use that we check that any floating point variables passed in are not NaN. 

## **Question 2**
**Given an integer array, write a binary search function, and include any specifications needed to verify the function.**

**Asnwer and Explanation:**
We are tasked with creating a binary search function given an integer array. First, what do we know needs to be true for a binary search function? We know that the array passed in must already be sorted, it cannot be empty, and depending what we choose as our parameters, we need to make sure that everything is within the range of zero to the array's length. Let's say that we decide to code the following binary search function:
```Java
public int binarySearch(int[] a, int low, int high, int key) {
	int mid;		
	
	while(low <= high) {
		mid = (low+high)/2;
		if(a[mid] == key)
			return mid;
		if(a[mid] > key)
			high = mid - 1;
		if(a[mid] < key)
			low = mid + 1;
	}
	return -1;
}
```
In the code above we take in four parameters: the array `a`, the `low` index, the `high` index, and `key` - which is what we are looking for. Within the function we create our variable `mid`, followed by a while-loop that runs while `low <= high` - typical of any binary search. Within the while loop we find our `mid` index and assess if the `key` is greater than `a[mid]`, less than `a[mid]`, or `a[mid]`. Finally, we `return -1` if we find that the key is not in the array. 

Now that we understand what is going on, let's start adding our JML specifications. First we need to make sure that the array != null, secondly that `low` and `high` are within the range of `a`, and finally that the array is sorted. We can come up with the first requirements pretty easily, as seen below:
```Java
//@ requires a != null;
//@ requires 0 <= low < a.length;
//@ requires 0 <= high < a.length;
public int binarySearch(int[] a, int low, int high, int key) {
	int mid;		
	
	while(low <= high) {
		mid = (low+high)/2;
		if(a[mid] == key)
			return mid;
		if(a[mid] > key)
			high = mid - 1;
		if(a[mid] < key)
			low = mid + 1;
	}
	return -1;
}
```
Note that in JML objects (including arrays) must not be null, so writing `a != null` is redundant and can be omitted.

However, now we need to make sure that the array `a` is sorted. How do we do this? We need to use the `\forall` clause, which will be discussed in the "[JML Expressions](https://www.openjml.org/tutorial/Expressions)" tutorial. So for now don't worry about the syntax, let's just make sure we understand what the requirement is doing.
```Java
//@ requires a != null;
//@ requires 0 <= low < a.length;
//@ requires 0 <= high < a.length;
//@ requires (\forall int i; 0 < i && i < a.length; a[i-1] <= a[i]);
public int binarySearch(int[] a, int low, int high, int key) {
	int mid;		
	
	while(low <= high) {
		mid = (low+high)/2;
		if(a[mid] == key)
			return mid;
		if(a[mid] > key)
			high = mid - 1;
		if(a[mid] < key)
			low = mid + 1;
	}
	return -1;
}
```
The last requirement is simply checking that that the array is sorted. The `\forall` clause acts as a for-loop in JML, and can be very useful when we want to ensure that something is true for a range of values. In this case the `\forall` clause is checking that the array is sorted for `i` greater than zero and less than `a.length`. We also need to include some assume statements within the while-loop to make sure that `a[mid]` is not out of bounds of the array. We will study the assume clause in more depth in the "[Assume Statements](https://www.openjml.org/tutorial/AssumeStatement)" tutorial. For now, just know that the code above will cause error unless the assume statement is included as seen below:
```Java
//@ requires a != null;
//@ requires 0 <= low < a.length;
//@ requires 0 <= high < a.length;
//@ requires (\forall int i; 0 < i && i < a.length; a[i-1] <= a[i]);
public int binarySearch(int[] a, int low, int high, int key) {
	int mid;		
	
	while(low <= high) {
		//@ assume 0 <= (low+high) < a.length;
		mid = (low+high)/2;
		if(a[mid] == key)
			return mid;
		if(a[mid] > key)
			high = mid - 1;
		if(a[mid] < key)
			low = mid + 1;
	}
	return -1;
}
```
**Learning Objective:**
The goal of this exercise is to test if the user understands how requirements might be used with arrays since there are some very important preconditions we have to consider. Depending how the student chooses to write their binary search will determine what their requirements look like; however, they should understand that while the syntax of the precondition statements might alter from program to program it is still vital that the preconditions are included. For example, if the student were to only pass in the array and the key, they should still include a precondition that ensures that the length of the array is not outside the range of the type int. Students should also know to check that the array is not empty regardless of how they code their binary search. It also introduces some new concepts like the `\forall` clause which we do not expect the student to understand fully - but we want them to understand how requirements can be used to ensure that the function they wrote performs properly. In this case the student should be able to recognize that a binary search *requires* that the array we are searching through is already sorted. This allows the students to know without a doubt that the program will throw an exception if this is not met and will allow them to spend less time sifting through results that don't make sense.

## **Resources:**
+ [Precondition Exercises](PreConEx.md)
+ [Question 1 Java](PreconditionExample1.java)
+ [Question 2 Java](PreconditionExample2.java)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)
