---
title: JML Tutorial - Exercises - Assert Statements
---
# Assert Statements Exercises:
## **Question 1**
**Given the code below determine the any specifications needed to verify the function, as well as the assert statements where indicated.**
```Java
public void max(int a, int b, int c) {
	int max;
	
	if(a >= b && a >= c) {
		max = a;
	//first assert
	}else if(b >= a && b >= c) {
		max = b;
	//second assert
	}else {
		max = c;
	}				
	//third assert
}
```
**Learning Objective:** 
+ Understand how `assert` can be used
+ Understand the relationship between `assert` statements and postconditions 

## **Question 2**
**Given the function below, write the strongest assert statements that will pass at the places indicated.**
```Java
//@ requires num > 0;
public boolean primeChecker(int num) {
	boolean isPrime;
	for (int i = 2; i <= num / 2; i++) {
		//@ assume i > 0;
		if (num % i == 0) {
			//first assertion here
			isPrime = false;
			//second assertion here 
			return isPrime;
		}
	}
	
	isPrime = true;
	//third assertion here
	return isPrime;
}
```
**Learning Objective:** 
+ Gain more experience writing `assert` statements

## **[Answer Key](AssertExKey.md)**
