---
title: JML Tutorial - Exercises - JML Expressions
---
# JML Expressions Exercises:
## [JML Expressions Tutorial](https://www.openjml.org/tutorial/Expressions)

## **Question 1**
**Look again at the `primeChecker` method below. This method checks if its argument is prime. Using a quantified expression, either `\exists` or `\forall`, write an expression that says that `\result` is true just when there are no integers between 2 and `num/2` inclusive that evenly divide the argument `num`. (This expression could be used as a [postcondition](https://openjml.org/tutorial/Postconditions.html) for the method.)**
```Java
//@ requires num > 0;
public boolean primeChecker(int num) {
	boolean flag;
	for (int i = 2; i <= num / 2; i++) {
		//@ assume i > 0;
		if (num % i == 0) {
			flag = false;
			//@ assert num % i == 0;
			//@ assert flag == false;
			return flag;
		}
	}

	flag = true;
	//@ assert flag == true;
	return flag;
}
```
**Learning Objectives:**
+ Understand quantified expressions and be able to write them
+ Understand JML operators and be able to utilize them

## **Question 2**
**Write a function that simulates the truth table for the Discrete Mathematical inference rule of Modus Ponens, use the function header given below to construct your function. Determine the specifications needed to verify your function.**
```Java
public boolean modusPonens(boolean p, boolean q);
```
**On the subject of Modus Ponens:**
Modus Ponens is a rule of inference, which states that if p is true, and p implies q is true, then q is true. This is shown in the truth table below.

```
P      	Q    |	P ==> Q	| P && (P ==> Q) | (P && (P ==> Q)) ==> Q
=================================================================
T	T    |	   T	|      T         |           T
------------------------|----------------|-----------------------
T      	F    | 	   F   	|      F	 |
------------------------|----------------|-----------------------
T	T    |	   T	|      T         |           T
------------------------|----------------|-----------------------
T	F    |	   F	|      F         |
------------------------=----------------------------------------
```


**Learning Objectives:**
+ Gain more experience using JML operators
+ Understand how the same JML statements can be used for different versions of the same code
+ Recall "strongest" specifications

## **[Answer Key](JmlExprExKey.md)**
## **[All exercises](https://www.openjml.org/tutorial/exercises/exercises)**
