---
title: JML Tutorial - Exercises - JML Expressions
---
# JML Expressions Exercises:
##**[JML Expressions Tutorial](https://www.openjml.org/tutorial/Expressions)**

## **Question 1**
**Take a look at the following function that checks if the number passed is prime. We've seen this code before, but now that you've read about JML Expressions, what can now be ensured about the function?**
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
Modus Ponens is a rule of inference, which states that if p is true, and p implies q, then q is true. Take a look at the truth table below. 
![Modus Ponens Truth Table](https://www.google.com/url?sa=i&url=https%3A%2F%2Fwww.quora.com%2FIs-Modus-Ponens-invalid&psig=AOvVaw27iAOGt0mZ8Pgp9V_YfYvr&ust=1651362963140000&source=images&cd=vfe&ved=0CAwQjRxqFwoTCNCBhMy8uvcCFQAAAAAdAAAAABAD)

**Learning Objectives:**
+ Gain more experience using JML operators
+ Understand how the same JML statements can be used for different versions of the same code
+ Recall "strongest" specifications

## **[Answer Key](JmlExprExKey.md)**
## **[All exercises](https://www.openjml.org/tutorial/exercises/exercises)**