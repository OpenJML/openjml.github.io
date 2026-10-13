---
title: JML Tutorial - Exercises - JML Expressions
---
# JML Expressions Exercises:
## [JML Expressions Tutorial](https://www.openjml.org/tutorial/Expressions)

## **Question 1**
**Look again at the `primeChecker` method below. This method checks if its argument is prime. Using a quantified expression, either `\exists` or `\forall`, write an expression in the assertion at the end that describes the property that there are no integers between 2 and `num/2` inclusive that evenly divide the argument `num`.**
```Java
public boolean primeChecker(int num) {
        //@ assume 0 < num;
	boolean isPrime = true;
        int i;
	for (i = 2; i < num/2; i++) {
                //@ assume isPrime && 2 <= i < num/2;
                //@ assume !(\exists int j; 2 <= j < i; num % j == 0);
		if (num % i == 0) {
			//@ assert num % i == 0;
			isPrime = false;
			return isPrime;
		}
                //@ assert isPrime && 2 <= i < num/2;
                //@ assert !(\exists int j; 2 <= j < i; num % j == 0);
	}
        //@ assume isPrime && 2 <= i && i == num/2;
        //@ assert !(\exists int j; 2 <= j < i; num % j == 0);
        if (num % i == 0) {
            isPrime = false;
            return isPrime;
        }
        //@ assert isPrime;
        // write an assert statement here about num
	return isPrime;
}
```

The predicate in the assert statement at the end that describes `num` could be adapted to be used as a [postcondition](https://openjml.org/tutorial/Postconditions.html) for the method.

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

## **[Answer Key](JmlExprExKey.md)**
## **[All exercises](https://www.openjml.org/tutorial/exercises/exercises)**

## Resources
+ [Java code for question 1](JmlExprExample1.java)
+ [Java code for question 2](JmlExprExample2.java)
