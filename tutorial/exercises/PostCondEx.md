---
title: JML Tutorial - Exercises - Postconditions
---
# Postcondition Exercises:
## [Postconditions Tutorial](https://www.openjml.org/tutorial/Postconditions)

## **Question 1**
**(a) Suppose that we want to change the precondition of the method `multiplyByTwo` below so that the argument (`num`) only has to be (strictly) greater than -1, that is the precondition would be `-1 < num < 100.
Why would this cause a verification error with the existing code?

```Java
//@ requires 0 < num < 100;
//@ ensures \result > num;
 public int multiplyByTwo(int num) {
	return num*2;
}
```

**(b) How you could fix the postcondition so that the existing code would verify with the precondition `-1 < num < 100`? Note that you are to only change the postcondition, not the code in the body of the method and you are to use the new precondition `-1 < num < 100`.**

**(c) Suppose we revert to the original specifications where the precondition is that `0 < num`. The function is unable to be verified. Determine where in the specifications it is failing, and fix it by (only) changing the specification.**

**(c) Suppose the code was updated to the following, with the original precondition that `0 < num`. What is the strongest postcondition that will allow the code in the body below to be verified?**
```Java
public int divideByTwo(int num) {
       return num/2;
}
```
**On the subject of "strongest" specifications:**
First let’s discuss the strength of predicates and specifications.
Suppose predicate P implies Q, then P is the _strong_ predicate and Q is the weaker one, so P is _stronger than_ Q. For example, `x > 1` implies `x > 0`, so `x > 1` is stronger than `x > 0`.
So the _strongest predicate_ is one that implies all others. 

Simple specifications have just a precondition and a postcondition.
Let us write (P,Q) for a simple specification with precondition P and postcondition Q.

A specification (P,Q) is _stronger than_ a specification (P',Q') when it prohibits some implementations (does not verify) some implementations that would be correct for (P',Q'). Thus, (P,Q) is _stronger than_ (P',Q') when P' is stronger than P and Q is stronger than Q', so the stronger specification works in more cases (as it has a weaker precondition), but delivers a result that will always satisfy Q'. In the literature, it is often said that (P,Q) _refines_ (P',Q') when P' implies P and Q implies Q'.

## ** Question 2**

** What precondition would be used in the strongest possible simple specification? What would a suitable be postcondition be?**

## ** Question 3**

** What precondition would be used in the weakest possible simple specification? What would a suitable postcondition be?**

**Learning Objectives:** 
+ Introduction to “strongest” specification 
+ Understand overflow errors
+ Understand relationship between pre and post conditions 

## **Question 4**
** (a) Given a rectangle of width w and height h, write a Java method that finds the area of the rectangle and returns it. (b) What is the strongest specifications that verifies the code you wrote?
The function header is given below.**
```Java 
public int area(int w, int h);
```
**Learning Objectives:** 
+ Gain more experience writhing pre and postconditions 
+ Understand the importance of postconditions and how they can be used to get the correct output for a program

## **[Answer Key](PostCondExKey.md)**

