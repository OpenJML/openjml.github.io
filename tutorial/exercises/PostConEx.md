---
title: JML Tutorial - Exercises - Postconditions
---
# Postcondition Exercises:
##**[Postconditions Tutorial](https://www.openjml.org/tutorial/Postconditions)**

## **Question 1**
**(a) Suppose that the function below had its specifications changed for num, where num is updated so that it only has to be greater than -1. Determine why this would cause an error, and how you could fix the remaining specifications to verify the function.**
```Java
//@ requires 0 < num < 100;
//@ ensures \result > num;
 public int multiplyByTwo(int num) {
	return num*2;
}
```
**(b) Suppose we revert to the orignal specifications where num > 0. The function is unable to be verified. Determine where in the specifications it is failing, and fix it.**

**(c) Suppose the code was updated to the following, and num must be a positive number. Determine the specifications needed to verify the function.**
```Java
 public int multiplyByTwo(int num) {
	return num/2;
}
```
**On the subject of "strongest" specifications:**
First let’s discuss what a strong predicate is. For the formula P implies Q, in this situation P is the strong preciate and Q is the weaker one. So when we say “strongest predicate” we are talking about the predicate that implies the other. For example, let’s think about the predicate that x > 1 implies x > 0, in this case the first predicate implies that x will always be greater than 5 which is greater than 0 - therefore it is true. 

Therefore, when asking for the “strongest” specifications we want a strong precondition that implies the postcondition. One way to determine the stronger predicates is to find the specific inputs and outputs we want.. This allows for fewer implementations.  

To read more about the subject check out the [following](https://www.cs.scranton.edu/~mccloske/courses/se504/predicate_strength.pdf)

**Learning Objectives:** 
+ Introduction to “strongest” specification 
+ Understand overflow errors
+ Understand relationship between pre and post conditions 

## **Question 2**
**Given a rectangle of width w and height h, write a function that finds the area of the rectangle and returns it. Determine the strongest specifications needed to verify the function. The function header is given below.**
```Java 
public int area(int w, int h);
```
**Learning Objectives:** 
+ Gain more experience writhing pre and postconditions 
+ Understand the importance of postconditions and how they can be used to get the correct output for a program

## **[Answer Key](PostConExKey.md)**
## **[All exercises](https://www.openjml.org/tutorial/exercises/exercises)**