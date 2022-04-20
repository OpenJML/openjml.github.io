---
title: JML Tutorial - Exercises - Postcondition
---
# Postcondition Exercises:
## **Question 1**
**(a) Suppose that the function below had its specifications changed for num, where num is updated so that it only has to be greater than -1. Determine why this would cause an error, and how you could fix the remaining specifications to verify the function. Note that num cannot be greater than 100 for this problem.**
```Java
//@ requires num > 0;
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
Let's think about the formula P implies Q. When we say the "strongest" postcondition, we want to find the state that P is stronger so that Q is true. We might say that the function above implies "true," but this would be the weakest postcondition - as it is not that specific. So we want to be as specific as possible when writing specifications. This allows for fewer implementations.  

## **Question 2**
**Given a rectangle of width w and height h, write a function that finds the area of the rectangle and returns it. Determine the specifications needed to verify the function. The function header is given below.**
```Java 
public int area(int w, int h){

}
```
## **[Key](PostConExKey.md)**