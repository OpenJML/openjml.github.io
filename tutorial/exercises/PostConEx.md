---
title: JML Tutorial - Exercises - ...
---
<i>Last Modified: <script type="text/javascript"> document.write(new Date(document.lastModified).toUTCString())</script></i>

# Postcondition Exercises:
## **Question 1**
**(a) The function given below is unable to be verified; determine where in the specifications it is failing, and fix it.**
```Java
//@ requires num > 0;
//@ ensures \result > num;
 public int multiplyByTwo(int num) {
	return num*2;
}
```
**(b) Suppose that the specifications for num were updated so that it only has to be greater than -1.  Determine why this would cause an error, and how you could fix the remaining specifications to verify the function.**

**(c) Suppose the code was updated to the following, and num must be a positive number. Determine the specifications needed to verify the function.**
```Java
 public int multiplyByTwo(int num) {
	return num/2;
}
```
## **Question 2**
**Given a rectangle of width w and height h, write a function that finds the area of the rectangle and returns it. Determine the specifications needed to verify the function. (Assume width and height are whole numbers)**

