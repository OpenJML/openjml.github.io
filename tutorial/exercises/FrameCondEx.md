---
title: JML Tutorial - Exercises - Frame Condtions 
---
# Frame Condtions Exercises:
## **Question 1**
**The program below checks if two integer arrays are the same size and if they are it adds them. However, the code is unable to be verified; determine what specifications are needed to verify the program.**
```Java
//first frame condition
public void addArrays(int[] a, int[] b) {	
	if(sameSize(a, b)) {
		int[] temp = a;
		for(int i = 0; i < a.length; i++) {
			a[i] = temp[i] + b[i];
		}	
	}
}

//second frame condition 		
public boolean sameSize(int[] a, int[] b) {
	return a.length == b.length;
}
```
**Learning Objectives:**
+ Understand how to write frame conditions 
+ Understand the `assigns` clause
+ Introduction to `pure` functions 

## **Question 2**
**Write a function that increases the size of an integer array that is a global variable to the class. Assume the function you write is void and takes in an integer increase that is used to determine how much to increase the original array by. Determine the strongest specifications needed to verify your function.**
```Java
public class FrameCondExample2 {
	//@ spec_public
	private int[] arr = new int[10];

  	public void increase(int increase);
}
```
**Note:** The `FrameCondExample2` class is included purely to satisfy Java's syntactic requirement that all methods be in a class.

**Learning Objectives:**
+ Gain more experience writing frame conditions and using the `assaigns` clause
+ Understand how to use the `\old` designator 
+ Understand the importance of denoting when memory locations have been modified
+ Be able to identify the “strongest” specifications

## **[Answer Key](FrameCondExKey.md)**
