---
title: JML Tutorial - Exercises - Assume Statements
---
# Assume Statements Exercises Key:
## [Assume Statements Tutorial](https://www.openjml.org/tutorial/AssumeStatement)

## **Question 1**
**Given the function below, determine the specifications needed to verify the function, as well as including the assume statements where indicated.**
```Java
public int[] reverseArray(int[] a) {
	int len = a.length;
	int[] b = new int[len];

	for (int i = 0; i < a.length; i++) {
		//first assume 
		//second assume
		b[len - 1] = a[i];
		len--;			
	}
	//@ assert b.length == a.length;
	return b;
}
```
**Asnwer and Explanation:**
The function above stores the length of array `a` and creates a new integer array `b`. Then a for-loop runs for `i < a.length`, and within the for-loop `b[len - 1] = a[i]`. This will set the last index of `b` to the first element in `a`. After the value of `b` is set at `len-1`, `len` is decremented by 1. This will cause a lot of warnings if we do not specify that both `i` and `(len-1)` are in the valid range of zero to `a.length`. So we need to include this as an assumption anytime we have a loop and need to ensure that we are not going out of bounds. Note that there are better ways of handling loops which we will see in the "[Specifying Loops](https://www.openjml.org/tutorial/Loops)" tutorial, but for now we will handle loops using the `assume` clause. 
```java
//@ ensures \result.length == a.length;
public int[] reverseArray(int[] a) {
	int len = a.length;
	int[] b = new int[len];

	for (int i = 0; i < a.length; i++) {
		//@ assume 0 <= i < a.length;
		//@ assume 0 <= len-1 < a.length;
		b[len - 1] = a[i];
		len--;			
	}
	//@ assert b.length == a.length;
	return b;
}
```
**Learning Objective:**
The goal of this exercise is to see if the student understands one way that the assume clause can be used at this point in the students' studies. The tutorial on assume statements goes over this use of assumes well, so it should be easy for the student to determine where the assumption clause should be put to ensure that there are no warnings. This also gives the student a taste of what is to come by using loop invariants which will come later. The questions also requires that the student recall past tutorials. 

## **Question 2**
**The following code has an error with finding the max value in an array. Determine how assume can be used to find where in the code the error occurs.**
```Java
//@ requires a != null;
//@ ensures (\forall int k; 0 < k < a.length; a[k-1] <= a[k]);
//@ ensures (\exists int k; 0 < k < a.length; \result >= a[k]);
public int sortFindMax(int[] a) {
	int max;

	for (int i = 0; i < a.length-1; i++) {
		for (int j = i+1; j < a.length; j++) {
			//first assume
			//second assume
			if (a[i] > a[j]) {
				int temp = a[i];
				a[i] = a[j];
				a[j] = temp;
			}
		}
	}
	//third assume 
	//fourth assume
	max = a[a.length-1];
	//fifth assume
	return max;
}
```
**Asnwer and Explanation:**
Given the code above we are tasked with utilizing the `assume` clause to find where in the code the error is - since the function is not finding the correct max value in the array. First, let's break down what the function is doing. The function is first sorting the array using a selection sort, and then sets `max = a[a.length-1]` - since, if the array is properly sorted in ascending order the max value should be in the last position of the array. Notice the pre and post conditions of the function. The function requires that `a != null`, typical when using arrays. However, there are two ensures clauses that use a `\forall` and `\exists` clause, we haven't seen how to use these yet as they will come up later in the "[JML Expressions](https://www.openjml.org/tutorial/Expressions)" tutorial. Essentially, the first ensures statement checks for the range of 0 to `a.length` the array should be sorted after the function call. The second ensures statement checks that there exists a max value in the array for the range 0 to `a.length`.

Now that we understand the code and the pre and postconditions let's start debugging. First, let's include our `assume` statements for the for-loops, since we need to specify that our indices don't go out of bounds when we iterate through. We will place these where is says "first assume" and "second assume" 
```java
//@ requires a != null;
//@ ensures (\forall int k; 0 < k < a.length; a[k-1] <= a[k]);
//@ ensures (\exists int k; 0 < k < a.length; \result >= a[k]);
public int sortFindMax(int[] a) {
	int max;

	for (int i = 0; i < a.length-1; i++) {
		for (int j = 0; j < a.length; j++) {
			//@ assume 0 <= i < a.length;
			//@ assume 0 <= j < a.length;
			if (a[i] > a[j]) {
				int temp = a[i];
				a[i] = a[j];
				a[j] = temp;
			}
		}
	}
	//third assume	
	//@ assume 0 <= a.length-1 < a.length;
	max = a[a.length-1];
	//fifth assume
	return max;
}
```
The current code when ran with OpenJML will warn us that the second ensures statement cannot be verified. So we can use the assume clause to check different parts of our code to narrow down where the error might be. First, let's check the selection sort by using the following assume statement below. We will place this assume statement where it says “third assume.” By placing the assume statement here we are telling OpenJML to assume that our sort works as intended.
```java
//@ requires a != null;
//@ ensures (\forall int k; 0 < k < a.length; a[k-1] <= a[k]);
//@ ensures (\exists int k; 0 < k < a.length; \result >= a[k]);
public int sortFindMax(int[] a) {
	int max;

	for (int i = 0; i < a.length-1; i++) {
		for (int j = 0; j < a.length; j++) {
			//@ assume 0 <= i < a.length;
			//@ assume 0 <= j < a.length;
			if (a[i] > a[j]) {
				int temp = a[i];
				a[i] = a[j];
				a[j] = temp;
			}
		}
	}
	//@ assume (\forall int i; 0 < i < a.length; a[i-1] <= a[i]);
	//@ assume 0 <= a.length-1 < a.length;
	max = a[a.length-1];
	//firth assume
	return max;
}
```
When we run this we still get an error that the second ensures statement cannot be verified. So let's check that our `max` is being set to the correct value by using another `assume` statement placed at “fifth assume.”
```java
//@ requires a != null;
//@ ensures (\forall int k; 0 < k < a.length; a[k-1] <= a[k]);
//@ ensures (\exists int k; 0 < k < a.length; \result >= a[k]);
public int sortFindMax(int[] a) {
	int max;

	for (int i = 0; i < a.length-1; i++) {
		for (int j = 0; j < a.length; j++) {
			//@ assume 0 <= i < a.length;
			//@ assume 0 <= j < a.length;
			if (a[i] > a[j]) {
				int temp = a[i];
				a[i] = a[j];
				a[j] = temp;
			}
		}
	}
	//@ assume (\forall int i; 0 < i < a.length; a[i-1] <= a[i]);
		
	//@ assume 0 <= a.length-1 < a.length;
	max = a[a.length-1];
	//@ assume (\exists int l; 0 < l < a.length; max >= a[l]); 
	return max;
}
```
After including this second `assume` statement our function finally verifies - but we have narrowed down that our error must be within the selection sort. You might have already caught it, but in the selection sort we have `j = 0`, when it needs to be `j = i + 1`. Something like that might be hard to find in an extensive program, so `assume` helps us to cut down the time of debugging. If we fix the code we see that the correct max value is found and the function can be verified. 
```java
//@ requires a != null;
//@ ensures (\forall int k; 0 < k < a.length; a[k-1] <= a[k]);
//@ ensures (\exists int k; 0 < k < a.length; \result >= a[k]);
public int sortFindMax(int[] a) {
	int max;

	for (int i = 0; i < a.length-1; i++) {
		for (int j = i+1; j < a.length; j++) {
			//@ assume 0 <= i < a.length;
			//@ assume 0 <= j < a.length;
			if (a[i] > a[j]) {
				int temp = a[i];
				a[i] = a[j];
				a[j] = temp;
			}
		}
	}
	//@ assume (\forall int i; 0 < i < a.length; a[i-1] <= a[i]);
		
	//@ assume 0 <= a.length-1 < a.length;
	max = a[a.length-1];
	//@ assume (\exists int l; 0 < l < a.length; max >= a[l]); 
	return max;
}
```
**Learning Objective:** 
The goal of this exercise is to check if the student understands how the `assume` clause can be used for debugging. In this example the student is told that the code does not work and we want them to go through and use `assume` to find the error in the code. In doing so the student should see how `assume` makes debugging more efficient. The student will also see how we still need to use `assume` right now to make sure that we don't go out of bounds.

## **Resources:**
+ [Assume Statements Exercises](AssumeEx.md)
+ [Question 1 Java](AssumeExample1.java)
+ [Question 2 Java](AssumeExample2.java)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)