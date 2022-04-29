---
title: JML Tutorial - Exercises - Assume Statements
---
# Assume Statements Exercises:
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
**Learning Objectives:** 
+ Understand how `assume` can be used for loops
+ Understand there are better ways of dealing with loops 

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
**Learning Objectives:** 
+ Understand how `assume` can be used for debugging 
+ Understand the relationship between `assume` and `assert`
+ Understand the differences between `assume` and `assert`

## **[Answer Key](AssumeExKey.md)**

