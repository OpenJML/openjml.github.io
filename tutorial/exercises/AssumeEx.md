---
title: JML Tutorial - Exercises - ...
---
<i>Last Modified: <script type="text/javascript"> document.write(new Date(document.lastModified).toUTCString())</script></i>

# Assume Statements Exercises:
## **Question 1**
**Write a function that takes in an integer array a and returns an array that is the reversal of a. Determine the specifications needed to verify the function.**

## **Question 2**
**The following code has an error with finding the max value in an array. Determine how assume can be used to find where in the code the error occurs.**
```Java
//@ requires a != null;
//@ ensures (\forall int k; 0 < k < a.length; a[k-1] <= a[k]);
//@ ensures (\exists int k; 0 < k < a.length; \result >= a[k]);
public int sortFindMax(int[] a) {
	int max;

	for (int i = 0; i < a.length-1; i++) {
		for (int j = 0; j < a.length; j++) {
			if (a[i] > a[j]) {
				int temp = a[i];
				a[i] = a[j];
				a[j] = temp;
			}
		}
	}
		
	max = a[a.length-1];
	return max;
}
```
## **[Key](AssumeExKey.md)**

