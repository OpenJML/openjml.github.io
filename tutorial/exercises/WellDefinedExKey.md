---
title: JML Tutorial - Exercises - Well-defined Expressions
---
# Well-defined Expressions Exercises Key:
## **Question 1**
**The function given below is unable to be verified; determine where in the specifications it is failing, and fix it. Explain why the current specifications are not well-defined.**
```Java
//@ ensures (\exists int i; 0 <= i < a.length; a[i] == key);
public int search(int[] a, int key) {
	int i;
  	for(i = 0; i < a.length; i++) {
		//@ assume 0 <= i < a.length;
		if(a[i] == key) { 
			return i;	
		}
	}
	//@ assert a[i] == key;
	return -1;
}
```
**Asnwer and Explanation:**
First let's see if we understand what the function is doing; the function takes in an integer array `a` and an integer `key`, and goes through the array iteratively and finds the index of `key` in the array. If `key` is not found in the array the function returns -1 so the user knows it wasn't found. With that being said, you might be able to see where the issue lies with our current `ensures` and `assert` statements. What happens if the key is not found in the array? If the key isn't found we return -1 so we cannot `ensure` that there exists an index `i` where `a[i] == key`, by that same logic we cannot assert that `a[i] == key`. However, that isn't to say that we can't `ensure` or `assert` these cases, but we need to be strategic where we put them and account for all possible outcomes.
 
Additionally, there are still more issues with the JML statements. What do we know needs to be included to make sure that we do not go out of bounds of the array when we iterate through it? We need to include an `assume` statement that assumes `i` is less than the length of the array, and greater than or equal to 0. Remember that OpenJML will test all possible paths in the method, that is to say that it tries all possible inputs that conform to the preconditions. And in this case we have no preconditions which is also an issue. We should make sure that the function requires an array that is not empty otherwise it will run into problems. So we could write something like the following to ensure that our JML statements are well defined.
```Java
//@ requires a != null;
//@ ensures (\exists int i; 0 <= i < a.length; a[i] == key) || \result == -1;
public int search(int[] a, int key) {
	int i;
	for(i = 0; i < a.length; i++) {
		//@ assume 0 <= i < a.length;
		if(a[i] == key) { 
			//@ assert a[i] == key;
			return i;	
		}
	}
 	return -1;
}
```
**Learning Objective:** 
The goal of this exercise is to see if the student understands why the current JML statements are not well-defined, and therefore cannot verify the function. This exercise takes everything the student has learned so far and asks them to use it in practice and write their own well-defined statements that verify the function. We also want to check if the student understands that not all statements are wrong just because OpenJML throws a warning, it might be throwing a warning because the statement is put in the wrong place where OpenJML cannot verify the statement. In this example we see that `//@ assert a[i] == key` is not necessarily wrong, but where it is currently placed in the code, OpenJML cannot make this assertion because `i` would be equal to `a.length`, and therefore out of range and really just means that key isn't in the array.

## **Resources:**
+ [Well-defined Expressions Exercises](WellDefinedEx.md)
+ [Question 1 Java](WellDefinedExample1.java)

