---
title: JML Tutorial - Exercises - Verifying Method Calls
---
# Verifying Method Calls Exercises:
## **Question 1**
**Write two functions that perform the following: an function that adds two integer arrays and a function that returns true if the arrays to be added are of the same size. Use the following function headers to help you. Determine the specifications needed to verify your functions.**
```Java
public int[] addArrays(int[] a, int[] b);

public boolean sameSize(int[] a, int[] b);
```
**Asnwer and Explanation:**
We are tasked with writing a program that adds two integer arrays, we will break up this process into two functions. The `addArrays()` will take in two integer arrays `a` and `b` and will add their elements if they are the same size. The `sameSize()` will also take in the arrays `a` and `b` and check if they have the same length. Given this information we can write something like the following program:
```Java
public int[] addArrays(int[] a, int[] b) {
	if(sameSize(a, b)) {
		int[] newArr = new int[a.length];
		for(int i = 0; i < a.length; i++) {
        		newArr[i] = a[i] + b[i];
		}	
		return newArr;
	}
	return new int[0];
}

public boolean sameSize(int[] a, int[] b) {
	return a.length == b.length;
}
```
The `addArrays()` function calls `sameSize()`, and if `a.length == b.length` a new integer array `newArr` is created of size `a.length`. Note, that it could also be of the size `b.length`, it doesn’t really matter since we have determined at this point they are the same size. After creating `newArr` there is a for-loop that runs for the length of `a` and will store `a[i] + b[i]` at `newArr[i]`. If `a` and `b` are NOT the same size the function will return an empty integer array which is written as `new int[0]`. The `sameSize()` function simply returns the result of checking if `a.length == b.length`, that is to say it will return true if `a` and `b` are the same length, and false otherwise. 
 
Now that we have written the code, what preconditions and postconditions should be included? Well, first let’s write any JML specifications for `sameSize()` as it is a more straightforward function. For `sameSize()` we can ensure that the result will always be equivalent to whether `a.length == b.length` (i.e true or false). So we might write something like the following for `sameSize()`
```Java
public int[] addArrays(int[] a, int[] b) {		
	if(sameSize(a, b)) {
		int[] newArr = new int[a.length];
		for(int i = 0; i < a.length; i++) {
			newArr[i] = a[i] + b[i];
		}	
		return newArr;
	}
	return new int[0];
}
//@ ensures \result <==> (a.length == b.length);
public boolean sameSize(int[] a, int[] b) {
	return a.length == b.length;
}

```
As for the `addArrays()` function let’s think about what preconditions we might want to require; we are adding the elements from `a` and `b` and any time we are dealing with integer arithmetic we want to make sure we remain in the size of type `int`. So we can use the `forall` clause to check that `a[i] + b[i] <= Integer.MAX_VALUE`. Additionally, since the function will return an empty array if `a` and `b` aren’t the same size we can ensure two things to be true. The `\result` will have the length equal to that of either array `a` or `b`. Secondly, if `a` and `b` aren’t the same length then `\result` will be empty and have the length of zero. 

Note:  We can write more complex `ensures` clauses that would actually check if the function `addArrays()` returns an array whose elements are equal to that of `a[i] + b[i]`, but that would require the use of loop invariant which we will get into in the [“Specifying Loops”](https://www.openjml.org/tutorial/Loops) tutorial. Additionally, as we move on you will see better ways of handling exceptions and different method behaviors, but for now we can write something like the following:  
```Java
//@ requires (\forall int j; 0 <= j < a.length; a[j]+b[j] <= Integer.MAX_VALUE);
//@ ensures \result.length == a.length || \result.length == 0;
//@ pure
public int[] addArrays(int[] a, int[] b) {		
	if(sameSize(a, b)) {
		int[] newArr = new int[a.length];
		for(int i = 0; i < a.length; i++) {
			newArr[i] = a[i] + b[i];
		}
		return newArr;
	}
	return new int[0];
}
	
//@ ensures \result <==> (a.length == b.length);
public boolean sameSize(int[] a, int[] b) {
	return a.length == b.length;
}
```
Now, since we are dealing with a for-loop we also have to include an assume statement so we don’t run into any issues going out-of-bounds. Additionally, since we're adding `a[i] + b[i]` we need to account for potential overflow errors like we did in our precondition, so let's also include an assume statement that handles this. 
```Java
//@ requires (\forall int j; 0 <= j < a.length; a[j]+b[j] <= Integer.MAX_VALUE);
//@ ensures \result.length == a.length || \result.length == 0;
//@ pure
public int[] addArrays(int[] a, int[] b) {		
	if(sameSize(a, b)) {
		int[] newArr = new int[a.length];
		for(int i = 0; i < a.length; i++) {
			//@ assume 0 <= i < a.length;
			//@ assume Integer.MIN_VALUE < a[i] + b[i] <= Integer.MAX_VALUE;
			newArr[i] = a[i] + b[i];
		}
		return newArr;
	}
	return new int[0];
}

//@ ensures \result <==> (a.length == b.length);
public boolean sameSize(int[] a, int[] b) {
	return a.length == b.length;
}
```
 Now that we have included everything from past tutorials, what new specifications do we need after reading "Method Calls?" Recall how a method call is verified; at the call site assert the precondition of the called method, and then assume the callee's postconditions. In our program we only have one preconditions for the caller function `addArrays()` which we’ve already accounted for, and one postcondition for the callee function `sameSize()`. So we can write the following:
```Java
//@ requires (\forall int j; 0 <= j < a.length; a[j]+b[j] <= Integer.MAX_VALUE);
//@ ensures \result.length == a.length || \result.length == 0;
//@ pure
public int[] addArrays(int[] a, int[] b) {	
	if(sameSize(a, b)) {
		//@ assert sameSize(a, b);
		int[] newArr = new int[a.length];
		for(int i = 0; i < a.length; i++) {
			//@ assume 0 <= i < a.length;
			//@ assume Integer.MIN_VALUE < a[i] + b[i] <= Integer.MAX_VALUE;
			newArr[i] = a[i] + b[i];
		}
		return newArr;
	}
	return new int[0];
}

//@ ensures \result <==> (a.length == b.length);
public boolean sameSize(int[] a, int[] b) {
	return a.length == b.length;
}
```

**Learning Objective:** 
The goal of this exercise is to see if the student understands how to verify method calls. This is a rather simple example, so the student should be able to identify the statements needed to verify functions. The exercise also checks that the student understands and can utilize information from past exercises as well. It also checks if the student can also identify all specifications needed - not just those used for verifying method calls.

## **Question 2**
**The program below is checking whether the user has enough material for an area given the dimensions of the area and the amount of material the user has. However, the program is unable to be verified; determine where in the specifications it is failing, and fix it.**
```Java
//@ ensures \result <==> (area(w, h) > materialSqFt);
public boolean enoughMaterial(int materialSqFt, int w, int h) {
	int area = area(w, h);
		
	return (area > materialSqFt);	
}
	
//@ ensures \result > 0;
//@ ensures \result >= w;
//@ ensures \result >= h;
//@ pure
public int area(int w, int h) {
	int A = w*h;

	return A;	
}
```
**Asnwer and Explanation:**
The program above is unable to be verified with its current specifications, let's break it down and see where the issues lie. The first function `enoughMaterial()` takes in three integer variables `materialSqFt`, `w`, and `h`. It then creates an integer `area` which is set equal to the function `area(w,h)`. If we drop down to the `area()` function we see that the code is the same as we've seen in past exercises, and simply finds the rectangular area given `w` and `h` and returns it. After `area(w,h)` is called in `enoughMaterial()`, the function checks if the `area > materialSqFt`. In the event that `area > materialSqFt` it returns false, otherwise it returns true. 
 
First, we can see that there will be an overflow error in the function `area()` unless we include a precondition that checks that `0 <= w <= Integer.MAX_VALUE` and `0 <= b <= Integer.MAX_VALUE`. Otherwise, all our preconditions and postconditions for the two functions look good. 

However, since `enoughMaterial()` calls `area()` we need to include some `assume` and `assert` statements to verify the two methods. Again we know the process for any function is 
at the call site assert the precondition of the called method, and then assume the callee's postconditions. So what might we include in the program above?
 
Let's start in the function `area()`; after we include that `w` and `h` need to be greater than zero, and less than or equal `Integer.MAX_VALUE`, we would need to assume this in the function. We would also want to assume that `w*h <= Integer.MAX_VALUE` so we don't get any overflow errors. After the body of the function and before the return statement, we want to include an `assert` statement that asserts our area postconditions. Now, back to the `enoughMaterial()` function, in this function we want to `assume` it's preconditions, and `assert` it's postconditions. However, before we call `area()` we want to assert `area()`'s precondtions, and then `assume` it's postconditions after the call. So we can write something like this to verify the program:
```Java
//@ requires materialSqFt > 0;
//@ requires 0 < w <= Integer.MAX_VALUE & 0 < h <= Integer.MAX_VALUE;
//@ ensures \result <==> (area(w, h) > materialSqFt);
public boolean enoughMaterial(int materialSqFt, int w, int h) {
	//@ assume materialSqFt > 0 && 0 < w <= Integer.MAX_VALUE & 0 < h <= Integer.MAX_VALUE;
	
	//@ assert 0 < w <= Integer.MAX_VALUE && 0 < h <= Integer.MAX_VALUE;
	int area = area(w, h);
	
	//@ assume area > 0 && area >= w && area >= h;
	
	//@ assert (area > materialSqFt);
	return (area > materialSqFt);	
}
	
//@ requires 0 < w <= Integer.MAX_VALUE & 0 < h <= Integer.MAX_VALUE;
//@ ensures \result > 0;
//@ ensures \result >= w;
//@ ensures \result >= h;
//@ pure
public int area(int w, int h) {
	//@ assume 0 < w <= Integer.MAX_VALUE & 0 < h <= Integer.MAX_VALUE;
	//@ assume w*h <= Integer.MAX_VALUE;
	int A = w*h;
	
	//@ assert A > 0 && A >= w && A >= h;
	return A;	
}	
```
**Learning Objective:** 
The goal of this exercise is to show the student the necessity of verifying method calls. This exercise is much more complex than the first exercise, and shows that the program cannot be verified without out `assume` and `assert` statements of the pre and postconditions. We want the student to get more comfortable with the process of verifying method calls, and understand it follows the same process every time.

## **Resources:**
+ [Verifying Method Calls Exercises](VerifyingMethodCallsEx.md)
+ [Question 1 Java](MethodCallsExample1.java)
+ [Question 2 Java](MethodCallsExample2.java)
