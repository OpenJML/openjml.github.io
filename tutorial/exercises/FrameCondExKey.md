---
title: JML Tutorial - Exercises - Frame Condtions 
---
# Frame Condtions Exercises Key:
## [Frame Conditions Tutorial](https://www.openjml.org/tutorial/FrameConditions)

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
**Asnwer and Explanation:**
The program adds two integer arrays, but breaks up this process by checking is they are the same size and then adds them if they are. We have seen this code in previous [exercises](VerifyingMethodCallsEx.md), but there have been some alterations to it. Notice that we are no longer returning anything from the `addArrays()` function, instead the code simply alters the array `a` passed in as an argument. 

That being said we know after reading the tutorial on "Frame Conditions" that we will have to specify what memory locations the method `addArrays()` may have modified. We can achieve this by using the `assigns` clause. What memory do we know is being alter by the `addArrays()` function? Integer array `a`, so we want to write something that denotes that the elements of `a` are being changed. Additionally, we see that the sameSize function modifies no memory locations, but we can still use the `assigns` clause to specify this by saying that the function `assigns` nothing. Note, that we can also say that `sameSize()` is pure - which also means no memory locations are being changed, but for this exercise we will show both the `assigns` clause and the `pure` clause. That being said we can write the two following frame conditions:
```Java
//@ requires sameSize(a, b);
	//@ requires (\forall int j; 0 <= j < a.length; a[j]+b[j] <= Integer.MAX_VALUE);
	//@ assigns a[*];
	//@ ensures a.length == \old(a.length);
	public void addArrays(int[] a, int[] b) {
			
		if(sameSize(a, b)) {
			//@ assert sameSize(a, b);
			int[] temp = a;
			for(int i = 0; i < a.length; i++) {
				//@ assume 0 <= i < a.length;
				//@ assume Integer.MIN_VALUE < a[i] + b[i] <= Integer.MAX_VALUE;
				a[i] = temp[i] + b[i];
			}	
		}
	}
		
	//@ ensures \result <==> (a.length == b.length);
	//@ assigns \nothing;
	//@ pure
	public boolean sameSize(int[] a, int[] b) {
		return a.length == b.length;
	}
```
**Learning Objective:** 
The goal of this exercise is to see if students see how to use frame conditions in practice. If we don't include `\\@ assigns a[*]` this could cause problems later down the line if we were to add on to this program. We also begin to introduce the idea of `pure` functions with `assigns \nothing` which the student should keep in mind as we move onto later tutorials. It is important that students see how to use the `assigns` clause and frame conditions appropriately.

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

**Asnwer and Explanation:**
We are tasked with writing a void function that increases the size of a global integer array by int `increase`, so let's think of how we can accomplish this. We might want to create a new array that is of the size of the original array plus `increase`, then we want to copy anything in the original array into the new array. Then since the original array is global to the class we're working in, we would just set it equal to our new array. So we might write the following:
```Java
public class FrameCondExample2 {
	//@ spec_public
	private int[] arr = new int[10];
	
	public void increase(int increase) {
		int[] newArr = new int[arr.length + increase];

		for (int i = 0; i < arr.length; i++) {
			newArr[i] = arr[i];
		}

		arr = newArr;
	}
}
```
Now, let's start writing our JML statements to verify the function. To begin, we should require that `increase` is greater than zero and less than `Integer.MAX_VALUE` to avoid any overflow errors. Additionally, since we're dealing with addition and for-loops in the function we should include some `assume` statements to ensure that we don't run into any errors when trying to run the function. So we can write the following:
```Java
public class FrameCondExample2 {
	//@ spec_public
	private int[] arr = new int[10];
	
	//@ requires arr != null;
	//@ requires 0 < increase < Integer.MAX_VALUE;
	public void increase(int increase) {
		//@ assume 0 <= (arr.length+increase) < Integer.MAX_VALUE;
		int[] newArr = new int[arr.length + increase];

		for (int i = 0; i < arr.length; i++) {
			//@ assume 0 <= i < arr.length;
			newArr[i] = arr[i];
		}

		arr = newArr;
	}
}
```
Now what can we ensure? We can ensure that `arr.length` will always be greater than the original `arr.length`, so how can we write this? Recall the `\old()` designator, we can say `arr.length > \old(arr.length)`. However, notice how the question asks for the “strongest” specifications. If we think about it `arr.length > \old(arr.length)` is NOT the strongest postcondition we could write. It would be better to say that `arr.length == \old(arr.length + increase)` as this accounts for how we alter the length by `increase` and is more specific than simply saying the length will be greater than the original size. Additionally, we are modifying the memory location storing `arr` so we need to specify this as well and write the following to verify the function:
```Java
public class FrameCondExample2 {
	//@ spec_public
	private int[] arr = new int[10];
	
	//@ requires arr != null;
	//@ requires 0 < increase < Integer.MAX_VALUE;
	//@ assigns arr;
	//@ ensures arr.length == \old(arr.length + increase);
	public void increase(int increase) {
		//@ assume 0 <= (arr.length+increase) < Integer.MAX_VALUE;
		int[] newArr = new int[arr.length + increase];

		for (int i = 0; i < arr.length; i++) {
			//@ assume 0 <= i < arr.length;
			newArr[i] = arr[i];
		}

		arr = newArr;
	}
}
```
**Learning Objective:** 
The goal of this exercise is to see if the student understands how to use the assigns clause and give them more experience with the `\old()` designator. We want to make sure that the student understands that we need to specify any occurrence of memory locations is being modified. We also check if the student remembers past tutorials, and specifically if they can regonize the “strongest” specifications. 

## **Resources:**
+ [Frame Conditions Exercises](FrameCondEx.md)
+ [Question 1 Java](FrameCondExample1.java)
+ [Question 2 Java](FrameCondExample2.java)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)
