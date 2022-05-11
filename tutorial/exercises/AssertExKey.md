---
title: JML Tutorial - Exercises - Assert Statements
---
# Assert Statements Exercises Key:
##**[Assert Statements Tutorial](https://www.openjml.org/tutorial/AssertStatement)**

## **Question 1**
**Given the code below determine the any specifications needed to verify the function, as well as the assert statements where indicated**
```Java
public void max(int a, int b, int c) {
	int max;
	
	if(a >= b && a >= c) {
		max = a;
	//first assert
	}else if(b >= a && b >= c) {
		max = b;
	//second assert
	}else {
		max = c;
	}				
	//third assert
}
```

**Asnwer and Explanation:**
First, let’s understand what the code is doing. The function takes in three integer numbers `a`, `b`, and `c`, the function then compares each integer against the other two. Note that when comparing the integers the `>=` operator is used, since we were not told that each integer would be distinct from the others. We are not given any definite pre or postconditions that need to be met, but we are told to write the appropriate assert statements where indicated. Remember that `assert` is used when a condition is expected to "hold at a point within the body of a method."

So what can we assert in the function above? We know that since we are checking if the values are `>=` to each other, one value will be set to `max` no matter what. Therefore, we can assert the following:
```Java
public void max(int a, int b, int c) {
	int max;
		
	if(a >= b && a >= c) {
		max = a;
	//@ assert max >= a;
	}else if(b >= a && b >= c) {
		max = b;
	//@ assert max >= a && max >= b;
	}else {
		max = c;
	}				
	//@ assert max >= a && max >= b && max >= c;
}
```
Given these assert statements, we can now write a postcondition for the function which basically is ensuring what we are asserting at the end of our function. 

```Java
//@ ensures \result >= a && \result >= b && \result >= c;
public void max(int a, int b, int c) {
	int max;
		
	if(a >= b && a >= c) {
		max = a;
	//@ assert max >= a;
	}else if(b >= a && b >= c) {
		max = b;
	//@ assert max >= a && max >= b;
	}else {
		max = c;
	}				
	//@ assert max >= a && max >= b && max >= c;
}
```
**Learning Objective:**
The goal of this exercise is to see if the student can identify how assert can be used in practice, and how logically it can be written in different ways. In the exercise the student can see that no matter what, the program WILL return whatever it determines to be the max value. But the student can make sure that the program returns a value that makes sense. There are no preconditions for this program, and since the student is not told that the values can't all be the same they can begin to make some assertions after the if statement. We want to see if the student can identify what can be asserted.

## **Question 2**
**Given the function below, write the strongest assert statements that will pass at the places indicated.**
```Java
//@ requires num > 0;
public boolean primeChecker(int num) {
	boolean isPrime;
	for (int i = 2; i <= num / 2; i++) {
		//@ assume i > 0;
		if (num % i == 0) {
			//first assertion here
			isPrime = false;
			//second assertion here 
			return isPrime;
		}
	}
	
	isPrime = true;
	//third assertion here
	return isPrime;
}
```
**Asnwer and Explanation:**
The function above checks if a number passed in is prime or not, and returns `flag =  true` if it is, and `flag = false` if it's not. We are already given some specifications needed to run this program without any warnings. However, we are asked to determine and include any assertions that can be made. We know that the function will stop and return `flag = false` if it finds that `num` is divisible by anything other than one and itself. If the function runs through the entire for-loop without finding that `num` is divisible by anything other than one and itself, it returns `flag = true` - in other words it has concluded that `num` is a prime number. So, we can assert that the function will set `flag` to false if `num % i == 0`, and we can also assert that `flag` will be set to true if the function runs through the for-loop without stopping. So we can write the following:
```Java
//@ requires num > 0;
//@ ensures \result <==> !(\exist int i; i >= 2; num % i == 0);
public boolean primeChecker(int num) {
	boolean isPrime;
	for (int i = 2; i <= num / 2; i++) {
		//@ assume i > 0;
		if (num % i == 0) {
			//@ assert num % i == 0;
			isPrime = false;
			//@ assert isPrime == false;
			return isPrime;
		}
	}
	
	isPrime = true;
	//@ assert isPrime == true;
	return isPrime;
}
```

**Learning Objective:** 
The goal of this exercise is to see if the student can identify what assertions can be made at certain points in the code. To avoid confusion the student is told where in the code the assert is meant to me added. This exercise also checks that the student understand that we cannot assert false because this will cause an error in OpenJML, which is why we assert that the variable flag can be false.

## **Resources:**
+ [Assert Statements Exercises](AssertEx.md)
+ [Question 1 Java](AssertExample1.java)
+ [Question 2 Java](AssertExample2.java)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)