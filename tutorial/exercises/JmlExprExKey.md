---
title: JML Tutorial - Exercises - JML Expressions
---
# JML Expressions Exercises Key:
## **Question 1**
**Take a look at the following function that checks if the number passed is prime. We've seen this code before, but now that you've read about JML Expressions, what can now be ensured about the function?**
```Java
//@ requires num > 0;
public boolean primeChecker(int num) {
	boolean flag;
	for (int i = 2; i <= num / 2; i++) {
		//@ assume i > 0;
		if (num % i == 0) {
			flag = false; 
			//@ assert num % i == 0;
			//@ assert flag == false;
			return flag;
		}
	}
		
	flag = true;
	//@ assert flag == true;
	return flag;
}
```
**Asnwer and Explanation:**
First we need to see if we understand what the function is doing. The function runs from 2 to `num/2` since we know that `num` will always be divisible by one. Therefore, we don't want to call a false negative on the number passed in because it is divisible by one. However, note that we only loop up to `num/2` because a number is never divisible by more than half of itself. For example, let's say we want to find the factors of 12, we have 1 and 12, 2 and 6, and 3 and 4, notice that the greatest factor other than the number itself is 6, which is half of 12 and no other factor is greater than this factor.

So, we can `ensure` that the result of the function will be equivalent to the negation of whether a value exists for `i` that proves `num % i == 0`. We can write this as seen below:
```Java
//@ requires num > 0;
//@ ensures \result <==> !(\exist int i; i >= 2; num % i == 0);
public boolean primeChecker(int num) {
	boolean flag;
	for (int i = 2; i <= num / 2; i++) {
		//@ assume i > 0;
		if (num % i == 0) {
			flag = false; 
			//@ assert num % i == 0;
			//@ assert flag == false;
			return flag;
		}
	}
	
	flag = true;
	//@ assert flag == true;
	return flag;
}
```
Note that since the function returns a boolean we use the `\exist` expression so we can check if something exists for `i >= 2` where `num % i == 0` exists. So if there is a value where `num % i == 0` `\exist` would be true so we take the negation of this since we return false is the number passed in is not prime. Additionally, we use the `<==>` expression to check if the boolean returned by the function matches the result of `\exist`.

**Learning Objective:** 
The goal of this exercise is to teach the student on two of the concepts introduced in the JML Expressions tutorial. After reading the tutorial the student should have a good understanding of quantified expressions as well as JML operators. The exercise above will also allow the student to see how these quantified expressions can be used in practice, and checks if the student understands what different expressions do. Additionally, by using code the student has seen before they should have a better understanding of what it does and how to add onto previous JML statements.

## **Question 2**
**Write a function that simulates the truth table for the Discrete Mathematical inference rule of Modus Ponens, use the function header given below to construct your function. Determine the specifications needed to verify your function.**
```Java
public boolean modusPonens(boolean p, boolean q);
```
**On the subject of Modus Ponens:**
Modus Ponens is a rule of inference, which states that if p is true, and p implies q, then q is true. Take a look at the truth table below. 
|   p    |   q    | p -> q |
|--------|--------|--------|
|  true  |  true  |  true  |
|  true  |  false |  false |
|  false |  true  |  true  |
|  false |  false |  true  |

**Asnwer and Explanation:**
First we need to understand what the inference rule Modus Ponens does. Simply put, `p` implies `q`; if `p` is true then `q` must also be true. We can use the following truth table to understand what different inputs of `p` and `q` produce. 
 
We see that `p -> q` is true for `p == true` and `q == true`, but also for `p == false` and either true or false for `q`. The only event where `p -> q` is false is when `p == true` and `q == false`.  Given this we can construct the following code for the given function header.
```Java 
public boolean modusPonens(boolean p, boolean q) {
	if (p == true) {
		if (q == true) {
			return true;
		} else {
			return false;
		}
	} else {
		return true;
	}
}
```
Now we can determine any specifications needed. We know that JML has an implication operator (==>) which we can use in this case to write an ensures statement. We can ensure that the result will be equivalent to `p -> q` no matter what boolean input `p` and `q` are. So we can write the following:
```Java
//@ ensures \result <==> (p==>q);	
public boolean modusPonens(boolean p, boolean q) {
	if (p == true) {
		if (q == true) {
			return true;
		} else {
			return false;
		}
	} else {
		return true;
	}
}
```
**Before we move on, take a look at these other correct implementations of Modus Ponens:**

**Version 1:** 
```Java
//@ ensures \result <==> (p==>q);
boolean modusPonens(boolean p, boolean q) {
  	return !p || q;
}
```
In this version we can see that we can significantly shorten the lines of code it takes to achieve the same result. Let’s break down this return statement to make sure that it follows the truth table of Modus Ponens. If `p` is false we take the opposite of false, which is true, and since we are using the or logical operator we will return true if `p` is false. If we look at our truth table we see that this aligns, when `p` is false the result will always be true no matter the value of `q`. If `p` is true however, we have to look at our value of `q`; if `q` is true we return true, else we return false. This implementation allows us to use the same ensures clause from our original version of the code, and it is important to note that this is one advantage of using JML. It allows us to use the same conditions for different code to ensure we have the correct output. 

**Version 2:** 
```Java
//@ ensures \result <==> (p==>q);
boolean modusPonens(boolean p, boolean q) {
   	return (p ? q : true);
}
 ```
We can also use the question mark and colon operator to rewrite the if-else code to simulate Modus Ponens. Recall that when using the question mark and colon we read it the same way as an if-else statement. First we check if `p` is true or false - remember that we don’t have to explicitly write `p == true` to check if `p` is true, simply checking `p` is enough - if `p` is true we return `q`, if `p` is false we return true. This also follows the truth table for Modus Ponens. If `p` is true we check the value of `q` and return whatever `q` is because that is what the result is dependent on; if `p` is false we simply return true. Again, we can use the same JML postcondition statement from our original code to verify the function.  

**Learning Objective:** 
The goal of this exercise is to further check if the student understands how JML operators work, and how they can be used to ensure that the function they write performs what it is intended. We also want to show the student that they can reuse JML statements for different versions of the same code - which is one of the benefits of JML. 


## **Resources:**
+ [JML Expressions Exercises](JmlExprEx.md)
+ [Question 1 Java](JMLExprExample1.java)
+ [Question 2 Java](JMLExprExample2.java)
