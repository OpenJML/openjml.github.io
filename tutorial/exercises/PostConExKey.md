---
title: JML Tutorial - Exercises - Postconditions
---
# Postcondition Exercises Key:
## **Question 1**
**(a) Suppose that the function below had its specifications changed for num, where num is updated so that it only has to be greater than -1. Determine why this would cause an error, and how you could fix the remaining specifications to verify the function.**
```Java
//@ requires 0 < num < 100;
//@ ensures \result > num;
 public int multiplyByTwo(int num) {
	return num*2;
}
```
**Answer and Explanation:**
First, let’s determine what the function does; it takes in an integer number variable `num`, and will multiply this number by 2 and return it. It is important to understand how `num > -1` affects the code. Saying that `num > -1` now includes zero as a potential input. If `num = 0`, then result would equal zero (0 * 2 = 0). Therefore, we cannot ensure that the result is greater than `num`, because in this case it is equal to `num`. Therefore, we would need to include the following to fix the specifications of the code and verify it by writing the following:
```Java
//@ requires -1 < num < 100;
//@ ensures \result >= num;
public int multiplyByTwo(int num) {
	return num*2;
}
```
**(b) Suppose we revert to the orignal specifications where num > 0. The function is unable to be verified. Determine where in the specifications it is failing, and fix it.**

**Answer and Explanation:**
The function is failing to verify in OpenJML with the current specifications. To figure out why the program is failing let’s determine what we do know. 

Since the number being passed in is a whole number, we know that the returned result will always be greater than the original number passed in when the number is greater than 0. In other words we can ensure the result will always be greater than num, required that num is greater than zero. However, we also need to take into account the return type is an `int`; therefore, we need to make sure that the number being passed in * 2 does not exceed the range of the type int. Additionally, ints in Java are 32 bit 2's complement numbers, and so they range from -2^31 to (2^31)-1.

We can see here that the program fails to verify because we are not specifying the range of `num`. To fix this problem, we simply need to include how big `num` can be.
```Java
//@ requires num > 0;
//@ requires num <= Integer.MAX_VALUE/2;
//@ ensures \result > num;
public int multiplyByTwo(int num) {
	return num*2;
}
```
By including the second requirement that `num <= Integer.MAX_VALUE` and `num <= Integer.MAX_VALUE/2`, we can now ensure that the result will always be greater than the original number passed in.

**(c) Suppose the code was updated to the following, and num must be a positive number. Determine the specifications needed to verify the function.**
```Java
 public int multiplyByTwo(int num) {
	return num/2;
}
```
**On the subject of "strongest" specifications:**
Let's think about the formula P implies Q. When we say the "strongest" postcondition, we want to find the state that P is stronger so that Q is true. We might say that the function above implies "true," but this would be the weakest postcondition - as it is not that specific. So we want to be as specific as possible when writing specifications. This allows for fewer implementations.  

**Answer and Explanation:**
First let's start with what we know. We are told that `num` must be positive, therefore, `num > 0` - since zero is neither positive nor negative. Secondly, the code has been updated to `num / 2` from `num * 2`. If `num * 2` ensured a value greater than num, then what is `num / 2` ensuring? Well, we know that whenever we divide a whole positive number by anything, the value gets smaller and smaller. Therefore, the code above ensures that the result will be less than the number passed in when `num` is greater than 0. So we can write:
```Java
//@ requires num > 0;
//@ requires num < Integer.MAX_VALUE*2;
//@ ensures \result < num;
public int multiplyByTwo(int num) {
	return num*2;
}
```
**Learning Objective:**
The goal of this exercise is to show students that warnings that might not occur when testing programs by hand still need to be account for. In part (a) we see that unless we specify the range of num we will have an overflow error because num * 2 would exceed the range of type int. If you were to input num = 10000000000 by hand, the compiler would tell the client that the value inputted is to large for the return type int. Additionally, part (b) has the goal of teaching the student how different preconditions affect the postconditions. In part (b) we see that num can now be 0, so we need to make sure that our postcondition reflects this change to the preconditions; in this case we have to update that the result can be greater than OR equal to num. Finally, part (c) checks if the student can begin to write JML statements on their own. The function is changed slightly to see if the student understands how pre and postconditions cannot simply be copy and pasted for simple functions. 

## **Question 2**
**Given a rectangle of width w and height h, write a function that finds the area of the rectangle and returns it. Determine the strongest specifications needed to verify the function. The function header is given below.**
```Java 
public int area(int w, int h);
```
**Answer and Explanation:**
When coming up with specifications for a program we should first organize the program into pre and post conditions, and consider what we know. We are tasked with writing a function that finds the area of a rectangle of width w and height h. The area of any rectangle is simply A=w∗h, so if we were to code this we would get something like this:
```Java
public int area(int w, int h) {
	int A = w*h;
	return A;		
}	
```
Now that we have our function, we want to determine any preconditions and postconditions, so what do we know needs to be true of the area of a rectangle? Firstly, we know that area can neither be negative nor zero. Secondly, we also know that in terms of the code, we are returning an integer value, so we have to ensure that `w*h` do not exceed the range of the type `int`

However, we're not done yet. Let's say that `w = 2`, `h = 3`, then `A = 6`; what does this mean? This means that since we're multiplying w and h together the result `A` will always be greater than either w or h. Additionally, if `w > 0` and `h > 0`, that means when `w = 1` and `h = 1` would result in `A = 1`. So the result could also equal `w` or `h` if `w = 1` and `h = 1`. Therefore, we can also ensure the following:
```Java
//@ requires w > 0 & h > 0;
//@ requires w <= Integer.MAX_VALUE/h;
//@ ensures \result > 0;
//@ ensures \result >= w;
//@ ensures \result >= h;
public int area(int w, int h) {
	int A = w*h;
	return A;		
}	
```
**Learning Objective:**
The goal of this exercise is to teach students how to find all the pre/postconditions needed when writing a function. The student is tasked with writing a simple function that takes in the width and height of a rectangle and returns the area. It requires that the student have some understanding of mathematics to know that Area can never be negative nor zero. Therefore, the student needs to ensure that the preconditions reflect this. Additionally, it tests that students take into account potential inputs that might cause an over flow error since we are multiply two integers and returning an integer. The bigger test comes with the postconditions. If the student can determine that Area cannot be negative nor zero than what does this ensure of the function? It ensures that the result is always greater than 0, and that the result will always be greater than or equal to the width and height of the rectangle. It is also important that students realize that ensuring these postconditions will prevent any errors that might occur if this code is used in another program and a client tries to input values that are not valid.

## **Resources:**
+ [Postcondition Exercises](PostConEx.md)
+ [Question 1 Java](PostconditionExample1.java)
+ [Question 2 Java](PostconditionExample2.java)