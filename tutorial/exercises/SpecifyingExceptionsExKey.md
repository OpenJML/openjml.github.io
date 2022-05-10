---
title: JML Tutorial - Exercises - Speciyfing Exceptions
---
# Speciyfing Exceptions Exercises Key:
## **Question 1**
**Given the function below, what additional specifications are needed to verify the function?**
```Java
//@ signals (Exception e) false;
public int elementAtIndex(int[] arr, int index) {
      return arr[index];
}
```
**Asnwer and Explanation:**
The function above simply returns the element at `index` in an integer array `arr`, and takes in said array and the index we want to access. The function will run in a Java compiler without any exceptions being thrown. However, if we run it in OpenJML we will get a warning that `arr[index]` is possibly too large, negative, and out of range. As it stands with the current specifications the `singals` statement cannot be verified. We need to include some additional specifications to verify the function and the `signals` statement.
 
We can first need to ensure that the function will always return the element at `index` in the array, which is `arr[index]`. Furthermore, to deal with the warnings about trying to access `arr` at `index` we should include an assume clause stating the range that `index` can be. By including these specifications the `signals` statement can now be verified, and we can say that an exception cannot be thrown since the function will verify as true.
```Java
//@ requires 0 <= index < arr.length;
//@ ensures \result == arr[index];
//@ signals (Exception e) false;
public int elementAtIndex(int[] arr, int index) {
	return arr[index];
}
```
**Learning Objective:** 
The goal of this exercise is to see if the student can identify the specifications needed so that the statement `signals (Exception e) false` verifies. The student should understand that `signals (Exception e) false` is essentially saying that if the function verifies as true, then no exceptions can be thrown. As it is, the original code does not include any specifications that would prove that the method is correct when OpenJML will try every possible path when running the code.

## **Question 2**
**Given the function below, what exceptions should be included?**
```Java
/*@ requires str == null;
    	@  //first exception here
    	@ also
    	@   requires str != null && tableSize == 0;
    	@   //second exception here
    	@ also
    	@   requires str != null && tableSize > 0;
    	@   //postcondition here 
    	@*/
	public int getHash(String str, int tableSize) {
		if(str == null) throw new NullPointerException();
		if(tableSize == 0) throw new ArithmeticException();
		
		return str.length()%tableSize;
	
	}
```
**Asnwer and Explanation:**
The function given above takes in a String `str` and an int `tableSize` and will find the hash value given the simple formula of string length mod table size. However, within the function we check if `str` is null - in which case we throw a null pointer exception because `str` wouldn't have a length to mod by. Then we check if `tableSize == 0` and throwa arithmetic exception because we cannot divide by zero. 

As such we can see that we have multiple specification cases. There is the case when `str` is null, `also` when `str` isn’t null byt `tableSize` is zero, and `also` when `str` isn’t null and `tableSize` is greater than zero. We see these cases outlined in the code given above. Our job is to find out what goes on the commented lines. Note that `also` is used to specify that we have multiple specification cases and needs to be included between an pre and postconditions that don’t go together. We will get more in depth about handling multiple specification cases in the [“Multiple Method Behvaior”](https://www.openjml.org/tutorial/MultipleBehaviors) tutorial. 

First, let’s tackle the case that `str` is null. Luckily for us the code itself tells us what should happen in this event, and null pointer exception should be thrown. Therefore, we should use the `signals` clause to denote this exception by writing the following:
```Java
/*@ requires str == null;
    	@  signals_only NullPointerException;
    	@ also
    	@   requires str != null && tableSize == 0;
    	@   //second exception here
    	@ also
    	@   requires str != null && tableSize > 0;
    	@   //postcondition here 
    	@*/
	public int getHash(String str, int tableSize) {
		if(str == null) throw new NullPointerException();
		if(tableSize == 0) throw new ArithmeticException();
		
		return str.length()%tableSize;
	
	}
```
Now, in the event that `str` isn’t null but `tableSize` is zero we know from the code that we need to throw an arithmetic exception because we can’t divide by zero. So we can use another `signals` clause to write that: 
```Java
/*@ requires str == null;
    	@  signals_only NullPointerException;
    	@ also
    	@   requires str != null && tableSize == 0;
    	@   signals_only ArithmeticException;
    	@ also
    	@   requires str != null && tableSize > 0;
    	@   //postcondition here 
    	@*/
	public int getHash(String str, int tableSize) {
		if(str == null) throw new NullPointerException();
		if(tableSize == 0) throw new ArithmeticException();
		
		return str.length()%tableSize;
	
}
```
Finally, in the event that we have all of the desired requirements met we know we just have to denote what the function will do. In the case that `str` isn’t null and `tableSize` is greater than zero we know the function should return `str.length()%tableSize`. So we can simply write the following: 
```Java
/*@ requires str == null;
    	@  signals_only NullPointerException;
    	@ also
    	@   requires str != null && tableSize == 0;
    	@   signals_only ArithmeticException;
    	@ also
    	@   requires str != null && tableSize > 0;
    	@   ensures \result == str.length % tableSize; 
    	@*/
	public int getHash(String str, int tableSize) {
		if(str == null) throw new NullPointerException();
		if(tableSize == 0) throw new ArithmeticException();
		
		return str.length()%tableSize;
	
	}
```
**Learning Objective:** 
The goal of this exercise is to see if the student understands how signals can be used in practice. We want the student to see how the `also` clause is used to handle multiple specification cases. In the exercise the student is given the format of how these multiple specification cases should be handles, and the student is also told where they need to write their own specifications. The student should be able to follow easily as the code tells them what to do in each case. 

## **Resources:**
+ [Specifying Exceptions Exercises](SpecifyingExceptionsEx.md)
+ [Question 1 Java](SpecifyingExceptionsExample1.java)
+ [Question 2 Java](SpecifyingExceptionsExample2.java)

