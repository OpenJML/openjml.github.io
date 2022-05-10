---
title: JML Tutorial - Exercises - Speciyfing Exceptions
---
# Speciyfing Exceptions Exercises:
## **Question 1**
**Given the function below, what additional specifications are needed to verify the function?**
```Java
//@ signals (Exception e) false;
public int elementAtIndex(int[] arr, int index) {
      return arr[index];
}
```
**Learning Objectives:**
+ Understand how to use the `signals`clause
+ Undertsand what the exception is saying

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
**Learning Objectives:**
+ Gain more experience with handling exceptions
+ Understand how to handle multiple specification cases
+ Introduction to the `also` clause

## **[Answer Key](SpecifyingExceptionsExKey.md)**
