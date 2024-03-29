---
title: JML Tutorial - Exercises - Well-defined Expressions
---
# Well-defined Expressions Exercises:
## [Well-defined Expressions Tutorial](https://www.openjml.org/tutorial/WellDefinedExpressions)

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
**Learning Objectives:**
+ Be able to identify where the issue in the current specifications lie 
+ Understand how to write well-defined statements
+ Understand the importance of placement of JML specifications 

## **[Answer Key](WellDefinedExKey.md)**
## **[All exercises](https://www.openjml.org/tutorial/exercises/exercises)**