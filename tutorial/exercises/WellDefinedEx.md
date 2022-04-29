---
title: JML Tutorial - Exercises - Well-defined Expressions
---
# Well-defined Expressions Exercises:
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
## **[Key](WellDefinedExKey.md)**
