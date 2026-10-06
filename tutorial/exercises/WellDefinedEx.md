---
title: JML Tutorial - Exercises - Well-defined Expressions
---
# Well-defined Expressions Exercises:
## [Well-defined Expressions Tutorial](https://www.openjml.org/tutorial/WellDefinedExpressions)

## **Question 1**
**The method given below is has a specification error; determine what the error is and fix it. Explain why the specification given is not well-defined.**
```Java
    /** Stub for a method that returns the index of key in array a. **/
    public int indexOf(int[] a, int key) {
        //@ assume a[0] == key;    // ERROR: some problem with this assume!
        return 0;
    }
```
**Learning Objectives:**
+ Be able to identify where the issue in the current specifications lie 
+ Understand how to write well-defined statements
>
## **[Answer Key](WellDefinedExKey.md)**

## **Resources:**
+ [Question 1 Java](WellDefinedExample1.java)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)
