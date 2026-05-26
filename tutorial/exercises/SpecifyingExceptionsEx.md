---
title: JML Tutorial - Exercises - Specifying Exceptions
---
# Specifying Exceptions Exercises:
## [Specifying Exceptions Tutorial](https://www.openjml.org/tutorial/SpecifyingExceptions)

## **Question 1**
**Are any additional specifications needed to verify the method below? If so, write them and check that your answer verifies with OpenJML. (Do not change the code or the signals clause in the specification.)**
```Java
//@ signals (Exception e) false;
public int elementAtIndex(int[] arr, int index) {
      return arr[index];
}
```

## **Question 2**

**Consider the method `getHash` below.
(a) Why is the precondition `str != null` unnecessary?
(b) What should the `signals_only` clause in the specification be changed to so that the implementation will verify without changing the code?
(c) What would be the strongest predicate that could used in a `signals` clause added to the spcification so that the code would still verify?
(Check your answer using OpenJML.)**
```Java
   //@ signals_only \nothing;
   public int getHash(String str, int tableSize) {
       if (tableSize == 0) {
           throw new IllegalArgumentException();
       }
       return str.length() % tableSize;
   }
```

**Learning Objectives:**
+ Understand how to use the `signals` and `signals_only` clauses
+ Understand what the exception is saying

## **[Answer Key](SpecifyingExceptionsExKey.md)**
## **[All exercises](https://www.openjml.org/tutorial/exercises/exercises)**
