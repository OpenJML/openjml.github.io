---
title: JML Tutorial - Exercises - Assume Statements
---
# Assume Statements Exercises:
## [Assume Statements Tutorial](https://www.openjml.org/tutorial/AssumeStatement)

## **Question 1**
**Given the method below, write assume statements (or a single assume statement) that are (is) needed to verify the method, where the comments indicate.** (Note that sometimes it is helpful to write two separate `assume` or `assert` statements, to make debugging easier, instead of combining them with a conjunction such as `&` or `&&`).
```Java
public class AssumeExample1 {
    //@ requires a != null;
    //@ ensures \result.length == a.length;
    public int[] reverseArray(int[] a) {
        int len = a.length;
        int[] b = new int[len];
        
        for (int i = 0; i < a.length; i++) {
            // first assume here (or both combined)
            // second assume here
            b[len - 1] = a[i];
            len--;			
        }
        //@ assert b.length == a.length;
        return b;
    }
}
```
**Learning Objectives:** 
+ Understand how `assume` can be used for loops

## **Question 2**
**The following code has an error with finding the max value in an array. Determine how assume statements can be used to find where in the code the error occurs.**
```Java
    public int sortFindMax(int[] a) {
        //@ assume a != null; // in place of a precondition
        int max;

        for (int i = 0; i < a.length-1; i++) {
            for (int j = i+1; j < a.length; j++) {
                // first assume here (or both first and second)
                // second assume here
                if (a[i] > a[j]) {
                    int temp = a[i];
                    a[i] = a[j];
                    a[j] = temp;
                }
            }
        }
        // third assume here (or both third and fourth)
        // fourth assume here
        max = a[a.length-1];
        // fifth assume here
        //@ assert (\exists int m; 0 < m < a.length; a[m] <= max);
        //@ assert (\forall int k; 0 < k < a.length; a[k-1] <= a[k]);
        return max;
    }
```
**Learning Objectives:** 
+ Understand how `assume` can be used for debugging 
+ Understand the relationship between `assume` and `assert`
+ Understand the differences between `assume` and `assert`

## **[Answer Key](AssumeExKey.md)**
## **[All exercises](https://www.openjml.org/tutorial/exercises/exercises)**

## Resources
+ [Code for question 1](AssumeExample1.java)
+ [Code for question 2](AssumeExample2.java)

