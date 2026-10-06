---
title: JML Tutorial - Exercises - Well-defined Expressions
---
# Well-defined Expressions Exercises Key:
## [Well-defined Expressions Tutorial](https://www.openjml.org/tutorial/WellDefinedExpressions)

## **Question 1**
The method is supposed to return the index into integer array argument `a` that is equal to the integer `key`. To pass the static checks of Java, it must have a return statement, and the idea of this stub is to assume that element 0 contains the key and a call thus returns 0. However, element 0 of `a` is not necessarily defined and will not be defined if `a` is empty.  So an additional assumption is needed to make 0 a legal index into `a`, namely that the length of `a` is at least 1, this is recorded in the added assume statement, which assumes that `0 < a.length`. (Note that, by default, JML assumes that `a != null`, see [the following section on Null and non-null](Nullness) for more about this default. Furthermore, the added assumption would usually be written as a [precondition](https://openjml.org/tutorial/Preconditions.html) in JML.)
```Java
    /** Stub for a method that returns the index of key in array a. **/
    public int indexOf(int[] a, int key) {
        //@ assume 0 < a.length;
        //@ assume a[0] == key;    // ERROR: some problem with this assume!
        return 0;
    }
```


