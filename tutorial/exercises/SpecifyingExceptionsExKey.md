---
title: JML Tutorial - Exercises - Speciyfing Exceptions
---
# Specifying Exceptions Exercises Key:
## [Specifying Exceptions Exercises](https://www.openjml.org/tutorial/exercises/SpecifyingExceptionsEx)

## **Question 1**

The method simply returns the element at the argument `index`
in the array argument `arr`. This method will execute without problems, unless `index` is too large or negative. However, OpenJML will point out those possible errors, warning that in the implementation `index` could be too large or negative, which would cause a (Java) runtime exception. Since the specification prohibits that exception from being thrown, the implementation cannot be verified.

The simplest addition to the specification to allow the code to be verified is to restrict `index` to be a legal index into the array,
using the following requires clause.
```
//@ requires 0 <= index < arr.length;
```

One can also specify an ensures clause. although the function does verify without that being specified (since the default ensures clause is `ensures true`, which is trivially satisfied by the code).
A stronger ensures clause that also verifies would be the following.
```
//@ ensures \result == arr[index];
```

## **Question 2**

For the `getHash` method:

(a) Requiring that `str` is not null is not needed, since that is the default in JML.

(b) Since the `getHash` method throws an `IllegalArgumentException`, that exception type must be listed in a `signals_only` clause. This results in the following code that does verify.

```Java
    //@ signals_only IllegalArgumentException;
    public int getHash(String str, int tableSize) {
        if(tableSize == 0) {
            throw new IllegalArgumentException();
        }
	return str.length() % tableSize;
    }
```

(c) A signals clause that could be added to the method would be the following.
```
    //@ signals (IllegalArgumentException) tableSize == 0;
```
which says that if an `IllegalArgumentException` is thrown, then the value of the argument `tableSize` must have been 0.

## **Resources:**
+ [Specifying Exceptions Exercises](SpecifyingExceptionsEx.md)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)
