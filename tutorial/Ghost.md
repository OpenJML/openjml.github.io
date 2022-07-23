---
title: Ghost variables and computations
---

It is sometimes helpful to include in a program various variables or computations that are only for specification.
For example, a ghost field might keep track of information about a class that the Java implementation does not.
Or, in the body of a method, one may want to record some value or perform some computation for the purpose of 
checking the Java implementation, but not have that variable or computation be part of the Java implementation or 
compiled into the runnable class.

JML provides `ghost` declarations and various JML-only statements for this purpose.

- Field declarations can be modified with the `ghost` keyword and placed in a JML comment. Such fields are in scope for
specifications but not in Java code.
- Model field methods and classes are also specification-only constructs.
- The JML `set` statement permits assignments and computations:
```
  //@ ghost int i = x; // x may be a Java variable
  //@ set i = i + 10; // a ghost computation
```
`set` statements may also include pure method calls.

The values of `ghost` variables may then be used in subsequent JML `assert` statements, for example.
