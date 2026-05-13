---
title: JML Tutorial - Ghost variables and computations
---

It is sometimes helpful to include in a program various variables or computations that are only for specification purposes.
In JML one can use a `ghost` field to, for example, keep track of information about an object class that the Java implementation does not track.
Or, in the body of a method, one may want to record some value or perform some computation for the purpose of 
checking the Java implementation, but not have that variable or computation be part of the Java implementation or 
compiled into the Java class (and thus not be executed when running the code).

JML provides `ghost` declarations and various JML-only statements for this purpose:

* Field declarations can be modified with the `ghost` keyword and placed in a JML comment. Such fields are in scope for
specifications but not in Java code.
* The JML `set` statement permits assignments and computations that are only done in the specification (not in the code):
```
  //@ ghost int i = x; // x may be a Java variable
  //@ set i = i + 10; // a ghost computation
```
`set` statements may also include pure method calls.

The values of `ghost` variables may then be used in subsequent JML `assert` statements, for example.

JML also has `model` fields and `represents` specification that can be used to help specify classes and interfaces. These are also specification-only constructs. (See the section on [model fields and datagroups](ModelFields).)

