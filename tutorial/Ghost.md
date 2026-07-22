---
title: JML Tutorial - Ghost variables and computations
---

It is sometimes helpful (for specification or verification) to include in a program various variables or computations that are intended only for specification or verification.
In JML one can use a `ghost` field to, for example, keep track of information about an object class that the Java implementation does not track.
Or, in the body of a method, one may want to record some value or perform some computation for the purpose of 
checking the Java implementation, but not have that variable or computation be part of the Java implementation or 
compiled into the Java class (and thus not be executed when running the code).

This can be particularly helpful if the ghost computation is easier to understand than some complicated (and hopefully faster) algorithm or data structure, especially when the ghost computation can be used to check the computation that the code performs at runtime.

JML provides `ghost` declarations and various JML-only statements for this purpose:

* Field declarations can be modified with the `ghost` keyword and placed in a JML comment. Such fields are in scope for
specifications but not in Java code.
* The JML `set` statement permits assignments and computations that are only done in the specification (not in the code):
```
  //@ ghost int i = x; // x may be a Java variable
  //@ set i = i + 10; // a ghost computation
```
`set` statements may also include pure method calls.

The values of `ghost` variables may then be used in subsequent JML `assert` (and `assume`) statements. These ghost variables and ghost computations can be used to prove that some step taken in algorithm or data structure design is justified. Alternatively, they may be used to point out to the reader some properties of the code written (such as its time efficiency or the equivalence of some sophisticated data structure to a straightforward one), without incurring a (time or space) penalty at runtime. Furthermore, ghost variables may be used to make stating assertions (or assumptions) easier.

JML also has `model` fields and `represents` specification that can be used to help specify classes and interfaces. These are also specification-only constructs. (See the section on [model fields and datagroups](ModelFields).)

## **[Exercises](https://www.openjml.org/tutorial/exercises/GhostEx.html)**

Follow the link in the above heading to work on the exercises on this topic.
