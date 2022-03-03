---
title: JML Tutorial - Specifying Constructors
---

Constructors are a special kind of method and also need to be specified. The syntax and concepts for doing so are very similar to method specifications, with just a few extra rules.

A simple class with a few data fields might have constructors that look like this:
```
// openjml --esc T_constructors1.java
public class T_constructors1 {

  public int width;
  public int height;

  //@ public normal_behavior
  //@   requires width >= 0 && height >= 0;
  //@   ensures this.width == width;
  //@   ensures this.height == height;
  //@ pure
  public T_constructors1(int width, int height) {
    this.width = width;
    this.height = height;
  }

  //@ public normal_behavior
  //@   ensures this.width == 0 && this.height == 0;
  //@ pure
  public T_constructors1() {
    this(0,0);
  }
}
```

The first constructor simply initializes the fields from the constructor's argument list. The specification for the constructor first requires that the 
input values are non-negative and then simply says that aftger the constructor is finished, the newly constructed object's data fields equal the input
values. The heading `normal_behavior` says that the constructor does not throw any exceptions; it is discussed further [here](TBD).
There is also the modifier `pure`; more on that below.

The second constructor is similar to the first. The specification is perhaps less obvious because of the constructor call (the `this` call) of the first
constructor. The second constructor uses the _specification_ of the first constructor to prove that its implementation---which is just the this-call--- satisfies its specification.

Both of these specifications are readily verified.

For a constructor, `pure` means that nothing is assigned (for a constructor it is really initialized) other than the
fields of the new object itself. If something else were assigned, say a static field that was keeping a count of new objects, then the costructor could not be pure and would have an assignable clause:
```
// openjml --esc T_constructors2.java
public class T_constructors2 {

  public static int count = 0;

  //@ public normal_behavior
  //@  requires count < Integer.MAX_VALUE;
  //@  assigns count;
  //@  ensures count == \old(count) + 1;
  public T_constructors2() {
    count++;
  }
}
``` 

(More on pure methods [here](TBD).)
This specification is also readily verified, though it needs the precondition to be sure that we don't overflow the `count` field -- more on arithmetic overflows [here](ArithmeticModes).

The implementation of these constructors is so simple, and common, that one might think that inferring the specification from the implementation should be easy. Indeed such specification inference is a not-yet-implemented goal that would reduce some of the specification-writing burden.

TODO- say more about the whole initialization process and initializer specs.


_Last modified: 2022-03-02 21:07:27_