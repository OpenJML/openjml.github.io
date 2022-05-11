---
title: JML Tutorial - Preconditions (requires clauses)
---

Sometimes a method may only be called in certain combinations of program state and actual
arguments. Such restrictions are called *preconditions* and
are written with a *requires* clause.

For example, a method to compute an integer square root requires its
input to be non-negative:
```
// openjml --esc T_requires1.java
public class T_requires1 {

  //@ requires i >= 0;
  public int isqrt(int i) {
    return 0; // yet to be implemented
  }
}
```

Other common preconditions are that a parameter is not null (e.g., `o != null`)
or that an index is in range for an array (`0 <= i < a.length`).

A method's specifications may include more than one requires clause. For example,
```
// openjml --esc --nullable-by-default T_requires2.java
public class T_requires2 {

  //@ requires a != null;
  //@ requires 0 <= index < a.length;
  //@ ensures \result == a[index];
  public int getElement(int[] a, int index) {
    return a[index];
  }
}
```

There may be an order to the requires clauses. In this case, the `a.length` in
the second clause is undefined if `a` is null. Thus we also need the
condition stated in the first clause, and it must be stated before the
second clause. Reversing the order will result in an error:
```
// openjml --esc --nullable-by-default T_requires3.java
public class T_requires3 {

  //@ requires 0 <= index < a.length;
  //@ requires a != null;
  //@ ensures \result == a[index];
  public int getElement(int[] a, int index) {
    return a[index];
  }
}
```
produces
```
T_requires3.java:4: verify: The prover cannot establish an assertion (UndefinedNullDeReference) in method getElement
  //@ requires 0 <= index < a.length;
                             ^
1 verification failure
```

Ensures clauses may be mixed in order with the requires clauses, but good,
and clearer, style suggests putting all requires clauses first and then
all ensures clauses.

## **[Preconditions Problem Set](https://www.openjml.org/tutorial/exercises/PreConEx.html)**

<i>Last Modified: <script type="text/javascript"> document.write(new Date(document.lastModified).toUTCString())</script></i>
