---
title: JML Tutorial - Method Specifications:old clauses and clause ordering
---

We have introduced a few kinds of method specification clauses so far. In fact there are many more, though most are not widely used:
* Precondition clauses
  * `requires`
  * [`old`](#old-clause)
* Frame conditions
  * `reads` (`accessible`)
  * `assignable` (`assigns`)
  * `captures`
  * `callable`
* Postconditions
  * `ensures`
  * `signals`
  * `signals_only`
  * `diverges`
  * `duration`
  * `working_space`
* Termination
  * `measured_by`

TODO -- add links to the above; check for completeness

Some of these have been already discussed; others are discussed in later lessons; and others are omitted from the tutorial because they are too advanced or too ill-defined -- see the JML Reference Manual for details on those. The `old` clause is presented below. Those clauses discussed in this tutorial are clickable hyperlinks in the above list.

## Ordering of clauses

There is no pre-defined order to the clauses within a single specification case (cf. a later lesson on [multiple specification cases](MultipleBehaviors)].
However, a specification is much more readable if the clauses generally follow the order above, with preconditions first, then frame conditions, followed by postconditions.

There is some meaning to the ordering within the precondition group and witbhin the postcondition group: earlier clauses can set conditions that are needed for later clause to be well-defined. For example,
```
// openjml --esc T_order1.java
//@ nullable_by_default // for the purpose of this example
public class T_order1 {

  //@ requires a.length > 10;
  //@ requires a != null;
  public void m(int[] a) {}

}
```
yields
```
T_order1.old
```
The first requires clause might not be well-defined because `a` might be null. If we reverse the order of the clauses, then JML is content:
```
// openjml --esc T_order2.java
//@ nullable_by_default // for the purpose of this example
public class T_order2 {

  //@ requires a != null;
  //@ requires a.length > 10;
  public void m(int[] a) {}

}
```
is successfully verified.



## old clause


TODO

<i>Last Modified: <script type="text/javascript"> document.write(new Date(document.lastModified).toUTCString())</script></i>