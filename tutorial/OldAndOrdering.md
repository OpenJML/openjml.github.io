---
title: JML Tutorial - Method Specifications: old clauses and clause ordering
---

We have introduced a few kinds of method specification clauses so far. In fact there are many more, though most are not widely used:
* Precondition clauses
  * [`recommends`](Recommends)
  * [`requires`](Preconditions)
  * [`old`](#old-clause)
* Frame conditions
  * `reads` (`accessible`)
  * [`assignable` (`assigns`, `writes`)](FrameConditions)
  * `captures`
  * `callable`
* Postconditions
  * [`ensures`](Postconditions)
  * [`signals`](SpecifyingExceptions)
  * [`signals_only`](SpecifyingExceptions)
  * `diverges`
  * `duration`
  * `working_space`
* Termination
  * `measured_by`

Some of these have been already discussed; others are discussed in later lessons; and others are omitted from the tutorial because they are too advanced or too ill-defined -- see the JML Reference Manual for details on those. The `old` clause is presented below. Those clauses discussed in this tutorial are clickable hyperlinks in the above list.

## Ordering of clauses

There is no pre-defined order to the clauses within a single specification case (the same applies to [multiple specification cases](MultipleBehaviors)).
However, a specification is more readable (by people familiar with JML) if the clauses generally follow the order above, with preconditions first, then frame conditions, followed by postconditions.

There is some meaning to the ordering within the precondition group and within the postcondition group: earlier clauses can set conditions that are needed for later clauses to be well-defined; but ordering only matters within the each kinds of clause; that is ordering matters within the set of preconditions (`requires` clauses) and separately within the set of postconditions (`ensures` clauses). For example,
```
{% include_relative T_order1.java %}
```
yields
```
{% include_relative T_order1.out %}
```
The first requires clause might not be well-defined because `a` might be null. However, if we reverse the order of the clauses, as in the following specification, then the method verifies.
```
{% include_relative T_order2.java %}
```


## old clause

The `old` clause is a means to compute a value (in the pre-state) that is used elsewhere in the specification.
It is a means to factor out common subexpressions, to compute something in the pre-state that is used in the postconditions, or to simply make the specification more readable.
In the following, the value of `g` is determined in the pre-state of a call to `GCD3`, and that value is used again in other that method's preconditions and in its postcondition.
```
{% include_relative T_Old.java %}
```

## **[Old and Ordering Problem Set](https://www.openjml.org/tutorial/exercises/OldAndOrderingEx.html)**

