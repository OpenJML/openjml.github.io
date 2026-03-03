---
title: JML Tutorial - Preconditions (requires clauses)
---

Sometimes a method may work (or be well-defined) in certain combinations of program state and actual
arguments. Such restrictions are called *preconditions* and
are written with one (or more) *requires* clause(s).

For example, a method to compute an integer square root requires its
input to be non-negative:
```
{% include_relative T_requires1.java %}
```

Other common preconditions are that a collection is not empty
(e.g., `!c.isEmpty()`)
or that an index is in range for an array (`0 <= i < a.length`).
Note that the default in JML is that arguments are automatically considered to be non-null (`a != null`) unless the specification indicates otherwise; see [Null and non-null](Nullness).

A method's specifications may include more than one requires clause. For example,
```
{% include_relative T_requires2.java %}
```

There may be an order to the requires clauses. In this case, the `a.length` in
the second clause is undefined if `a` is null. Thus we also need the
condition stated in the first clause, and it must be stated before the
second clause. Reversing the order will result in an error (when arguments are nullable by default):
```
{% include_relative T_requires3.java %}
```
produces
```
{% include_relative T_requires3.out %}
```

Ensures clauses may be mixed in order with the requires clauses, but good,
and clearer, style suggests putting all requires clauses first and then
all ensures clauses.

## **[Preconditions Problem Set](https://www.openjml.org/tutorial/exercises/PreConEx.html)**

