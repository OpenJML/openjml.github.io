---
title: JML Tutorial - Multiple Method Behaviors
---

## Multiple behaviors

So far our method specifications have been simple sequences of clauses: pre-, frame- and post-conditions.
But as methods become more complex it is helpful to separate the method specification into multiple 
 _specification cases_, which can be thought of as different _behaviors_.

Each behavior is a simple sequence of clauses, with its own preconditions, postconditions, etc.
The specification can consist of multiple behaviors, connected by the keyword `also`.
For example,
```
{% include_relative T_MultipleBehaviors1.java %}
```
The specification here is a bit more verbose than the code, but it separates out the cases a bit more readably than the code does.
Furthermore, by writing the goal of the method in two different ways, an erroneous exchange of 'a' for 'b' or '<' for '>' is readily caught by OpenJML.

There are a few points to note:
* There is no order to the behaviors; they can be written in any order that is understandable.
* Every behavior applies on its own and must hold by itself --- there is no if-then-else  among them. If a behavior's preconditions hold,
then its postconditions must hold, independent of what any other behavior says.

In our example, if `a`, `b`, and `c` are all equal, then the precondition (`requires` clause) of each of the three behaviors is true.
So the postconditions of each of the behaviors must also be true.  Fortunately they all agree.

As an experiment, this example introduces a mistake in one behavior:
```
{% include_relative T_MultipleBehaviors2.java %}
```
which yields this result
```
{% include_relative T_MultipleBehaviors2.out %}
```
The verification failure message points to the postcondition on line 4, which narrows our debugging to the relationship between
that behavior and the code. A little inspection shows a typo at the end of the precondition on line 3.

## Separating normal from exceptional behaviors

A very common use of multiple behaviors is to separate normal execution from exceptions. For example,
```
{% include_relative T_MultipleBehaviors3.java %}
```
The code in this example does some parameter validation checks. If the checks fail an exception is thrown.
The method could go on to do something useful, but for this example, it just returns.
There are then two behaviors. 
* In the normal case the arguments satisfy the checks and the method just returns normally;
that is the first behavior --- the ensures postcondition is `true` (which could be omitted entirely), which just states that
the method is allowed (but not required) to return normally; the signals postcondition is false, which states that under
these preconditions, the method is _not_ allowed to throw an exception.
* The second behavior is the exceptional case. Here one or the other of the argument validation checks fails. In this case, the postcondition is `ensures false`, which means that the method is _not_ allowed to return normally; the default, omitted, `signals true` clause says that an exception is allowed; the `signals_only` clause says that if there is an exception it must be an `IllegalArgumentException` (the only one listed).

We could even separate out two kinds of exceptions:
```
{% include_relative T_MultipleBehaviors4.java %}
```
Now the `signals_only` clause allows the two kinds of exceptions, although the specification does not say when each one is thrown. We could go to one more level of specification detail to stipulate that each exception is thrown just when the appropriate argument validation check fails. Try it as an exercise. There is a question though: what if both checks fail? Should the specification state which exception is thrown in preference to the other? If it does it is constraining the implementation, perhaps overly so.

## Specialized behaviors

The normal and exceptional behaviors illustrated in the previous section are very common, so much so that they have specialized syntax: `normal_behavior` and `exceptional_behavior`. We can rewrite the previous example as 
```
{% include_relative T_MultipleBehaviors5.java %}
```
The `normal_behavior` heading implies that no exception is allowed (`signals false`); the `exceptional_behavior` heading says that normal termination is not allowed (`ensures false`).
A behavior that is neither of these is a simple `behavior`, which is the default when there is no heading.

One other point: any one of the behavior keywords needs a visibility keyword; almost always, as in the example above, the visibility is the same as the method. The absence of a visibility modifier means `package` visibility, just as the absence of a visibility modifier on the method declaration.

## Summary of specification cases

To summarize, a method may have multiple specification cases. 
* They are separated/connected by the `also` keyword. 
* Each specification case consists of an optional heading followed by a series of method specification clauses
* There are four styles of headings. Here `V` is a visibility modifier: one of `public`, `protected, `private`, or absent, meaning package visibility
  * The most general: `V behavior`
  * Normal exit only: `V normal_behavior`
  * Exit by exception only: `V exceptional_behavior`
  * The most common: no heading, which means `V behavior` with the visibility `V` being the same as the method's visibilty


## Nested clause groups

We will just mention an advanced topic here: nested clauses groups within a method specification. For details see the JML Reference Manual.
Here is an example:
```
  requires P1;
  ensures Q1;
  {|
     requires P2;
     ensures Q2;
  also
     requires P3;
     ensures Q3;
  |}
```
which is a less repetitious representation of the equivalent
```
  requires P1;
  requires P2;
  ensures Q1;
  ensures Q2;
also
  requires P1;
  requires P3;
  ensures Q1;
  ensures Q3;
```

## **[Multiple Method Behavior Problem Set](https://www.openjml.org/tutorial/exercises/MultMethodBehaviorEx.html)**
