---
title: JML Tutorial - Multiple Method Behaviors
---

## Multiple Behaviors

So far our method specifications have been simple sequences of clauses: pre-, frame- and post-conditions.
But, as method behaviors become more complex, it is helpful to separate the method specification into multiple _specification cases_, which can be specified as different _behaviors_ in JML.

Each behavior is a simple sequence of clauses, with its own preconditions, postconditions, and frame, etc.
That is, specification can consist of multiple behaviors, each called a "specification case," connected by the keyword `also`.
For example,
```
{% include_relative T_MultipleBehaviors1.java %}
```
The specification here is a bit more verbose than the code, but it separates out the cases in a more readable manner than the code.
Furthermore, by writing the goal of the method in two different ways, an erroneous exchange of 'a' for 'b' or '<=' for '>=' is readily caught by OpenJML.

There are a few points to note:

* There is no order to the behaviors; they can be written in any order that is understandable.
* Every behavior applies on its own and must hold by itself --- there is no if-then-else relationship or ordering among them. If a behavior's preconditions hold,
then its frame and postconditions must hold, independent of what any other behavior says.
* The effective precondition for each behavior is the conjunction (with `&&`) of the preconditions for that behavior. The effective precondition for the entire combination of all of the multiple behaviors is the disjunction (with `||`) of the effective preconditions of the individual behaviors. Consequently, at the point where such a method is called, at least one, but by no means necessarily all, of the behaviors must have an effective precondition that is true.
* When a precondition holds, the corresponding frame condition given in that specification case must hold. (If it did not, then reasoning about using a specification case with that precondition would be invalid.) Therefore, if two preconditions both hold, then the effective frame condition is the intersection of those two frame conditions (for such a pre-state). So it is best to use only one `assignable` clause for each specification case, as described in [the tutorial about frame conditions](FrameConditions).

In our example, if `a`, `b`, and `c` are all equal, then the precondiition (`requires` clause) of all three behaviors is true; in this case the postconditions of each of these behaviors must also be true.
Fortunately they all agree in that case.
(In addition, since the method is pure, each specification case has an implicit frame condition of `assignable \nothing`, and so they all satisfy that frame condition.)

As an experiment, this example introduces a mistake in one behavior:
```
{% include_relative T_MultipleBehaviors2.java %}
```
which yields this result
```
{% include_relative T_MultipleBehaviors2.out %}
```
The verification failure message points to the first specification case's postcondition, on line 4, which narrows our debugging to the relationship between that specification case and the code. A little inspection shows a typo at the end of the first specification case's precondition, on line 3.

## Separating Normal from Exceptional Behaviors

A very common use of multiple behaviors is to separate normal execution from exceptions. For example,
```
{% include_relative T_MultipleBehaviors3.java %}
```
The code in this example does some parameter validation checks. If the checks fail, then an exception is thrown.
The method could go on to do something useful, but for this example, it just returns.
There are thus two behaviors. 
* The first specification case is the normal case,
where the arguments satisfy the checks and the method just returns normally;
that is the first behavior --- the ensures postcondition is `true` (which could be omitted entirely), which just states that
the method is allowed (but not required) to return normally; the signals postcondition is false, which states that under
these preconditions, the method is _not_ allowed to throw an exception.
* The second behavior is the exceptional case. Here one or the other of the argument validation checks fails. In this case, the postcondition is `ensures false`, which means that the method is _not_ allowed to return normally; the default, omitted, `signals (Exception x) true` clause says that an exception is allowed; the `signals_only` clause says that if there is an exception it must be an `IllegalArgumentException` (the only one listed).

We could even separate out two kinds of exceptions:
```
{% include_relative T_MultipleBehaviors4.java %}
```
Now the `signals_only` clause allows the two kinds of exceptions, although the specification does not say when each one is thrown. We could go to one more level of specification detail to stipulate that each exception is thrown just when the appropriate argument validation check fails. Try specifying that as an exercise. One could try separating the specification of when each exception should be thrown into two specification cases, but that raises the question: what if both specification cases have preconditions that are true (that is, what if both checks fail)? Should the specification state which exception is thrown in preference to the other? If it does specify that, then it is constraining the implementation, perhaps overly so. However, if it does not, and both preconditions hold, then the specification would say that the method must throw both exceptions, which is impossible. (So such a specification would be "unsatisfiable.")

## <a name="SpecializedBehaviors"></a>Specialized Behaviors

The normal and exceptional behaviors illustrated in the previous section are very common, so much so that they have specialized syntax: `normal_behavior` and `exceptional_behavior`. We can rewrite the previous example as 
```
{% include_relative T_MultipleBehaviors5.java %}
```
The `normal_behavior` heading implies that no exception is allowed (which is equivalent to specifying `signals false`); the `exceptional_behavior` heading says that normal termination is not allowed (`ensures false`).
A behavior that is neither of these is a simple `behavior`, which is the default when there is no heading.

One other point: in a class these behavior keywords need to have a specified visibility (declared by a visibility keyword); almost always, as in the example above, the visibility is the same as the method. However, the absence of a visibility modifier means `package` visibility, just as in Java the absence of a visibility modifier on the method declaration would give the method package visibility. On the other hand, if there is no specialized behavior keyword, then there is no place for the visibility keyword; in that case, the visibility default is the same as the visibility of the method.

## Summary of Specification Cases

To summarize, a method may have multiple specification cases. 
* They are separated/connected by the `also` keyword. 
* Each specification case consists of an optional heading followed by a series of method specification clauses
* There are four styles of behavior headings. Here `V` is a visibility modifier: one of `public`, `protected`, `private`, or absent (meaning package visibility)
  * The most general: `V behavior`
  * Normal exit only: `V normal_behavior`
  * Exit by exception only: `V exceptional_behavior`
  * The most common: no behavior heading, which means `V behavior` with the visibility `V` being the same as the method's visibility.


## Nested Clause Groups

We will just mention an advanced topic here: nested clauses groups within a method specification. For details see [the JML Reference Manual](https://www.openjml.org/documentation/JML_Reference_Manual.pdf).
Here is an example:
```
  requires P1;
  assignable F1
  ensures Q1;
  {|
     requires P2;
     ensures Q2;
  also
     requires P3;
     ensures Q3;
  |}
```
which is a less repetitious way of specifying a method than the equivalent:
```
  requires P1;
  requires P2;
  assignable F1;
  ensures Q1;
  ensures Q2;
also
  requires P1;
  requires P3;
  assignable F1;
  ensures Q1;
  ensures Q3;
```

## **[Exercises](https://www.openjml.org/tutorial/exercises/MultMethodBehaviorEx.html)**

Follow the link in the above heading to work on the exercises on this topic.

## Resources
+ [T_MultipleBehaviors1 file](T_MultipleBehaviors1.java)
+ [T_MultipleBehaviors2 file](T_MultipleBehaviors2.java)
+ [T_MultipleBehaviors3 file](T_MultipleBehaviors3.java)
+ [T_MultipleBehaviors4 file](T_MultipleBehaviors4.java)
+ [T_MultipleBehaviors5 file](T_MultipleBehaviors5.java)
