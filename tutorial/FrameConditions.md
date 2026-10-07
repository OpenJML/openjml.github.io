---
title: JML Tutorial - Frame Conditions
---

The [previous lesson](MethodCalls) described the verification process when 
there are multiple methods that call each other. But that lesson left out
an important consideration: how to specify the effects of methods
(these effects are often called "side-effects"), 
which are changes to storage that exists before a method is called
and outlives the method call.

Consider the following example:
```
{% include_relative T_frame1.java %}
```
which produces
```
{% include_relative T_frame1.out %}
```
Note first a new bit of syntax: the `\old` designator. The `increment` methods make a change in state: the value of `counter1` or `counter2` is different after
the method than before it is called and we need a way to refer to their values before and after the call. 
The `\old(E)` syntax evaluates the enclosed expression (`E`)
in the call's pre-state, that is, the state at the beginning 
of the method's execution.
Using `counter1` without the `\old` designator means the value of `counter1` 
in the call's post-state, that is, the state after the call has completed.

Also, why the comparison to `Integer.MAX_VALUE` in the preconditions? That is to avoid [warnings about arithmetic overflow](ArithmeticModes).

Now to the point of this lesson. The two increment methods verify, but 
what is happening in the `test()` method?
First the code initializes `counter1` and `counter2`, which makes the test more  concrete.
After calling `increment1()`, the value of `counter1` has increased by 1; 
the postcondition of `increment1()` says just that and the first assert
statement is readily proved. 

But the second assert statement is not verified. Why not? `increment1()` does not change
`counter2`; however, the problem is that the specification of `increment1()` does not say
that `counter2` is unchanged. One solution would be to add an additional 
ensures clause that states that `counter2 == \old(counter2)`. This specification
would also verify.

However, adding such postconditions is not a practical specification technique. We can't add to `increment1()`'s specification a clause stating that every variable that is visible to a caller is unchanged (in part because some of those locations will not be visible to the method `increment1()`).
Instead we use a *frame condition* whose purpose is to state which memory
locations a method _might_ assign during its execution. 
There are a variety of names for such a frame clause:
JML traditionally uses the keyword `assignable`,
but `assigns`, and `writes` are also permitted.
Note that `modifies` is also an
(implemented) synonym, but in some tools it has a slightly different meaning,
so its use is not recommended.

A method's frame condition states which memory locations might be changed by that method's execution. Anything not mentioned is assumed to be unchanged. In fact, a method
is not allowed to *assign* to a memory location (even with the same value) unless it is listed in the frame condition --- this makes the check for violations of the frame condition, whether by tool or by eye, independent of the values computed.

## Names for Frame Condition Clauses

If there is no explicit frame condition clause in a method's specification (case), then a default is used, namely `assignable \everything;`--- which means exactly that: after a call of this method, any memory location in the state might have been written to and might be changed. It is very difficult to prove anything about a program that includes a call to a method with such a frame condition. Thus *you must include a frame condition for any method that is called within a program*.

In our example above, before we added a frame clause, the effective frame
clause was `assignable \everything`. Then in method `test` the call of
`increment1` is specified as potentially changing every memory location, 
including `counter2` in this example.

You can also write `assignable \nothing`, which means no memory locations 
may be assigned to.

So now our example looks like this:
```
{% include_relative T_frame3.java %}
```
which successfully verifies.

## Memory Location Details

A few more details about the memory locations in a frame condition:
* Local variables, i.e., variables declared in the body of a method,
are not visible to callers (or in a method's specification), so they are not listed in a frame condition.
* The formal arguments of the method are in scope for the frame condition,
just like for the `requires` and `ensures` clauses.
However, these formal arguments cannot be changed by a call (due to the way arguments are passed in Java), but if they are references to objects,
then the fields of those objects could be written to by the method. 
So a method `m(MyType q)` might have a frame condition `assignable q.f;` 
if `f` is a field of `MyType` that is assigned in the body of `m`.
* If a method has no external effects other than its return value, you can specify a frame condition `assignable \nothing;`.

A shorthand way to say that a method `assignable \nothing;` is to designate it `pure`, as in
```
//@ requires ...
//@ ensures ...
//@ pure
public void m() { ... }
```
though there are a few other details to purity --- see the [lesson on pure](MethodsInSpecifications).

## Abbreviations for Sets of Locations

There are also several abbreviations for mentioning sets of locations in specifications:
* `q.*` means all fields of the value of the expression `q`
* `a[i]` for expressions `a` and `i`, means the particular array element `a[i]` (where the values of `a` and `i` are interpreted in the method's pre-state)
* `a[*]` for array expression `a`, means all elements of array `a`
* `a[i..j]` for expressions `a`, `i`, and `j`, means the stated range of array elements, from `i` to `j` inclusive. Also `a[i ..]` means the same thing as `a[i .. a.length-1]`.

## Evaluation of Expressions is in the Pre-State

When a frame condition includes expressions, such as the indices of array expressions, those expressions are evaluated in the call's pre-state, not its post-state. This allows callers of the method to understand the potential effects of a method before calling it.

## Multiple Frame Conditions in a Specification

A frame condition is a method specification clause like `requires` and `ensures`. Thus a method specification may contain more than one such clause.
However, each clause is considered individually and thus each clause
by itself lists the memory locations that may be written to by the method.
As each frame condition clause must be valid on its own, the effect of multiple iframe clauses is the same as one clause with the _intersection_ of the sets of locations given by the separate clauses.
For example,
```
assignable i,j;
assignable i,k;
```
is the same as
```
assignable i;
```
and
```
assignable i;
assignable j;
```
is the same as
```
assignable \nothing;
```

One might think that it would be more convenient if the
result of multiple assignable clauses was the *union* of their contents,
but that is not the case, for historical reasons and
to make reasoning about inheritance of specifications,
which can involve [multiple specification cases](MultipleBehaviors) able to count on what is not assignable by a method without knowing about the specifications of subtypes.[^1] The advice is thus to
*use only one frame condition per specification (case)*, even if that
means the clause has a long list. 

## **[Exercises](https://www.openjml.org/tutorial/exercises/FrameCondEx.html)**

Follow the link in the above heading to work on the exercises on this topic.

## Resources
+ [T_frame1 file](T_frame1.java)
+ [T_frame3 file](T_frame3.java)

## Footnotes

[^1]: Reasoning that can ignore subtypes is called "supertype abstraction", see Gary T. Leavens and David A. Naumann, "Behavioral Subtyping, Specification Inheritance, and Modular Reasoning", in _ACM Transactions on Programming Languages and Systems_, vol. 37, num. 4 (August), 2015, pp. 13:1-13:88, http://doi.acm.org/10.1145/2766446.
