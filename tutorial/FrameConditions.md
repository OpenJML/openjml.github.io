---
title: JML Tutorial - Frame Conditions
---

The [previous lesson](MethodCalls) described the verification process when 
there are multiple methods that call each other. But that lesson left out
an important consideration: how to specify side-effects of methods.

Consider this example:
```
{% include_relative T_frame1.java %}
```
which produces
```
{% include_relative T_frame1.out %}
```
Note first a new bit of syntax: the `\old` designator. The `increment` methods make a change in state: the value of `counter1` or `counter2` is different after
the method than before and we need a way to refer to their values before and after. The `\old` syntax means to determine the value of the enclosed expression
in the pre-state, that is, the state at the beginning of the method's execution.
`counter1` without the `\old` designator means the value of `counter1` in the
post-state, the state after the method has completed.

Also, why the comparison to `Integer.MAX_VALUE`? That is to avoid warnings about arithmetic overflow. We'll get to that topic [later](ArithmeticModes).

Now to the point of this lesson. The two increment methods verify, but 
what is happening in the test method?
First we assume some values for `counter1` and `counter2`. This is just to give
a concrete starting point.
After calling `increment1`, the value of `counter1` has increased by 1; 
the postcondition of `increment1` says just that and the first assert
statement is readily proved. 

But the second assert statement is not. Why not? `increment1()` does not change
`counter2`. The problem is that the specification of `increment1()` does not say
that `counter2` is unchanged. One solution would be to add an additional 
ensures clause that states that `counter2 == \old(counter2)`. This specification
verifies as correct.

But this is not a practical solution. We can't add to `increment1()`'s specification a clause stating that every visible variable is unchanged.
Instead we use a *frame condition* whose purpose is to state what memory
locations a method might have modified. There are a variety of names for
the frame clause: traditionally it is `assignable`, but `assigns` is also permitted.
Note that `modifies` is also an
(implemented) synonym, but in some tools it has a slightly different meaning,
so its use is not recommended.

The frame condition states which memory locations might be changed by the method at hand. Anything not mentioned is assumed to be unchanged. In fact, a method
is not allowed to *assign* to a memory location (even with the same value) unless it is listed in the frame condition --- this makes the check for violations of the frame condition, whether by tool or by eye, independent of the values computed.

So now our example looks like this:
```
{% include_relative T_frame3.java %}
```
which successfully verifies.

A few more details about the memory locations in a frame condition:
* One does not need to list variables that are local to the body of a method;
those are not visible in the specification and they are not part of the 
program state outside of the method.
* The formal arguments of the method are in scope for the frame condition,
just like for the `requires` and `ensures` clauses. The formal arguments \
themselves cannot be changed by a method, but if they are references to objects,
their fields might be written to by a method. So a method `m(MyType q)`
might have a frame condition `assigns q.f;` if `f` is a field of `MyType`
that is written to in the body of `m`.
* If there are no effects of a method, you can specify a frame condition `assigns \nothing;`
* `q.*` for an expression `q` means all fields of q
* `a[i]` for expression `a` and `i` means that particular array element
* `a[*]` for array expression `a` means all elements of that array
* `a[i..j]` for expressions `a`, `i`, and `j` means the stated range of array elements, from `i` to `j` inclusive.

If there is no frame condition at all, then a default is used, namely `assigns \everything;`--- which means exactly that: after a call of this method, any memory location in the state might have been written to and might be changed. It is very difficult to prove anything about a program that includes a call to a method with such a frame condition. Thus  
*you must include a frame condition for any method that is called within a program*

A shorthand way to say that a method `assigns \nothing;` is to designate it `pure`, as in
```
//@ requires ...
//@ ensures ...
//@ pure
public void m() { ... }
```
though there are a few other details to purity --- see the [lesson on pure](Pure).

There are two other points to know about frame conditions. First, where a frame condition clause includes expressions, such as the indices of array expressions, those expressions are evaluated in the pre-state, not the post-state.

Second, a frame condition is a method specification clause like `requires` and `ensures`. A method specification may contain more than one such clause.
However, note that each cluase is considered individually. That is, each clause
by itself lists the memory locations that may be written to by the method.
As each frame condition clause must be valid on its own, the effect of multiple clauses is the same as one clause with the intersection of the sets of locations given by the separate clauses.
For example,
```
assigns i,j;
assigns i,k;
```
is the same as
```
assigns i;
```
and
```
assigns i;
assigns j;
```
is the same as
```
assigns \nothing;
```
Admittedly,  it would be much more convenient and perhaps intuitive if the
result of mutiple assigns clauses was the *union* of their contents, but that is
not the case, for historical reasons. The advice is then to
*have only one frame condition clause per specification (case)*, even if that
means the clause has a long list. (All the method specifications in the
tutorial lessons so far have just one specification case; an advanced lesson
presents [multiple specification cases](SpecificationCases).)


## **[Frame Consitions Problem Set](https://www.openjml.org/tutorial/exercises/FrameCondEx.html)**

