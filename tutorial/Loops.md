---
title: JML Tutorial - Specifying Loops
---

In the current state of deductive verification technology it is essential that all loops have loop specifications.

A loop typically has the following steps:
* some initialization code
* a loop condition, which if false causes the control flow to exit the loop
* a loop body 
* an update statement that typically moves a loop index variable to the next value
* and then control returns to testing the loop condition

There are four aspects of a loop that typically need to be specified:
1. a constraint on the expected values of the loop index (including just before exiting the loop), given by a loop invariant
2. an inductive predicate that says what has been accomplised so far by the loop, given also by a loop invariant
3. a loop frame condition that says which memory locations are modified by any iteration of the loop body
4. a termination condition (with an integer type) that enables proving that the loop will terminate

## For loops

Here is a typical, simple loop with specifications:
```
{% include_relative T_forloop.java %}
```

The loop has a loop index `i` that counts up from 0, exiting the loop when it reaches the length of the input array. 
On each iteration, the loop body sets the `i`'th element of the array to the value of the index.

* The first loop invariant (`maintaining` clause) states what values the loop index will have. If the range is too small,
then the desired property for the whole array will not be provable. If the range is too large, then OpenJML
will attempt to check the loop body for these out of range values, likely reporting errors. Very importantly, 
the range must include the value the loop index will take on when it exits the loop. So in this case the range is
`0 <= i <= a.length`, not `0 <= i < a.length`.
* The second `maintaining` clause states what has been accomplished in `i` iterations, namely that each arrray element up
to (but not yet including) `i` is initialized to the expected value. This invariant is very typically a `forall`expression.
* The third specification clause states which memory locations are modified by the loop body.
* And the fourth line is a quantity that must decrease on each iteration but always be non-negative when the loop body is executed.
If those conditions are satisfied (and the verifier checks them), then we know that the loop will eventually terminate.

It may help to understand what the verifier tries to prove about a loop. It proves three things:
* First, when control flow reaches the loop (after the loop initialization), the loop invariants must be true. In the example above,
`i` is `0` at this point, so both `maintaining` clauses are true.
* Second, it
  * assumes it knows nothing about the memory locations in the loop frame condition (which includes the loop index)
  * it then assumes that the loop invariants hold 
  * it also establishes that the value of the termination expression at the beginning of the loop body is non-negative
  * and then assumes that the loop condition is true
  * it then applies the actions of the loop body
  * and does the update step
  * and the result must satisfy the loop invariants again (with the updated value of the loop index)
  * and also the termination expression must have decreased
* Third, it assumes the first two steps above but that the loop condition is false and goes on to reason about any program steps and postconditions that follow the loop.

In the example above, the second proof obligation assumes `0 <= i <= a.length` and `\forall int k; 0 <= k < i; a[k] == k;` and
`(i < a.length)`, and then applies `a[i]=i` and `i++`, and proves `\forall int k; 0 <= k < i'; a[k]==k`, where `i'` is the updated `i`.

It also must prove that `a.length-i` is non-negative at the start of the loop body and that after the loop index update that value is greater  than
the new value of the expression, namely `a.length-i'`.

The third proof obligation assumes `0 <= i <= a.length` and `\forall int k; 0 <= k < i; a[k] == k;` and `!(i < a.length)`, from which it can prove the `assert` statement.

## For-each loops

Java also has a loop syntax that does not have any loop index. In that case, the built-in variable `\count` can be used --- its value is the number of loop
body executions so far. In the for loop above, it would have the same value as `i`.

Here is a typical for-each loop:
```
{% include_relative  T_foreach.java %}
```
Note that the (second) loop invariant states that so far (up to array index `\count`) all array elements are positive. That is because at the beginning of any loop iteration,
all elements seen have been positive. As soon as a non-positive element is seen, the loop exists prematurely, but the verifier can follow this control flow to prove that 
the postcondition is valid for either exit.

Note also the use of `\count` as a stand-in for a loop counter and the use of `\nothing` to say that nothing is modified in the loop body, other than `\count`, which is always included as a modified variable.

## While loops

A while loop generally follows the same pattern as a traditional for loop. Here we give another example that does not have an explicit loop index.
```
{% include_relative  T_whileloop.java %}
```

## Do-while loops

Do-while loops can be tricky to specify because they do not follow the same update-at-the-start of a loop pattern. Here is a simple example.
```
{% include_relative  T_dowhile.java %}
```
Here the order of assumptions is this:
* assume the loop invariants
* execute the body
* do the loop test (which in this example incorporates the loop update)
* check that the loop invariants still hold

Because the loop update and test are at the end of the body, the initial loop invariant only reflects the possible values at the start of the loop; the final increment and exit from the loop happen without 
checking the loop invariant again. So the loop invariant here is `0 <= i < 10`, not `0 <= i <= 10`.


## Loop verification errors

The examples above all verify, so here are some examples showing the kinds of verification errors that are produced by erroneous specifications.

### Loop initialization error

In this example, the initial value of `i` does not satisfy the first loop invariant:
```
{% include_relative  T_LoopInitError.java %}
```
producing this output:
```
{% include_relative  T_LoopInitError.out %}
```

### Loop body error
In this example, a loop invariant cannot be proven after execution of the loop body. To help see why, a `show` statment (cf. TBD) is included, which shows that the problem occurs when
the loop index is one less than the array length. Indeed, in that case, when the loop index is incremented on the final loop iteration, its value will be the array length, and then the
first loop invariant will not hold. Interestingly, there is also a loop initialization error. Why? Because if `a.length` is 0, then the initial value of `i` does not satisfy the first 
loop invariant.
```
{% include_relative  T_LoopBodyError.java %}
```
produces
```
{% include_relative  T_LoopBodyError.out %}
```
(The order of error messages and the specific values returned by show are non-deterministic.)

### Loop decreases error
If the `decreases` expression does not decrease, one receives the error shown in this example:
```
{% include_relative  T_LoopDecreasesError.java %}
```
with the output
```
{% include_relative  T_LoopDecreasesError.out %}
```
### Negative termination value
If the termination expression can be negative at the start of a loop, one gets this behavior:
```
{% include_relative  T_LoopNegativeError.java %}
```
which produces
```
{% include_relative  T_LoopNegativeError.out %}
```

## **[Specifying Loops Problem Set](https://www.openjml.org/tutorial/exercises/SpecifyingLoopsEx.html)**
