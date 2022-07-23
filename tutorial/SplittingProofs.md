---
title: JML Tutorial - Splitting up proofs
---

By default, OpenJML attempts to verify each method on its own and converts the entire method into one verification condition that contains all of the implicit and explicit assertions needed to verify that a method's specification and implementation agree. Treating each assertion individually or even in groups would require duplicating effort within the solver. Solvers are highly engineered for large problems and for speed.

Nevertheless, sometimes it is helpful to break up a method's verification condition into pieces, for understanding, for debugging, or because the method is large. This lesson describes some mechanisms for doing that.

## The halt statement

The halt statement, `//@ halt;`, may be placed anywhere a statement may be placed in a Java program. Its effect is to halt translation of the method at that point. So the resulting verification condition and proof will only contain assertions from the method preconditions and beginning of the body to that point in the body. If the halt statement is in a branch, then other branches will be translated all the way to the end of the method and its postconditions unless they too contain halt statements.

As a result the verification condition is smaller, any proof is quicker, and any debugging effort is focussed on the portion of the program up to that point. Once that portion of the program is correct and understood, the halt statement can be moved further down in the program and the process repeated.
Obviously this is only a debugging technique; in the end, verification must be successful without any halt statements.

Note that one could obtain a similar effect by inserting a `assume false;` statement into the method. This also has the effect that any assertions after
this statement are not considered by the prover. However, it does not have the effect of making the verification condition smaller and its effect is not
as intuitive.

Here is a simple example with some obvious seeded errors:
```
{% include_relative T_halt1.java %}
```
produces
```
{% include_relative T_halt1.out %}
```
(The failures are reported in a non-deterministic order.)
Adding two halt statements before the assertions omits both assertions and the postconditions from analysis:
```
{% include_relative T_halt2.java %}
```
has no errors.
Removing one halt statement and leaving the other will trigger one of the assertions and the postcondition.
```
{% include_relative T_halt3.java %}
```
produces
```
{% include_relative T_halt3.out %}
```

## The split statement and --split option

The halt statement above makes a kind of horizontal cut in the top-to-bottom flow of a method body. In contrast, the `split` statement makes a kind of vertical division. Consider an `if` statement: the logical analysis has to consider both branches; the split statement directs the prover to consider
each branch individually (as if there were a `halt` statement at the beginning of the other branch). The program can be split at several points, by placing a `//@ split;` statement immediately before the relevant control construct:
* split on the two branches of an `if`
* split on the cases of a `switch` statement (but not a switch expression)
* split on a loop condition
* split on a block specification (see the next section)
* split on a condition

For the last option, the split statement contains a condition: `//@ split <predicate>;` and the split is done assuming the condition is true and false respectively. A method may have multiple `split` statements, which results in a multiplicative number of splits to prove.

Like the `halt` statement, the `split` statement reduces the size of the verification condition. But unlike the `halt` statement, `split` statements may be left in the method, because, so long as each split case verifies, all execution paths will have been properly verified.

Each split of the method body has a alphabetic designator, like 'ABA', which tells which branch of each split encountered is taken. `openjml` can be run with the option `--split=<designators>` where the value of the option is a comma-separated list of such designators; verification is then attempted for just those split combinations, in turn.

Here is a bare-bones example:
```
{% include_relative T_split1.java %}
```
which produces
```
{% include_relative T_split1.out %}
```
First a few details:
* We use the `--progress` option so we can see what is happening (always use that option with splits, at least until they are all successful)
* The `--split` option ... TODO
* In the case of a loop, the split statement is put between the loop specification and the loop itself.

Now note that four splits were produced in the example above. First there is a split at the if-statement, `A` for the _then_ branch, `B` for the _else_ branch. Then, within the _then_
branch, there is a switch statement with three cases, which will be labeled `A`, `B`, and `C`. So we have four splits with designators, `AA`, `AB`, `AC`, `B`.
OpenJML attempts verification for each of these in turn. 
* Case AA fails; the `show` statement tells us that the value of `i` is `1`, as we expect.
* Case AB succeeds, so we don't get a counterexample, but we surmise that `i` must be `2`.
* Case AC fails again, now with an `i` that is positive but not `1` or `2`.
* Case B fails, now with some `i` that is non-positive and `p` is false.

We can rerun this for just two of the splits by using the option `--split=AB,B`, giving
```
{% include_relative T_split2.out %}
```

## Block specifications

A final way to reduce the size of verification conditions is to use _block specifications_. This is a technique in which specifications, similar to method specifications, are written for a portion of a method body. Schematically,
```
{
    pre-stuff
    //@ requires P
    //@ ensures Q
    {
       block
    }
    post-stuff
}
```
Here the specification summarizes the effect of the statement (usually a block) that immediately follows. This enables OpenJML to break the proof into two pieces: first one in which the specification is verified against the statement:
```
{
    ... symbolically execute pre-stuff
    prove that P holds
    ... symbolically execute block
    prove that Q holds
}
```
And then second we can use the specification to summarize the block and go on to prove any assertions in 'post-stuff':
```
{
    ... symbolically execute pre-stuff
    prove that P holds
    assume that Q holds
    ... symbolically execute post-stuff
}
```

As you can see from the sketches above, the precondition is not really neeeded; it is just like an assert. The important parts are an `assignable` clause saying what is modified in the block and `ensures` and `signals` clauses that say what the effect of the block is. Other method specification clauses may appear in more complex scenarios -- see the OpenJML Users' Guide for more detail.

The statement specification here can be the specification of
* the next single statement
* most commonly, the next single statement which is a block
* or a sequence of statements (in the same scope) bounded by the `//@ begin;` and `//@ end;` JML statements.

The last case is used when the desired sequence of statements is not contained within a block, is more than one statement, and one cannot modify the code by putting in a pair of braces, or such a pair of braces would change the scope of declarations.

The two pieces of the proof are an obvious case for splitting the proof. In fact that is the default behavior, because the main purpose of a statement specification, along with adding some documentation and clarity, is to be able to divide up the proof. However, if you are writing the software and it seems a statement specification is needed, you should probably consider breaking up the method into multiple methods; if you are verifying legacy code that cannot be modified, then a statement specification can be very handy. It is also helpful as a means of separating out a portion of the method body that is very difficult to prove.

Here is a worked example.

TBD



