---
title: JML Tutorial
---
<i>Last Modified: <script type="text/javascript"> document.write(new Date(document.lastModified).toUTCString())</script></i>

These pages provide a quick introduction to JML (the Java Modeling Language) and 
OpenJML (a tool that checks specifications written in JML for Java programs)
in the form of an on-line tutorial.

You should 
* read the brief [What is Deductive Verification](Introduction) page to clearly understand the overall concept of deductive verification
* follow the installation/execution/syntax instructions just enough to get you going
* start with the Simple Method Specification sequence, but
* branch out into other topics as you are interested

```diff
! This tutorial is a Work In Progress (March 2022).
! Expect lots of editing and new pages.
```

The tutorial does not cover all aspects of JML and OpenJML. See also the 
[JML Reference Manual](../documentation/JML_Reference_Manual.pdf)
and the [OpenJML User Guide](../documentation/OpenJMLUserGuide.pdf).

Many tutorial pages have links to supplementary exercises. A table of contents for all the exercises is collected [here](./exercises/exercises).

Also note that there are additional standalone examples in a sibling page under [Examples](../examples).

**Tutorial Material** All of the examples in this tutorial are part of the OpenJML installation
zip file, in the top-level `tutorial` folder. For example, the `T_ensures1`
example is present as the `T_ensures1.java` file. From within the tutorial
folder, you can run the example using `../openjml -esc T_ensures1.java`.
Examples that produce output (e.g., error messages) have a corresponding `.out`
file containing the expected output.
The command-line to run the example is shown in the first line of the
example code; just add the appropriate path to the `openjml` command.


* [What is Deductive Verification](Introduction)
  * [Installation](Installation)
  * [Execution](Execution)
  * [Syntax](Syntax)

* Simple Method Specifications
  * [Postconditions](Postconditions)
  * [Preconditions](Preconditions)
  * [Specifying Exceptions](SpecifyingExceptions)
  * [Verifying Method Calls](MethodCalls)
  * [Frame Conditions](FrameConditions)
  * [Method Specifications: old clauses and clause ordering](OldAndOrdering)
  * [Multiple Method Behaviors](MultipleBehaviors)
  * [Minimizing replicated specifications --- initially, constraint, invariant clauses](InitiallyConstraint)
  * [Specifying Constructors](Constructors)
  * [Using Method Calls in Specifications](MethodsInSpecifications)
  * [Visibility](Visibility)
* JML Expressions
  * [JML Expressions](Expressions)
  * [Well-defined Expressions](WellDefinedExpressions)
  * [Arithmetic](ArithmeticModes)
  * [Null and non-null](Nullness)
* [Method Body Specifications](SpecStatements)
  * [Assert statements](AssertStatement)
  * [Assume statements](AssumeStatement)
  * [Specifying Loops](Loops)
  * [Ghost variables and computations](Ghost)

* Inheritance
  * [Inheriting Specifications](InheritingSpecifications)
  * [Abstractions using Model Fields and Datagroups](ModelFields)
  * [Abstractions using Model Methods](ModelMethods)

* [Object Invariants](Invariants)

* [Built-in mathematical types for specifications](BuiltinTypes)
  * [\bigint](type-bigint)
  * [\real](type-real)
  * [\set](type-set)
  * [\seq](type-seq)
  * [\map](type-map)
  * [\string](type-string)
  * [\range](type-range)
  * [\TYPE](type-TYPE)
  
* [Managing proofs](ManagingProofs)
  * [Choosing what files and methods to verify](MethodSelection)
  * [Limiting time](TimeAndErrorLimits)

* [Debugging Techniques](Debugging)
  * [Inspecting Counterexamples](InspectingCounterexamples)
  * [Splitting up proofs](SplittingProofs)
  * [Adding Logical Information](Lemmas)
  * [Checking Feasibility](Feasibility)

* Runtime Assertion Checking
  * [Compilation and Execution](RACCompilation)
  * [RAC Exit Code](RACExit)
  * [RAC Output](RACOutput)
  * [RAC and Java checks](RACJavaChecks)

* Advanced topics
  * [Specification (.jml) files](SpecificationFiles)
  * [Java @-annotations for JML](JavaAnnotations)
  * [JML Errors and Java Exceptions](JavaErrorsAndExceptions)
  * [Recommends clauses](Recommends)
  * [Reasoning about bit-wise operations](BitVectors)
  * [Reasoning about Floating Point operations](FloatingPoint)
  * [Reasoning about Enums](Enums)
  * [Reasoning about Records](Records)
  * [Reasoning about Lambda Functions](Lambdas)
  * [Reasoning about Streams](Streams)
  * [Reasoning about Types](TYPE)
  * [Reasoning about locks](Locks)
  * [Reasoning about recursive functions and data structures](Recursion)
  * [Reasoning about non-deterministic functions and volatile variables](Nondeterminism)
  * [Reasoning about termination](Termination) 

