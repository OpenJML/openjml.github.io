# Tutorial

These pages provide a quick introduction to JML (the Java Modeling Language) and 
OpenJML (a tool that implements checks of the specifications written in JML for Java programs)
in the form of an on-line tutorial.
Aside from the installation instructions, you can read the _General_ pages as needed and dive right in to the section on Method Specifications.

The tutorial does not cover all aspects of JML and OpenJML. See also the 
[JML Reference Manual](../documentation/JML_Reference_Manual.pdf)
and the [OpenJML Reference Manual](../documentation/OpenJMLUserGuide.pdf).

**Tutorial Material** All of the examples in this tutorial are part of the installation
zip file, in the top-level `tutorial` folder. For example, the `T_ensures1`
example is present as the `T_ensures1.java` file. From within the tutorial
folder, you can run the example using `../openjml -esc T_ensures1.java`.
Examples that produce output (e.g., error messages) have a corresponding `.out`
file containing the expected output.
The command-line to run the example is shown in the first line of the
example code; just add the appropriate path to the `openjml` command.


* General
  * [Installation](Installation)
  * [Execution](Execution)
  * [Syntax](Syntax)

* Simple Method Specifications
  * [Postconditions](Postconditions)
  * [Preconditions](Preconditions)
  * [Assert statements](AssertStatement)
  * [Assume statements](AssumeStatement)
  * [JML Expressions](Expressions)
  * [Well-defined Expressions](WellDefinedExpressions)
  * [Verifying Method Calls](MethodCalls)
  * [Frame Conditions](FrameConditions)

  * [Using Method Calls in Specifications](MethodsInSpecifications)
  * [Arithmetic](ArithmeticModes)
  * [Null and non-null](Nullness)
  * [Visibility](Visibility)
  * [Specifying Loops](Loops)
  * [Specifying Exceptions](Exceptions)

* Inheritance
  * [Inheriting Specifications](InheritingSpecifications)
  * [Abstracting Frame Conditions --- Datagroups](Datagroups)
  * [Model Methods](ModelMethods)
  
* [Managing proofs](ManagingProofs)

* [Debugging Techniques](Debugging)

* Runtime Assertion Checking
  * [Compilation and Execution](RACCompilation)
  * [RAC Exit Code](RACExit)
  * [RAC Output](RACOutput)
  * [RAC and Java checks](RACJavaChecks)

* Advanced topics
  * [Reasoning about Types](TYPE)
  * [Modularizing Specifications](SpecificationCases)
  

<!--
embedded comments
Java annotations
heavyweight method specs
arithmetic modes
invariants
JML types
JML expressions

reasoning about lambda expressions
-->
