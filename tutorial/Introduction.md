---
title: JML Tutorial - What is Deductive Verification?
---

We know you are eager to just try out some code, but here is a quick set of points to be sure you understand where this tutorial is headed:
* JML is a language for writing specifications of the behavior of Java programs.
* OpenJML is tool for checking that the Java implementation of the program is consistent with its JML specifications.
* This checking can either be done:
   * statically (without running the program) -- sometimes called Deductive Verification in the literature, but OpenJML calls it ESC (Extended Static Checking), or
   * dynamically by running test cases through an instrumented program, called RAC (Runtime Assertion Checking).

When a program is _statically verified_ to be _correct_ using ESC, it means that for every possible run of the program, if the starting state satisfies the specification, then the program's behavior follows the specification; this will be guaranteed in all possible cases (assuming that the compiler and computer work as intended).

The tutorial is mostly focussed on ESC (though there are lessons on RAC as well):
* The ESC approach is akin to symbolically executing a method for every possible legal set of inputs (every possible pre-state), so when the method verification is successful, the result is a more powerful statement of correctness than one can obtain by testing/RAC
* Each method is checked on its own, using the specifications (not the implementations) of the other methods; this kind of modular verification is a valid approach as long as, eventually, all methods verify successfully (and it can be proved that the program terminates).

The tutorial walks you through basic JML, with plenty of examples that you can execute using OpenJML.
There are also exercises for you to test your understanding of the tutorial material.

Have fun!


