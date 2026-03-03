---
title: JML Tutorial - What is Deductive Verification?
---

We know you are eager to just try out some code, but here is a quick set of points to be sure you understand where this tutorial is headed:
* JML is a language for writing specifications of the behavior of Java programs.
* OpenJML is tool for checking that the Java implementation of the program is consistent with its JML specifications.
* This checking can either be done:
   * statically (without running the program) -- called Deductive Verification, - DV or ESC (Extended Static Checking), or
   * dynamically by running test cases through an instrumented program - RAC (Runtime Assertion Checking).

The tutorial is mostly focussed on DV/ESC (though there are lessons on RAC as well):
* The DV approach is akin to logically symbolically executing a method for every possible legal set of inputs (every possible pre-state)
* So when the method verifications are successful, the result is a more powerful statement of correctness than is testing/RAC
* Each method is checked on its own, using the specifications (not the implementations) of the other methods
* This is a valid approach so long as, eventually, all methods verify successfully (and it can be proved that the program terminates)

The tutorial walks you through basic JML, with plenty of examples that you can execute using OpenJML.
There are also exercises for you to test your understanding of the tutorial material.

Have fun!


