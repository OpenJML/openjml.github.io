---
title: JML Tutorial - What is Deductive Verification?
---

We know you are eager to just try out some code, but here is a quick set of bullet points to be sure you understand where this tutorial is headed:
* JML is a language for writing specifications for Java programs
* OpenJML is tool for checking that the Java implementation of the program is consistent with the JML specifications
* This checking can either be done statically (without running the program) -- called Deductive Verification - DV or ESC (Extended static checking)
* or it can be done by running test cases through an instrumented program (RAC - runtime-assertion-checking)

The tutorial is mostly focussed on DV/ESC (though there are lessons on RAC as well):
* The DV approach is akin to logically symbolically executing a method for every possible legal set of inputs (every popssible pre-state)
* So when the method verifications are successful, the result is a more powerful statement of correctness than is testing/RAC
* Each method is checked on its own, using the specifications (not the implementations) of the other methods.
* This is a valid approach so long as, eventually, all methods verify successfully (and it can be proved that the program terminates)

The tutorial walks you through basic JML, with plenty of examples that you can execute using OpenJML.
We hope to add exercises for the motivated tutorial reader.

Have fun!

_Last modified: 2022-03-02 23:12:33_
