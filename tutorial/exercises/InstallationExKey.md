---
title: JML Tutorial - Exercises - Installation
---
# Installation Exercises Key:
## [Installation Tutorial](https://www.openjml.org/tutorial/Installation)

## **Question 1**
This should show a brief message (on standard output, i.e., the console/terminal) like the following.

```
openjml 21.0.28
```

If that does not happen, make sure you have `openjml` in your `PATH` and take whatever (OS specific) steps may be needed to make sure that you have permission to execute OpenJML, etc.

## **Question 2**

When you run `openjml --esc TestOpenJML.java`, you should see output something like the following. (The exact output might vary depending on the version of OpenJML you are using.)

```
TestOpenJML.java:6: verify: The prover cannot establish an assertion (Assert) in method main
        //@ assert 1 < 0;   // ERROR: ESC should fail on this!
            ^
1 verification failure
```

## **Resources:**
+ [Installation Exercises](installationEx.md)
+ [Question 2 Java](TestOpenJML.java)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)
