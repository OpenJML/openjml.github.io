---
title: JML Tutorial - Exercises - Installation
---
# Installation Exercises:
## [Installation Tutorial](https://www.openjml.org/tutorial/Installation)

## **Question 1**
**Install OpenJML on the computer system you use for reading this tutorial or for developing code. Run `openjml --version` to check that the installation worked.**

## **Question 2**
**Run OpenJML's ESC to see that the following class results in a verification failure.**

```
/** a class to test if OpenJML's ESC is working properly **/
public class TestOpenJML {
    public static void main(String [] argv) {
        System.out.println("running TestOpenJML...");
        //@ assert 1 < 0;   // ERROR: ESC should fail on this!
    }
}
```

**Learning Objectives:** 
+ Install OpenJML
+ Be able to tell if the installation is working.

## **[Answer Key](InstallationExKey.md)**
## **[All exercises](https://www.openjml.org/tutorial/exercises/exercises)**

## Resources
+ [TestOpenJML](TestOpenJML.java) the `TestOpenJML` class above.
