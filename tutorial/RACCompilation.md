---
title: JML Tutorial - Runtime Assertion Checking (RAC) - Compilation and Execution
---

A JML-annotated Java program can be compiled and executed like any Java program, but with the JML assertions checked at runtime.
The JML assertions are only checked for the particular values of inputs, variables, etc. that occur during that particular run
of the program, not for all possible inputs (as in static deductive verification). Furthermore not all JML constructs are executable;
some will be ignored during compilation for RAC.

## Compilation

The `openjml` tool when used with the `--rac` option compiles a Java program with runtime assertions added. In this mode `openjml`
functions much like `javac`: it has the same Java command-line options (like `-cp` or `--classpath`), along with additional OpenJML
options.

For example,
```
{% include_relative T_Rac1.java %}
```
compiles with `openjml --rac T_Rac1.java` to produce a `T_Rac1.class` file.


## Execution

The RAC-compiled Java program can then be executed in two ways: either using the command `openjml-java` or the standard installed `java` command.
If you are using `openjml-java` you do not need to have an installation of Java itself.

### openjml-java

`openjml-java` is a build of `java` produced and installed along with `openjml`. It functions like `java` except that it includes the 
runtime libraries needed for RAC. So to run the program compiled above one just executes

`openjml-java -cp . T_Rac1`

producing
```
{% include_relative T_Rac2.out %}
```

If you run it with one command-line argument, then the assertion in the program is true and does not produce any error messages:

`openjml-java -cp . T_Rac1 hi`

### java
If you have java (at least v. 21, as of December 2024) installed on your system, you can use it to run the RAC-compiled program produced by `openjml`. You need to include in your classpath the JML runtime library, `jmlruntime.jar`, which is available in the OpenJML installation. 
If `$OJ` is the path to the installation folder containing `openjml` and `jmlruntime.jar` then you can run the RAC-compiled class file from 
above as

`java -cp .:$OJ/jmlruntime.jar T_Rac1`

producing
```
{% include_relative T_Rac3.out %}
``` 


