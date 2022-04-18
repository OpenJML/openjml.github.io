---
title: JML Tutorial - RAC and Java Checks
---


OpenJML checks for some program states that Java also checks for. When doing runtime-assertion-checking, those checks can happen twice.
So OpenJML will omit the RAC check if it is immediately followed by an identical Java check.
For example, with default settings, the file

```
{% include_relative T_RacJavaCheck.java %}
```

produces
```
{% include_relative T_RacJavaCheck.out %}
```

If you want to see both the RAC check and the Java check, compile using the `--rac-java-checks` option:
`openjml -rac --rac-java-checks T_RacJavaCheck.java && openjml-java -cp . T_RacJavaCheck`
produces
```
{% includei_relative T_RacJavaCheck1.out %}
```

In most cases of such Java checks (e.g. null dereference, index out of bounds), Java will terminate with an exception, as ther is no way
to proceed after such an error (unless the program itself catches and handles the exception).

