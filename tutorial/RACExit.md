---
title: JML Tutorial - RAC Exit Code
---

A RAC-compiled program behaves just like the normally compiled program, except for the runtime assertion checks and, likely, taking longer
to execute. In particular, the program produces the same exit code as it would without RAC, even if there are RAC error messages.
This behavior is not always what is desired.

The exit code of a RAC-compiled program can be changed by setting a Java property, `org.jmlspecs.openjml.racexitcode`, while the
program is executing. For example, the program
```
// openjml -rac T_RacExit.java
public class T_RacExit {

  public static void main(String... args) {
    //@ assert args.length == 1;
    System.exit(10);
  }
}
```
will produce the exit code `10`, as programmed, when compiled and run with either Java or OpenJML:

`openjml -rac T_RacExit.java; openjml-java -cp . T_RacExit; echo $?`

produces the expected error message and reports the exit code of `10`.

However, when run with the property set, the exit code can be different:

`openjml-java -Dorg.jmlspecs.openjml.racexitcode=42 -cp . T_RacExit; echo $?`

produces `42`. Note that the definition of the property must appear in the command-line before the name of the class being executed;
everything after the class name is the command-line for the `T_RacExit` program, not the `openjml-java` program.

If you run the program with arguments that do not produce an assertion error, then the exit code remains `10` as programmed:

`openjml-java -Dorg.jmlspecs.openjml.racexitcode=42 -cp . T_RacExit Z ; echo $?`



<i>Last Modified: <script type="text/javascript"> document.write(new Date(document.lastModified).toUTCString())</script></i>
