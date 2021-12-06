# RAC Verification error messages

The default behavior of a RAC-compiled program when detecting an assertion error is to print an error message and continue.
That behavior can be altered at execution time. There are various modes of operation, controlled by Java properties.
Those modes are illustrated with our example program:

```
// openjml -rac T_RacOutput.java
public class T_RacOutput {

  public static void main(String... args) {
    checkArgs(args.length);
    System.out.println("END");
  }

  public static void checkArgs(int len) {
    //@ assert len == 1;
  }
}
```
compiled with

`openjml -rac T_RacOutput.java`

## Error message and continue

The default mode is to simply issue an error message (to `System.out`) and continue execution:

`openjml-java -cp . T_RacOutput`

produces

```
T_RacOutput.java:10: verify: JML assertion is false
    //@ assert len == 1;
        ^
END
```

## Show call stack and continue

An alternate mode shows the call stack leading to the violated assertion:

`openjml-java -cp . -Dorg.jmlspecs.openjml.rac=stack T_RacOutput`

produces the output

```
org.jmlspecs.runtime.JmlAssertionError: T_RacOutput.java:10: verify: JML assertion is false
    //@ assert len == 1;
        ^
	at java.base/org.jmlspecs.runtime.Utils.createException(Utils.java:130)
	at java.base/org.jmlspecs.runtime.Utils.assertionFailureL(Utils.java:86)
	at T_RacOutput.checkArgs(T_RacOutput.java:1)
	at T_RacOutput.main(T_RacOutput.java:5)
END
```

The program continues executing after issuing this expanded error messaage.

## Throw exception (and terminate)

A third alternative is to simply throw an exception upon encountering the first failed assertion. This might be used in fail-fast testing for example.

`openjml-java -cp . -Dorg.jmlspecs.openjml.rac=exception T_RacOutput`

produces the output

```
Exception in thread "main" org.jmlspecs.runtime.JmlAssertionError: T_RacOutput.java:10: verify: JML assertion is false
    //@ assert len == 1;
        ^
	at java.base/org.jmlspecs.runtime.Utils.createException(Utils.java:130)
	at java.base/org.jmlspecs.runtime.Utils.assertionFailureL(Utils.java:84)
	at T_RacOutput.checkArgs(T_RacOutput.java:1)
	at T_RacOutput.main(T_RacOutput.java:5)
```

The exception thrown is a `org.jmlspecs.runtime.JmlAssertionError`, which, unless it is caught and handled within the program itself, causes an immediate exit. 
It is the Java runtime system that prints the exception and its stack, not OpenJML, and the printing is to `System.err`.
The particular kind of exception thrown can be changed by advanced features of OpenJML.

## Use a Java assert

A fourth alternative is to terminate using a Java assert statement. 

`openjml-java -cp . -esa -Dorg.jmlspecs.openjml.rac=assert T_RacOutput`

produces the output
```
Exception in thread "main" java.lang.AssertionError: T_RacOutput.java:10: verify: JML assertion is false
    //@ assert len == 1;
        ^
	at java.base/org.jmlspecs.runtime.Utils.assertionFailureL(Utils.java:89)
	at T_RacOutput.checkArgs(T_RacOutput.java:1)
	at T_RacOutput.main(T_RacOutput.java:5)
```
This is still a choice made at runtime. Upon encountering a false assertion, the program will terminate immediately with a Java `java.lang.AssertionError`.
Remember that assertions in Java are disabled at runtime by default. So executing the compiled program with `openjml-java` requires the 
option `-esa` to enable the assertions; if executing with `java`, use `-ea`.

## Compiling to Java assert statements

By default, JML assertions are checked by code inserted in the test program by OpenJML. The OpenJML compilation can instead insert
*Java* assert statements to do the assertion checking. Wrhjen a Java program is executed, the Java assert statements are disabled by
default.
They must be enabled by the Java `-ea` option.
Using our running example,

`openjml -rac -racCompileToJavaAssert T_RacOutput.java && openjml-java -cp . -ea T_RacOutput`

produces

```
Exception in thread "main" java.lang.AssertionError: T_RacOutput.java:10: verify: JML assertion is false
    //@ assert len == 1;
        ^
	at T_RacOutput.checkArgs(T_RacOutput.java:10)
	at T_RacOutput.main(T_RacOutput.java:5)
```

Now a Java `java.lang.AssertionError` is thrown and the program terminates immediately.
## Control of source information

The amount of source information in an error message can be adjusted. The default message, as shown above, includes a snippet of source information to point to where the error is detected.
This is informative, but there are some reasons one might want to suppress this information. First, it can be verbose. Second it can change as
the source program is edited making test output that inspects this source information volatile. Finally, a RAC-compiled class file is much larger than a simple Java-compiled class file because of the assertion checks that have been added; those assertion checks include the text of the
error messages to be emitted should the assertion be false. Consequently a verbose error message contributes to the size of the 
RAC-compiled file.

The content of the error message is controlled by the `-showRacSource` compilation command-line option, which takes one of
three options: source, line, or none. The default is "source" and produces messages that show part of the source file;
"line" just gives line information; "none" just gives the message.

With `-showRacSource=source":
```
T_RacOutput.java:10: verify: JML assertion is false
    //@ assert len == 1;
        ^
END
```

With `-showRacSource=line":
```
T_RacOutput.java:10: verify: JML assertion is false
END
```

With `-showRacSource=none":
```
verify: JML assertion is false
END
```

As the text of error messages is compiled into the class file, the control of error messages is a *compile-time*, not a runtime, option.


