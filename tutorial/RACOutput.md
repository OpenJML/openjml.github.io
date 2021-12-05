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

`openjml-java -cp . -Dorg.jmlspecs.openjml.racshowstack T_RacOutput`

produces the output

```
org.jmlspecs.runtime.JmlAssertionError: T_RacOutput.java:10: verify: JML assertion is false
    //@ assert len == 1;
        ^
	at java.base/org.jmlspecs.runtime.Utils.createException(Utils.java:128)
	at java.base/org.jmlspecs.runtime.Utils.assertionFailureL(Utils.java:86)
	at T_RacOutput.checkArgs(T_RacOutput.java:1)
	at T_RacOutput.main(T_RacOutput.java:5)
END
```

The program continues executing after issuing this expanded error messaage.

## Throw exception (and terminate)

A third alternative is to simply throw an exception upon encountering the first failed assertion. This might be used in fail-fast testing for example.

`openjml-java -cp . -Dorg.jmlspecs.openjml.racexceptions T_RacOutput`

produces the output

```
Exception in thread "main" org.jmlspecs.runtime.JmlAssertionError: T_RacOutput.java:10: verify: JML assertion is false
    //@ assert len == 1;
        ^
	at java.base/org.jmlspecs.runtime.Utils.createException(Utils.java:128)
	at java.base/org.jmlspecs.runtime.Utils.assertionFailureL(Utils.java:82)
	at T_RacOutput.checkArgs(T_RacOutput.java:1)
	at T_RacOutput.main(T_RacOutput.java:5)
```

The exception thrown is a `org.jmlspecs.runtime.JmlAssertionError`, which, unless it is caught and handled within the program itself, causes an immediate exit. 
It is the Java runtime system that prints the exception and its stack, not OpenJML, and the printing is to `System.err`.
The particular kind of exception thrown can be changed by advanced features of OpenJML.

## Control of source information

Finally, the amount of source information in an error message can be adjusted. The default message, as shown above, includes a snippet of source information to point to where the error is detected.
This is informative, but there are some reasons one might want to suppress this information. First, it can be verbose. Second it can change as
the source program is edited making test output that inspects this source information volatile. Finally, a RAC-compiled class file is much larger than a simple Java-compiled class file because of the assertion checks that have been added; those assertion checks include the text of the
error messages to be emitted should the assertion be false. Consequently a verbose error message contributes to the size of the 
RAC-compiled file.

The content of the error message is controlled by the `-showRacSource` compilation command-line option. By default this is enabled and
the error messages contain the source information:

```
T_RacOutput.java:10: verify: JML assertion is false
    //@ assert len == 1;
        ^
END
```

If the option is disabled during compilation, using `-no-racShowSource`, then only the line position is shown:
```
T_RacOutput.java:10: verify: JML assertion is false
END
```

As the text of error messages is compiled into the class file, the control of error messages is a *compile-time*, not a runtime, option.



