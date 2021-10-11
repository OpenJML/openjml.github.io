# Executing openjml

## Options and files

The `openjml` executable is a modified version of the OpenJDK `javac`
and is correspondingly a classic command-line tool:
* The command-line arguments are a mix of files and options.
* Files are given as absolute file paths 
or paths relative to the current working directory
(not relative to the location of `openjml`).
* Options begin with a single hyphen (e.g., `-quiet`). Options that take a value either (a) have the value follow the option as the next argument or (b) 
(for OpenJML options only) use the syntax `-option=value`.
For some options, the value may be a comma separated list; if the value contains
whitespace, it must be enclosed in quotes.

The details of all the options are given in the [OpenJML Reference Manual](../documentation/OpenJMLUserGuide.pdf). A few are worth mentioning here:
* `-help`: emit help information (about all of the options)
* `-esc`: run static checking (the default is just parse and type-checking)
* `-rac`: run runtime-assertion-checking
* `-progress`: emits more information during processing than the default `-normal`

Use `-classpath` or `-cp` just as you would for `javac`.

## Exit codes

The executable returns with one of these exit values:
* 0 - success, though possibly warnings or informational message may have been emitted
* 1 - errors occurredi, such as parsing or type checking errors
* 2 - an error in interpreting the command-line arguments
* 3 - a system error, such as out of memory
* 4 - a fatal error, such as an internal inconsistency or an unexpected exception
* 5 - exit because an operation was cancelled 
* 6 - exit because of a verification failure

The exit code for a verification failure can be changed to one of the other exti codes using the `-verify-exit` option.

## Tutorial material

All of the examples in the [tutorial](../index) are part of the installation
zip file, in the top-level `tutorial` folder. For example, the `T_ensures1`
example is present as the `T_ensures1.java` file. From within the tutorial
folder, you can run the example using `../openjml -esc T_ensures1.java`.
Examples that produce output (e.g., error messages) have a corresponding `.out`
file containing the expected output.
