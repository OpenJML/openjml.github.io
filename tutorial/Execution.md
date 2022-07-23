---
title: JML Tutorial - Executing openjml
---

## Options and files

The `openjml` executable is a modified version of the OpenJDK `javac`
and is correspondingly a classic command-line tool:
* The command-line arguments are a mix of files and options.
* Files are given as absolute file paths 
or paths relative to the current working directory
(not relative to the location of `openjml`).
* Options inherited from javac are unchanged. They are a mix of single-hyphen and double-hyphen spellings.
* OpenJML-specific options begin with a double hyphen (e.g., `--quiet`) (single hyphens are still accepted for most options). 
Options that take a value either (a) have the value follow the option as the next argument or (b) 
(for OpenJML options, but only some Java option) use the syntax `-option=value`.
For some options, the value may be a comma-separated list; if the value contains
whitespace, it must be enclosed in quotes.

The details of all the options are given in the [OpenJML Users' Guide](../documentation/OpenJMLUserGuide.pdf). A few are worth mentioning here:
* `--help` or `-?`: emit help information (about all of the options)
* `--esc`: run static checking (the default is just parse and type-checking)
* `--rac`: run runtime-assertion-checking
* `--progress`: emits more information during processing than the default `--normal`

Use `--class-path` or `-cp` just as you would for `javac` to specify the list of folders on which to find files. `openjml` uses a classpath and a sourcepath exactly like `javac` does; in addition `openjml` considers a _specspath_ for finding specification files. For most applications, it is simplest to define a single classpath (using the `-cp` command-line option or the `CLASSPATH` environment variable) giving the jar files and folder roots of package hierarchies for all the class, source and specification files. The details are an advanced topic presented [here](SpecificationFiles).

## Exit codes

The executable returns with one of these exit values:
* 0 - success, though possibly warnings or informational messages may have been emitted
* 1 - errors occurred, such as parsing or type checking errors
* 2 - an error in interpreting the command-line arguments
* 3 - a system error, such as out of memory
* 4 - a fatal error, such as an internal inconsistency or an unexpected exception
* 5 - exit because an operation was cancelled 
* 6 - exit because of a verification failure

The exit code for a verification failure can be changed to one of the other exit codes using the `--verify-exit` option.


