---
title: JML Tutorial - Specification (.jml) files
---

## .jml files

In the examples in this tutorial, specifications are written directly in the .java file, along with the program source code. This is convenient if the same engineers are working on both the code and the specifications. 
However, an alternative is to separate the specifications into a separate file.
Such specification files have a `.jml` suffix and are subject to the rules described in this lesson.

There are three reasons to separate specifications from source code:
* It may be that there is no source code. The specifications for libraries, such as the Java system library, are all written in separate `.jml` files.
* It may be that the source code is available but not modifiable. For example, suppose the software is that of a critical legacy system and no modifications to the source (not even to comments) are permitted without substantial review and approval. Then it is better to write the specifications in separate files and have `openjml` combine the source and specifications for verification.
* It may be that the software team simply wants to keep source and specifications separate. Perhaps the two are the domains of separate parts of the team.

Not all specifications can be separated into the `.jml` file. All of the class and method specifications can be, but any helper statement specifications (like assert statements or loop specifications) still need to be intermixed with the actual source. In this case, if the source cannot be modified, the verifier needs to work with a copy of the source that can be edited for verification purposes.

## Working with .jml files

Here is a simple example of a `.java` file and a corresponding `.jml` file. With a .java file like this:
```
{% include_relative T_jmlexample.java %}
```
and a corresponding `.jml` file (with an intentional mistake) in the same folder:
```
{% include_relative T_jmlexample.jml %}
```
we simply run `openjml` on the `.java` file as before:
`openjml --esc T_jmlexample.java`\\
producing
```
{% include_relative T_jmlexample.out %}
```
to see that `openjml` does indeed see the specifications and identify the verification failure.

In this example you can see some of the characteristics of the `.jml` file: the class name (and package) are the same; the method signature is the same but the method has no implementation.

## Where to put .jml files

If specifications are in separate files, the `openjml` tool must be able to find them and associate them with the correct class. 

When a Java compiler compiles source files given on the command-line, those source files may mention other classes that are not on the command-line. The compiler finds those classes by looking in the _classpath_ for compiled `.class` files or the _sourcepath_ for source code files. Both files are lists of folders or .jar files in which to look for the desired file. Developers often do not bother with writing a sourcepath because it is by default (almost) the same as the classpath. So it is easy just to put all the needed folders on one classpath.

Similarly specification files are looked for on a _specspath_, also a sequence of folders or jar files.
When `openjml` reads a source or class file, 
* it looks for a corresponding `.jml` file on the specspath.
* If it does not find one, it looks for a .java file for that class on the specspath. 
* If it does not find a .java file, it uses the .java file from the command-line (if one exists)
* Otherwise, it uses a default set of specifications for the class and its methods.

Now the specspath by default is (almost) the same as the sourcepath, which by default is (almost) the same as the classpath, so it is common practice to use just one classpath for all three paths.

The specspath adds to the sourcepath the specifications for system library files that are part of the OpenJML release. You can specify the specspath explictly with the `--specs-path` option; the given path has the system specification files added to it by default.

Remember also that these paths all contain the folders that are the root of the package path to which a class belongs. That is a class named `org.mypackage.MyClass` would have its .class or .java or .jml file in a folder `X/org/mypackage` where it is `X` that is on the appropriate path.

## Rules about .jml files

Important rule: If there is a .jml file for a class, then any JML annotation comments outside a method body in a .java file for that class are completely (and silently) ignored.

Specification files are very similar to the corresponding source file.
* The package declaration is the same.
* The class signature is the same -- same name, same visibility, same super class and interfaces.
* The method signature is the same, but there is no body --- just a trailing semicolon and the specifications placed before the signature as they would be in the .java file.
* Field declarations are also the same as in the .java file, except that the fields may not have initializers.
* Though the source and specification must have matching Java modifiers (like `public` or `static`) any JML modifiers (like `pure`) are placed in the specification file.
* Any ghost or model declarations are placed in the .jml file. These have all the components of a regular Java declaration (e.g. initializer, method implementation). They cannot be named the same as a Java declaration.
* Any `invariant`s, `initially` clauses, `constraint` clauses, `axiom`s, `represents` clauses, `initializer` specification and `static_initializer` specification are part of the class declaration in the specification file.
* The .jml file may have at most one `initializer` specification and at most one `static_initializer` specification.

OpenJML matches up the Java declarations (that is those declarations not inside a JML annotation comment) with the corresponding Java declarations by comparing names and types. Any mismatch will cause an error.
Then all the ghost and model declarations (those inside a JML annotation comment) are considered; they may not duplicate any Java declarations or each other (or an error results).



