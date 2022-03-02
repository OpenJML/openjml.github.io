---
title: JML Tutorial - Method Selection
---

One way to be more efficient is to limit your attention to onefile or even one method at a time.
This page describes how to expand or contract the set of methods being verified.

## Files and Folders

First, remember that the `OpenJML` command-line lists options (and their values) and files,
just like the Java compiler (`javac`) does. Usually though you have a set of interdependent files
together in one folder. So `OpenJML` allows you to put a folder path on the command-line,
after the `--dir` option, as in `openjml --esc --dir ~/myfiles`. You can use the `--dirs` option
to list several files: `openjml --esc --dirs ~/myfiles1 ~/myfiles2 ~/myfiles3`. Listing a 
folder name includes subfolders recusively by default. If you don't want recursion, then list
the files using a wildcard as in `~/myfiles/*.java`. The `--dirs` option interprets all
successive command-line arguments as folder paths, up to an argument that begins with a hyphen (`-`).

## Specific methods

To limit proof attempts to specific methods, use the `--method` and `--exclude` options.

* By far the most common use is `--method=<name>`, where `<name>` is a simple name of a method.
Then, within all the files (and folders) listed on the command-line, any method with that name 
is (attempted to be) verified. You can exclude everything with a given name using `--exclude`.
Both of these options can take mutiple comma-separated names. 
`--exclude` takes precedence over `--method`. A constructor is named the same as its parent class.
* A simple name can be ambiguous. To resolve ambiguity, use a full signature: either or both
a prepended fully-qualified class name or an appended aragument signature, as in
`--method="mypackage.MyClass.myMethod"` or `--method="myMethod(int,java.lang.String)"`. Note that
when the expanded name includes characters interpreted by the shell, such as periods and
parentheses, quotes around the method name are needed.
*  Matching patterns -- TBD


_Last modified: 2022-03-01 20:54:09_
