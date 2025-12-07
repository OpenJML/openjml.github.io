---
title: JML Tutorial - Installation
---

Installation of OpenJML is simple:

* Download the current release (in the 21.* or higher series) from [here](https://github.com/OpenJML/OpenJML/releases/latest).
* Unzip the downloaded .zip file in a clean folder. The location and name of the directory are up to the user (though spaces in the folder name or path are not permitted).
* The executable is the script named `openjml` in the top-level of the 
installation. Do not move or rename this file, but you may make a link to the
file or place it on your system PATH.
* On a Mac you may need to run `mac-setup` to enable permissions for the downloaded executables. You may also need to install `realpath` (for example, using `brew install coreutils`), so that symbolic links can be resolved (you only need this if you make a symbolic link to openjml or other executables in the installation.)
* OpenJML is a modified version of the OpenJDK `javac`. It is a standalone, 
encapsulated executable; no installation of Java is needed to run it.

You can check that the installation is working by running `openjml --version`.
Instructions on running `openjml` and executing the tutorial examples are
[here](Execution).


