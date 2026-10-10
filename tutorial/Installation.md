---
title: JML Tutorial - Installation
---

Installation of OpenJML done by following the simple steps below:

* Download the current release (in the 21.* or higher series) from [the OpenJML github releases page](https://github.com/OpenJML/OpenJML/releases/latest).
* Unzip the downloaded .zip file in an empty folder. The location and name of the directory are up to the user, although neither should contain any spaces.
* The executable is the script named `openjml` in the top-level of the 
installation. Do not move or rename this file, but you may make a link to the
file or place it on your system PATH.
* On a Mac you may need to run `mac-setup` to enable permissions for the downloaded executables. You may also need to install `realpath` (for example, using `brew install coreutils`), so that symbolic links can be resolved (however, you only need this if you make a symbolic link to `openjml` or other executables in the installation.)

Note that OpenJML is a modified version of the OpenJDK `javac` compiler. 
It is a standalone, encapsulated executable; however, 
no installation of Java is needed to run it.

## **[Exercises](https://www.openjml.org/tutorial/exercises/InstallationEx.html)**

Follow the link in the above heading to work on the exercises for this lesson.

## Resources
+ [Instructions for running openjml and for executing the tutorial's examples](Execution)
