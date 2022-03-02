---
title: JML Tutorial - Managing Proofs
---


By default, OpenJML will attempt to verify every method in every file listed on the command-line. 
That is a lot of proof attempts and will likely take a while; a complete run is appropriate for 
the occasional full-system test, but is inefficient for editing, debugging and retrying proof attempts.

This section describes some techniques for managing proofs. These are specific to the OpenJML tool.

* [Choosing what files and methods to verify](MethodSelection)

* [Limiting time](TimeAndErrorLimits)

_Last modified: 2022-03-01 20:49:01_
