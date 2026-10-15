---
title: JML Tutorial - Time and Error Limits
---

This page describes how to limit the time spent on proof attempts.

## Timeouts

Two options limit the time the SMT solver spends on proofs. Both take a
number of seconds; 0 means no limit.

* `--timeout` limits each individual solver query. The default is 300.
* `--timeout-method` limits the solver's total time for one method's proof,
  over all of its queries. The default is 0, no limit.

A method's proof may take several queries: the main proof, one more for each
further verification failure after the first is reported, and one for each
feasibility check (see `--check-feasibility`). So a method can take a multiple
of the `--timeout` value. To bound the time for a whole method, use
`--timeout-method`; for example, `--timeout=60 --timeout-method=180`.

When either limit is reached, OpenJML reports that validity (or, for a
feasibility check, feasibility) is unknown because a time limit was reached,
and goes on to the next method. A shorter limit lets fast proofs be reported
while not taking up too much time on long ones.

These limits apply only to the solver. Time OpenJML itself spends, for example
translating a method before it is sent to the solver, is not limited.

## Limiting errors

By default, each method is a single, individual proof attempt. OpenJML
looks for a verification failure in the method. If one is found, it is reported
and the tool goes on to find a next one. (The order in which assertion violations
are found is non-deterministic.) The proof attempt quits when the tool cannot
find any more failures.

However, the last step -- where no more assertion violations are found --
can be time-consuming. So sometimes it is useful to stop after just one verification failure  (or a small fixed number) is reported.
The number of errors reported for each method can be limited using the 
`--esc-max-warnings` option. By default it is set to a very large number,
but it is a reasonable working style to set it to 1.

Note that there will be no proof attempts for any methods in a file if there
are parsing or type-checking errors in the source or specification files.

