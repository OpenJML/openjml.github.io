
This page describes how to limit the time spent on proof attempts.

## Timeouts

You can set a timeout for a proof attempt with the `-timeout` option.
The value given is an integer number of seconds. A limit of a few minutes 
(e.g. 180) is reasonable. A shorter limit will let fast proofs be reported
while not taking up too much time on longer proofs. 

## Limiting errors

By default, each method is a single, individual proof attempt. OpenJML
looks for a verification failure in the method. If one is found, it is reported
and the tool goes on to find a next one. (The order in which assertion violations
are found is non-deterministic.) The proof attempt quites when the tool cannot
find any more failures.

However, the last step -- where no more assertion violations are found --
can be time-consuming. Why not just stop after one violation is reported and go on to the next method.
The number of errors repoprted for each method can be limited useing the 
`-escMaxWarnings` option. By default it is set to a very large numer,
but it is a reasonable working style to set it to 1.

Note that there will be no proof attempts for any methods in a file if there
are parsing or type-checking errors in the source or specification files.
