"""Shared helpers of the popso-sat benchmark tooling (standard library only).

paths     where things live (this checkout, the main checkout's cache and tool binaries)
dimacs    DIMACS CNF reader (streaming; .cnf/.gz/.xz/.bz2) and deterministic writer
output    parsing of SAT Competition solver output ('s ...' / 'v ...' lines)
verify    model verification against the original formula (streaming)
proc      subprocess runner with wall-clock and memory (RSS) caps
drat      drat-trim invocation and result parsing
classify  result classes and expected-status logic
sets      instance list files (benchmarks/sets/*.txt) and expected statuses
"""
