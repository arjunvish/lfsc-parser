(set-info :smt-lib-version 2.6)
(set-logic QF_AUFBV)
; This file was generated with the help of KLEE
(set-info :source |
Generated by: Alexandre Gonzalvez
Generated on: 2019-02-28
Generator: KLEE
Target solver: Boolector Z3 STP

Benchmarks arising from a generator of opaque expressions.
These expressions are used to protect some constants against
reverse-engineering, but their robustness can be compromised by
SMT-solvers. More informations in "Effectiveness of synthesis in concolic
deobfuscation" - CS 2017.
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status sat)
; Time expected : less than 1 minute

(declare-fun k () (Array (_ BitVec 32) (_ BitVec 8) ) )
(declare-fun x0 () (Array (_ BitVec 32) (_ BitVec 8) ) )
(declare-fun x1 () (Array (_ BitVec 32) (_ BitVec 8) ) )
(declare-fun x10 () (Array (_ BitVec 32) (_ BitVec 8) ) )
(declare-fun x11 () (Array (_ BitVec 32) (_ BitVec 8) ) )
(declare-fun x5 () (Array (_ BitVec 32) (_ BitVec 8) ) )
(declare-fun x6 () (Array (_ BitVec 32) (_ BitVec 8) ) )
(check-sat)
(exit)