(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun v0 () (_ BitVec 4))
(declare-fun v1 () (_ BitVec 4))

(assert (= v0 (bvadd #b1111 (bvneg #b1111))))
(assert (= v1 (bvmul #b0001 #b0001)))
(assert (= v0 v1))

(check-sat)
(exit)
