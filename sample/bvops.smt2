(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun v0 () (_ BitVec 4))
(declare-fun v1 () (_ BitVec 4))

(assert (= v0 (bvnot #b0000)))
(assert (= v1 (bvand #b1000 #b0101)))
(assert (= v0 v1))

(check-sat)
(exit)
