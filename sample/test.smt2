(set-logic ALL_SUPPORTED)
(define-fun f ((x Bool)) Bool (not x))
(assert (= (f true) (f false)))
(check-sat)
