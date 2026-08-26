(set-logic QF_LIA)
(declare-const x Int)
(assert (= (* 2 x) 1))
(check-sat)
