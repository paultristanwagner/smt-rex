; QF_NRA equation elimination: substituted variables, and their model values
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun x () Real) (declare-fun y () Real) (declare-fun w () Real)
(assert (= w (* x y)))
(assert (= x (- 3.0 y)))
(assert (= y (* 2.0 w)))
(assert (> w 0.0))
(check-sat)
