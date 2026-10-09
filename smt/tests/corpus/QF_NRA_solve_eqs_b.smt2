; QF_NRA equation elimination: substituted variables, and their model values
(set-info :status unsat)
(set-logic QF_NRA)
(declare-fun x () Real) (declare-fun y () Real)
(assert (= (+ (* 3.0 x) y) 1.0))
(assert (= (- x y) (/ 1.0 2.0)))
(assert (> (* x x y) 0.1))
(check-sat)
