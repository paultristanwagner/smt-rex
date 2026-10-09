; QF_NRA equation elimination: substituted variables, and their model values
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun x () Real) (declare-fun y () Real) (declare-fun z () Real)
(assert (> (* x y) 2.0))
(assert (= x (+ y 1.0)))
(assert (= (* 2.0 z) (- x y)))
(assert (< (* y y) 3.0))
(check-sat)
