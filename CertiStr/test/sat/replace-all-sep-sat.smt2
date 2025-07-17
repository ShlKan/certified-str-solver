(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)

(assert (= a "A2X2X2X3X2"))
(assert (= b "A3X3X3X3X3"))
(assert (= b (str.replace_all a "2" "3")))

(check-sat)
(get-model)
