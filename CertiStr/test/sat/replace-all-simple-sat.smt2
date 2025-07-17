(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)

(assert (= a "I22"))
(assert (= b "I33"))
(assert (= b (str.replace_all a "2" "3")))

(check-sat)
(get-model)
