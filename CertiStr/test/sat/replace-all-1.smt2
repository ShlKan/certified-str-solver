
(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)



(assert (= b (str.replace_all a "a" "b")))

(assert (= b "c"))

(check-sat)




