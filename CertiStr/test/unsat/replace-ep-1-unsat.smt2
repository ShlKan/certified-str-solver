(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)

(assert (= a "ITP2024"))
(assert (= b "ITP 2"))
(assert (= b (str.replace a "2024" "")))

(check-sat)
(get-model)
