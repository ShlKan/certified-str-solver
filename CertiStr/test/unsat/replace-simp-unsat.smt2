(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)

(assert (= a "ITP2024"))
(assert (= b "ITP2025"))
(assert (= b (str.replace a "2024" "2023")))

(check-sat)
(get-model)
