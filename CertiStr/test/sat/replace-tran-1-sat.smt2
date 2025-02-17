(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)

(assert (= a "ITP2024"))
(assert (= b "ITP2023"))
(assert (= c a))
(assert (= b (str.replace c "2024" "2023")))

(check-sat)
(get-model)
