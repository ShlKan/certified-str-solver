(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(declare-fun d () String)
(declare-fun e () String)

(assert (= a "ITP2024"))
(assert (= b "ITP2024"))
(assert (= b (str.replace a "" "2024")))


(check-sat)
