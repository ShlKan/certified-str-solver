(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(declare-fun d () String)
(declare-fun e () String)

(assert (= a "ITP2024"))
(assert (= b "2024ITP2024"))
(assert (= b (str.replace a "" "2024")))

(assert (= c "I2024P2024"))
(assert (= c (str.replace "ITP2024" "T" "2024")))

(assert (= d "ITP22024024"))
(assert (= d (str.replace "ITP2Q024" "Q" "2024")))

(assert (= e "ITP20242024"))
(assert (= e (str.replace "ITPWW2024" "WW" "2024")))


(check-sat)
