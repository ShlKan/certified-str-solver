(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(declare-fun d () String)
(declare-fun e () String)
(declare-fun f () String)
(declare-fun g () String)
(declare-fun i () String)


(assert (= a (str.++ b c)))
(assert (= b (str.++ d e)))
(assert (= d (str.++ f g)))
(assert (= i (str.++ a b)))

(check-sat)
(get-model)
