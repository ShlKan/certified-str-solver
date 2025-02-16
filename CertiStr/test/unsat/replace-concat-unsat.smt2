(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(declare-fun d () String)

(assert (= a "Hello"))
(assert (= b " World"))
(assert (= c (str.++ a b)))
(assert (= d "Hello World"))
(assert (= d (str.replace c "Hello" "Hello ")))

(check-sat)
(get-model)
