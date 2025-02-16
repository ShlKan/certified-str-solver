(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(declare-fun d () String)

(assert (str.in_re a (re.+ (str.to_re "a"))))
(assert (= b "World"))
(assert (= c (str.++ a b)))
(assert (= d "Hello World"))
(assert (= d (str.replace c "aaaaa" "Hello ")))

(check-sat)
