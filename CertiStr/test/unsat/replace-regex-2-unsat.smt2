(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)

(assert (str.in_re a (re.++ (re.+ (str.to_re "a")) (re.* (str.to_re "b")))))
(assert (= b "2023bbbba"))
(assert (= b (str.replace a "aaa" "2023")))

(check-sat)
(get-model)
