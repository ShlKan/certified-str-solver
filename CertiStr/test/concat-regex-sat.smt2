(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)

(assert (= a (str.++ b c)))

(assert (str.in_re a (re.++ (re.range "a" "z") (re.range "A" "Z"))))
(assert (str.in_re b (re.range "a" "z")))
(assert (str.in_re c (re.range "A" "Z")))

(check-sat)
(get-model)
