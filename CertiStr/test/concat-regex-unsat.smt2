(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(declare-fun d () String)

(assert (= a (str.++ b c)))


(assert (str.in_re a (re.+ (re.union (str.to_re "x") (str.to_re "y")))))
(assert (str.in_re b (re.union (str.to_re "A") (re.range "a" "g"))))
(assert (str.in_re c (re.union (str.to_re "B") (re.range "a" "z"))))
(assert (= d (str.replace a "x" "y")))

(check-sat)
(get-model)
