(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(declare-fun d () String)

(assert (= a (str.++ b c)))
(assert (= a (str.++ c d)))
(assert (= b (str.++ d c)))

(assert (str.in_re a (re.+ (re.union (str.to_re "x") (str.to_re "y")))))
(assert (str.in_re c (re.union (str.to_re "A") (re.range "a" "z"))))
(assert (str.in_re c (re.union (str.to_re "B") (re.range "a" "Z"))))
;(assert (= d (str.replace "Ilove" "love" "like")))

(check-sat)
(get-model)
