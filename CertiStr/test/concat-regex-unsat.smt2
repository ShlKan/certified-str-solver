(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(declare-fun d () String)

(assert (= a (str.++ b c)))


(assert (str.in_re a (re.+ (re.union (str.to_re "x") (str.to_re "y")))))
(assert (str.in_re b (re.union (str.to_re "A") (re.range "a" "g"))))
(assert (str.in_re c (re.union (str.to_re "\u{2f}") (re.range "\u{2f}" "\u{3fff}"))))
(assert (= d (str.replace a 
"\u{74}\u{69}\u{6e}\u{79}\u{6d}\u{63}\u{65}\u{5f}" "y")))

(check-sat)
(get-model)
