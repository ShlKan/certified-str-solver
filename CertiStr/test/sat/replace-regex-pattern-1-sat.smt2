(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)

(assert (= a "ITP202412342342"))
(assert (= b "ITP2023"))
(assert (= b (str.replace_re a (re.+ (re.range "0" "9")) "2023")))

(check-sat)
(get-model)
