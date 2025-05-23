(set-info :smt-lib-version 2.6)
(set-logic QF_SLIA)
(set-info :source |
Generated by: Oliver Markgraf
Generator: Stranger
Generated on: 2023-04-03
Application: Real Web Applications
Target solver: SLENT
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status unknown)
(declare-fun sigmaStar_safe_48 () String)
(declare-fun b_sigmaStar_safe_48 () Bool)
(declare-fun sigmaStar_safe_49 () String)
(declare-fun b_sigmaStar_safe_49 () Bool)
(declare-fun sigmaStar_050 () String)
(declare-fun b_sigmaStar_050 () Bool)
(declare-fun literal_8 () String)
(declare-fun b_literal_8 () Bool)
(declare-fun literal_10 () String)
(declare-fun b_literal_10 () Bool)
(declare-fun literal_13 () String)
(declare-fun b_literal_13 () Bool)
(declare-fun atkPtn () String)
(declare-fun b_atkPtn () Bool)
(declare-fun x_1 () String)
(declare-fun b_x_1 () Bool)
(declare-fun x_2 () String)
(declare-fun b_x_2 () Bool)
(declare-fun x_7 () String)
(declare-fun b_x_7 () Bool)
(declare-fun x_9 () String)
(declare-fun b_x_9 () Bool)
(declare-fun x_11 () String)
(declare-fun b_x_11 () Bool)
(declare-fun x_12 () String)
(declare-fun b_x_12 () Bool)
(declare-fun x_14 () String)
(declare-fun b_x_14 () Bool)
(declare-fun sink () String)
(declare-fun b_sink () Bool)
(declare-fun atk_sigmaStar_1 () String)
(declare-fun atk_sigmaStar_2 () String)
(declare-fun atk_sink () String)


(assert (str.in_re sigmaStar_safe_48 (re.* (re.union (re.range "0" "9") (re.union (re.range "a" "z") (re.range "A" "Z"))))))

(assert (str.in_re sigmaStar_safe_49 (re.* (re.union (re.range "0" "9") (re.union (re.range "a" "z") (re.range "A" "Z"))))))

(assert (= literal_8 "\x20\x20\x20\x20"))

(assert (= literal_10 "\x20\x3d\x20\x27"))

(assert (= literal_13 "\x27\x3b\x5c\x6e"))
(assert (str.in_re atkPtn (re.++ (re.union (str.to_re "j") (re.union (str.to_re "|") (str.to_re "J"))) (re.++ (re.union (str.to_re "a") (re.union (str.to_re "|") (str.to_re "A"))) (re.++ (re.union (str.to_re "v") (re.union (str.to_re "|") (str.to_re "V"))) (re.++ (re.union (str.to_re "a") (re.union (str.to_re "|") (str.to_re "A"))) (re.++ (re.union (str.to_re "s") (re.union (str.to_re "|") (str.to_re "S"))) (re.++ (re.union (str.to_re "c") (re.union (str.to_re "|") (str.to_re "C"))) (re.++ (re.union (str.to_re "r") (re.union (str.to_re "|") (str.to_re "R"))) (re.++ (re.union (str.to_re "i") (re.union (str.to_re "|") (str.to_re "I"))) (re.++ (re.union (str.to_re "p") (re.union (str.to_re "|") (str.to_re "P"))) (re.++ (re.union (str.to_re "t") (re.union (str.to_re "|") (str.to_re "T"))) (str.to_re ":")))))))))))))
(declare-fun tmp_0 () String)
(assert (= tmp_0 (str.++ atkPtn atk_sigmaStar_2)))
(assert (= atk_sink (str.++ atk_sigmaStar_1 tmp_0)))
(assert (= x_1 sigmaStar_safe_48))

(assert (= x_1 sigmaStar_safe_49))

(assert (= x_2 x_1))

(assert (= x_2 sigmaStar_050))

(assert (= x_7 (str.replace_re x_2 (re.++ (re.union (str.to_re "j") (re.union (str.to_re "|") (str.to_re "J"))) (re.++ (re.union (str.to_re "a") (re.union (str.to_re "|") (str.to_re "A"))) (re.++ (re.union (str.to_re "v") (re.union (str.to_re "|") (str.to_re "V"))) (re.++ (re.union (str.to_re "a") (re.union (str.to_re "|") (str.to_re "A"))) (re.++ (re.union (str.to_re "s") (re.union (str.to_re "|") (str.to_re "S"))) (re.++ (re.union (str.to_re "c") (re.union (str.to_re "|") (str.to_re "C"))) (re.++ (re.union (str.to_re "r") (re.union (str.to_re "|") (str.to_re "R"))) (re.++ (re.union (str.to_re "i") (re.union (str.to_re "|") (str.to_re "I"))) (re.++ (re.union (str.to_re "p") (re.union (str.to_re "|") (str.to_re "P"))) (re.++ (re.union (str.to_re "t") (re.union (str.to_re "|") (str.to_re "T"))) (str.to_re ":"))))))))))) "_$1.") ))



(assert (= x_9 (str.++ literal_8 x_7)))




(assert (= x_11 (str.++ x_9 literal_10)))





(assert (= x_14 (str.++ x_12 literal_13)))


(assert (= sink x_14))
(assert (= sink atk_sink))


(check-sat)
(exit)