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
(declare-fun sigmaStar_safe_50 () String)
(declare-fun b_sigmaStar_safe_50 () Bool)
(declare-fun sigmaStar_safe_51 () String)
(declare-fun b_sigmaStar_safe_51 () Bool)
(declare-fun literal_8 () String)
(declare-fun b_literal_8 () Bool)
(declare-fun sigmaStar_553 () String)
(declare-fun b_sigmaStar_553 () Bool)
(declare-fun literal_10 () String)
(declare-fun b_literal_10 () Bool)
(declare-fun sigmaStar_055 () String)
(declare-fun b_sigmaStar_055 () Bool)
(declare-fun literal_18 () String)
(declare-fun b_literal_18 () Bool)
(declare-fun literal_22 () String)
(declare-fun b_literal_22 () Bool)
(declare-fun sigmaStar_1761 () String)
(declare-fun b_sigmaStar_1761 () Bool)
(declare-fun literal_25 () String)
(declare-fun b_literal_25 () Bool)
(declare-fun literal_26 () String)
(declare-fun b_literal_26 () Bool)
(declare-fun literal_33 () String)
(declare-fun b_literal_33 () Bool)
(declare-fun literal_32 () String)
(declare-fun b_literal_32 () Bool)
(declare-fun literal_31 () String)
(declare-fun b_literal_31 () Bool)
(declare-fun literal_30 () String)
(declare-fun b_literal_30 () Bool)
(declare-fun literal_29 () String)
(declare-fun b_literal_29 () Bool)
(declare-fun literal_39 () String)
(declare-fun b_literal_39 () Bool)
(declare-fun literal_40 () String)
(declare-fun b_literal_40 () Bool)
(declare-fun literal_41 () String)
(declare-fun b_literal_41 () Bool)
(declare-fun literal_42 () String)
(declare-fun b_literal_42 () Bool)
(declare-fun literal_27 () String)
(declare-fun b_literal_27 () Bool)
(declare-fun literal_43 () String)
(declare-fun b_literal_43 () Bool)
(declare-fun literal_50 () String)
(declare-fun b_literal_50 () Bool)
(declare-fun literal_56 () String)
(declare-fun b_literal_56 () Bool)
(declare-fun literal_62 () String)
(declare-fun b_literal_62 () Bool)
(declare-fun literal_61 () String)
(declare-fun b_literal_61 () Bool)
(declare-fun literal_60 () String)
(declare-fun b_literal_60 () Bool)
(declare-fun literal_59 () String)
(declare-fun b_literal_59 () Bool)
(declare-fun literal_58 () String)
(declare-fun b_literal_58 () Bool)
(declare-fun literal_63 () String)
(declare-fun b_literal_63 () Bool)
(declare-fun atkPtn () String)
(declare-fun b_atkPtn () Bool)
(declare-fun x_9 () String)
(declare-fun b_x_9 () Bool)
(declare-fun x_12 () String)
(declare-fun b_x_12 () Bool)
(declare-fun x_13 () String)
(declare-fun b_x_13 () Bool)
(declare-fun x_14 () String)
(declare-fun b_x_14 () Bool)
(declare-fun x_20 () String)
(declare-fun b_x_20 () Bool)
(declare-fun x_21 () String)
(declare-fun b_x_21 () Bool)
(declare-fun x_23 () String)
(declare-fun b_x_23 () Bool)
(declare-fun x_24 () String)
(declare-fun b_x_24 () Bool)
(declare-fun x_28 () String)
(declare-fun b_x_28 () Bool)
(declare-fun x_34 () String)
(declare-fun b_x_34 () Bool)
(declare-fun x_35 () String)
(declare-fun b_x_35 () Bool)
(declare-fun x_36 () String)
(declare-fun b_x_36 () Bool)
(declare-fun x_37 () String)
(declare-fun b_x_37 () Bool)
(declare-fun x_38 () String)
(declare-fun b_x_38 () Bool)
(declare-fun x_44 () String)
(declare-fun b_x_44 () Bool)
(declare-fun x_45 () String)
(declare-fun b_x_45 () Bool)
(declare-fun x_46 () String)
(declare-fun b_x_46 () Bool)
(declare-fun x_47 () String)
(declare-fun b_x_47 () Bool)
(declare-fun x_48 () String)
(declare-fun b_x_48 () Bool)
(declare-fun x_49 () String)
(declare-fun b_x_49 () Bool)
(declare-fun x_51 () String)
(declare-fun b_x_51 () Bool)
(declare-fun x_52 () String)
(declare-fun b_x_52 () Bool)
(declare-fun x_53 () String)
(declare-fun b_x_53 () Bool)
(declare-fun x_54 () String)
(declare-fun b_x_54 () Bool)
(declare-fun x_55 () String)
(declare-fun b_x_55 () Bool)
(declare-fun x_57 () String)
(declare-fun b_x_57 () Bool)
(declare-fun x_64 () String)
(declare-fun b_x_64 () Bool)
(declare-fun x_65 () String)
(declare-fun b_x_65 () Bool)
(declare-fun x_66 () String)
(declare-fun b_x_66 () Bool)
(declare-fun x_67 () String)
(declare-fun b_x_67 () Bool)
(declare-fun x_68 () String)
(declare-fun b_x_68 () Bool)
(declare-fun x_69 () String)
(declare-fun b_x_69 () Bool)
(declare-fun x_70 () String)
(declare-fun b_x_70 () Bool)
(declare-fun sink () String)
(declare-fun b_sink () Bool)
(declare-fun atk_sigmaStar_1 () String)
(declare-fun atk_sigmaStar_2 () String)
(declare-fun atk_sink () String)
(declare-fun sigmaStar_n0 () String)
(declare-fun b_sigmaStar_n0 () Bool)
(declare-fun sigmaStar_n1 () String)
(declare-fun b_sigmaStar_n1 () Bool)
(declare-fun sigmaStar_n2 () String)
(declare-fun b_sigmaStar_n2 () Bool)

(assert (str.in_re sigmaStar_safe_50 (re.* (re.union (re.range "0" "9") (re.union (re.range "a" "z") (re.range "A" "Z"))))))
(assert (str.in_re sigmaStar_safe_51 (re.* (re.union (re.range "0" "9") (re.union (re.range "a" "z") (re.range "A" "Z"))))))

(assert (= literal_8 "\x20\x4f\x52\x20\x62\x6c\x61\x63\x6b\x6c\x69\x73\x74\x5f\x69\x70\x3d"))

(assert (= literal_10 ""))

(assert (= literal_18 "\x20\x4f\x52\x20\x62\x6c\x61\x63\x6b\x6c\x69\x73\x74\x5f\x69\x70\x3d"))

(assert (= literal_22 "\x20\x28\x61\x64\x6d\x69\x6e\x5f\x72\x69\x67\x68\x74\x73\x3d\x27"))

(assert (= literal_25 "\x27\x29"))

(assert (= literal_26 "\x27"))

(assert (= literal_33 "\x28\x2a\x29"))

(assert (= literal_32 "\x28\x2a\x29"))

(assert (= literal_31 "\x28\x2a\x29"))

(assert (= literal_30 "\x28\x2a\x29"))

(assert (= literal_29 "\x28\x2a\x29"))

(assert (= literal_39 "\x53\x45\x4c\x45\x43\x54\x20\x43\x6f\x75\x6e\x74"))

(assert (= literal_40 "\x20\x41\x4e\x44\x20\x61\x64\x6d\x69\x6e\x5f\x6c\x69\x6e\x6b\x21\x3d\x27\x72\x65\x73\x65\x72\x76\x65\x64\x27\x20\x41\x4e\x44\x20\x61\x64\x6d\x69\x6e\x5f\x70\x61\x67\x65\x3d\x27\x34\x27"))

(assert (= literal_41 "\x20\x41\x4e\x44\x20\x61\x64\x6d\x69\x6e\x5f\x6c\x69\x6e\x6b\x21\x3d\x27\x72\x65\x73\x65\x72\x76\x65\x64\x27\x20\x41\x4e\x44\x20\x61\x64\x6d\x69\x6e\x5f\x70\x61\x67\x65\x3d\x27\x31\x27"))

(assert (= literal_42 "\x20\x41\x4e\x44\x20\x61\x64\x6d\x69\x6e\x5f\x6c\x69\x6e\x6b\x21\x3d\x27\x72\x65\x73\x65\x72\x76\x65\x64\x27\x20\x41\x4e\x44\x20\x61\x64\x6d\x69\x6e\x5f\x70\x61\x67\x65\x3d\x27\x32\x27"))

(assert (= literal_27 "\x62\x6c\x61\x63\x6b\x6c\x69\x73\x74\x5f\x69\x70\x3d\x27"))

(assert (= literal_43 "\x20\x41\x4e\x44\x20\x61\x64\x6d\x69\x6e\x5f\x6c\x69\x6e\x6b\x21\x3d\x27\x72\x65\x73\x65\x72\x76\x65\x64\x27\x20\x41\x4e\x44\x20\x61\x64\x6d\x69\x6e\x5f\x70\x61\x67\x65\x3d\x27\x33\x27"))

(assert (= literal_50 "\x20\x46\x52\x4f\x4d\x20"))

(assert (= literal_56 "\x20\x57\x48\x45\x52\x45\x20"))

(assert (= literal_62 "\x61\x64\x6d\x69\x6e"))

(assert (= literal_61 "\x62\x6c\x61\x63\x6b\x6c\x69\x73\x74"))

(assert (= literal_60 "\x61\x64\x6d\x69\x6e"))

(assert (= literal_59 "\x61\x64\x6d\x69\x6e"))

(assert (= literal_58 "\x61\x64\x6d\x69\x6e"))

(assert (= literal_63 ""))
(assert (str.in_re atkPtn (re.++ (re.union (str.to_re "%27") (str.to_re "'")) (str.to_re "union"))))
(declare-fun tmp_0 () String)
(assert (= tmp_0 (str.++ atkPtn atk_sigmaStar_2)))
(assert (= atk_sink (str.++ atk_sigmaStar_1 tmp_0)))
(assert (= x_9 sigmaStar_safe_50))

(assert (= x_9 sigmaStar_safe_51))



(assert (= x_12 (str.++ literal_8 sigmaStar_553)))


(assert (= x_13 literal_10))

(assert (= x_13 x_9))

(assert (= x_14 x_13))

(assert (= x_14 sigmaStar_055))

(assert (= x_20 (str.replace x_14 "." "' OR admin_rights='") ))



(assert (= x_21 (str.++ x_12 literal_18)))




(assert (= x_23 (str.++ literal_22 x_20)))




(assert (= x_24 (str.++ x_21 sigmaStar_1761)))




(assert (= x_28 (str.++ x_23 literal_25)))




(assert (= x_34 (str.++ x_24 literal_26)))


(assert (= x_35 literal_33))

(assert (= x_35 literal_32))

(assert (= x_36 x_35))

(assert (= x_36 literal_31))

(assert (= x_37 x_36))

(assert (= x_37 literal_30))

(assert (= x_38 x_37))

(assert (= x_38 literal_29))



(assert (= x_44 (str.++ literal_39 x_38)))




(assert (= x_45 (str.++ x_28 literal_40)))




(assert (= x_46 (str.++ sigmaStar_n0 literal_41)))




(assert (= x_47 (str.++ sigmaStar_n1 literal_42)))




(assert (= x_48 (str.++ literal_27 x_34)))




(assert (= x_49 (str.++ sigmaStar_n2 literal_43)))




(assert (= x_51 (str.++ x_44 literal_50)))


(assert (= x_52 x_49))

(assert (= x_52 x_48))

(assert (= x_53 x_52))

(assert (= x_53 x_47))

(assert (= x_54 x_53))

(assert (= x_54 x_46))

(assert (= x_55 x_54))

(assert (= x_55 x_45))



(assert (= x_57 (str.++ literal_56 x_55)))


(assert (= x_64 literal_62))

(assert (= x_64 literal_61))

(assert (= x_65 x_64))

(assert (= x_65 literal_60))

(assert (= x_66 x_65))

(assert (= x_66 literal_59))

(assert (= x_67 x_66))

(assert (= x_67 literal_58))

(assert (= x_68 literal_63))

(assert (= x_68 x_57))



(assert (= x_69 (str.++ x_51 x_67)))




(assert (= x_70 (str.++ x_69 x_68)))


(assert (= sink x_70))
(assert (= sink atk_sink))


(check-sat)
(exit)