(set-info :smt-lib-version 2.6)
(set-logic QF_S)
(set-info :source |
Generated by: Hung-En Wang, Tzung-Lin Tsai, Chun-Han Lin, Fang Yu, and Jie-Hong R. Jiang
Generated on: 2019-02-28
Generator: Stranger
Application: Security analysis of string manipulating web applications
Target solver: CVC4, Norn, Z3-str2
Publication:
Hung-En Wang, Tzung-Lin Tsai, Chun-Han Lin, Fang Yu, Jie-Hong R. Jiang:
String Analysis via Automata Manipulation with Logic Circuit Representation. CAV (1) 2016: 241-260.
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status unknown)

(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun sigmaStar_5 () String)
(declare-fun sigmaStar_7 () String)
(declare-fun literal_1 () String)
(declare-fun x_9 () String)
(declare-fun literal_11 () String)
(declare-fun x_13 () String)
(declare-fun literal_15 () String)
(declare-fun x_19 () String)
(declare-fun literal_18 () String)
(declare-fun x_23 () String)
(declare-fun literal_22 () String)
(declare-fun x_28 () String)
(declare-fun literal_25 () String)
(declare-fun x_34 () String)
(declare-fun literal_27 () String)
(declare-fun x_38 () String)
(declare-fun literal_31 () String)
(declare-fun x_33 () String)
(declare-fun literal_30 () String)
(declare-fun literal_29 () String)
(declare-fun x_39 () String)
(declare-fun literal_40 () String)
(declare-fun x_43 () String)
(declare-fun literal_35 () String)
(declare-fun x_44 () String)
(declare-fun literal_36 () String)
(declare-fun x_45 () String)
(declare-fun literal_37 () String)
(declare-fun x_47 () String)
(declare-fun literal_42 () String)
(declare-fun x_48 () String)
(declare-fun literal_49 () String)
(declare-fun x_51 () String)
(declare-fun literal_50 () String)
(declare-fun x_52 () String)
(declare-fun literal_46 () String)
(declare-fun x_53 () String)
(declare-fun x_54 () String)
(declare-fun sigmaStar_61 () String)
(declare-fun x_58 () String)
(declare-fun sigmaStar_65 () String)
(declare-fun x_62 () String)
(declare-fun sigmaStar_69 () String)
(declare-fun x_66 () String)
(declare-fun x_70 () String)
(declare-fun literal_71 () String)
(declare-fun x_72 () String)
(assert (= literal_1 "\u{44}\u{42}\u{20}\u{63}\u{61}\u{63}\u{68}\u{65}\u{5f}\u{66}\u{69}\u{6c}\u{74}\u{65}\u{72}\u{73}\u{20}\u{65}\u{6e}\u{74}\u{72}\u{79}\u{20}\u{66}\u{6f}\u{72}\u{20}"))


(assert (= x_9 (str.++ literal_1 sigmaStar_7)))
(assert (= literal_11 "\u{5c}\u{6e}"))


(assert (= x_13 (str.++ x_9 literal_11)))
(assert (= literal_15 "\u{69}\u{64}\u{20}\u{3d}\u{20}\u{5c}\u{6e}"))


(assert (= x_19 (str.++ x_13 literal_15)))
(assert (= literal_18 "\u{66}\u{69}\u{6c}\u{74}\u{65}\u{72}\u{20}\u{3d}\u{20}\u{5c}\u{6e}"))


(assert (= x_23 (str.++ x_19 literal_18)))
(assert (= literal_22 "\u{76}\u{65}\u{72}\u{73}\u{69}\u{6f}\u{6e}\u{20}\u{3d}\u{20}\u{5c}\u{6e}"))


(assert (= x_28 (str.++ x_23 literal_22)))
(assert (= literal_25 "\u{44}\u{65}\u{6c}\u{65}\u{74}\u{69}\u{6e}\u{67}\u{20}\u{44}\u{42}\u{20}\u{63}\u{61}\u{63}\u{68}\u{65}\u{5f}\u{66}\u{69}\u{6c}\u{74}\u{65}\u{72}\u{73}\u{20}\u{65}\u{6e}\u{74}\u{72}\u{79}\u{20}\u{66}\u{6f}\u{72}\u{20}"))


(assert (= x_34 (str.++ literal_25 sigmaStar_7)))
(assert (= literal_27 "\u{6d}\u{64}\u{35}\u{6b}\u{65}\u{79}\u{20}\u{3d}\u{20}\u{5c}\u{6e}"))


(assert (= x_38 (str.++ x_28 literal_27)))
(assert (= literal_31 "\u{4e}\u{75}\u{6d}\u{62}\u{65}\u{72}\u{20}\u{6f}\u{66}\u{20}\u{72}\u{65}\u{63}\u{6f}\u{72}\u{64}\u{73}\u{20}\u{64}\u{65}\u{6c}\u{65}\u{74}\u{65}\u{64}\u{20}\u{3d}\u{20}"))
(assert (= literal_30 "\u{31}"))
(assert (= literal_29 "\u{30}"))


(assert (= x_39 (str.++ literal_31 x_33)))
(assert (= literal_40 "\u{5c}\u{6e}"))


(assert (= x_43 (str.++ x_34 literal_40)))
(assert (= literal_35 "\u{44}\u{42}\u{20}\u{63}\u{61}\u{63}\u{68}\u{65}\u{5f}\u{66}\u{69}\u{6c}\u{74}\u{65}\u{72}\u{73}\u{20}\u{65}\u{6e}\u{74}\u{72}\u{79}\u{20}\u{66}\u{6f}\u{72}\u{20}"))


(assert (= x_44 (str.++ literal_35 sigmaStar_7)))
(assert (= literal_36 "\u{43}\u{6f}\u{75}\u{6c}\u{64}\u{20}\u{6e}\u{6f}\u{74}\u{20}\u{64}\u{65}\u{6c}\u{65}\u{74}\u{65}\u{20}\u{44}\u{42}\u{20}\u{63}\u{61}\u{63}\u{68}\u{65}\u{5f}\u{66}\u{69}\u{6c}\u{74}\u{65}\u{72}\u{73}\u{20}\u{65}\u{6e}\u{74}\u{72}\u{79}\u{20}\u{66}\u{6f}\u{72}\u{20}"))


(assert (= x_45 (str.++ literal_36 sigmaStar_7)))
(assert (= literal_37 "\u{72}\u{61}\u{77}\u{74}\u{65}\u{78}\u{74}\u{20}\u{3d}\u{20}\u{5c}\u{6e}"))


(assert (= x_47 (str.++ x_38 literal_37)))
(assert (= literal_42 "\u{5c}\u{6e}"))


(assert (= x_48 (str.++ x_39 literal_42)))
(assert (= literal_49 "\u{20}\u{6e}\u{6f}\u{74}\u{20}\u{66}\u{6f}\u{75}\u{6e}\u{64}\u{5c}\u{6e}"))


(assert (= x_51 (str.++ x_44 literal_49)))
(assert (= literal_50 "\u{5c}\u{6e}\u{62}\u{65}\u{63}\u{61}\u{75}\u{73}\u{65}\u{20}\u{69}\u{74}\u{20}\u{63}\u{6f}\u{75}\u{6c}\u{64}\u{20}\u{6e}\u{6f}\u{74}\u{20}\u{62}\u{65}\u{20}\u{66}\u{6f}\u{75}\u{6e}\u{64}\u{2e}\u{5c}\u{6e}"))


(assert (= x_52 (str.++ x_45 literal_50)))
(assert (= literal_46 "\u{74}\u{69}\u{6d}\u{65}\u{6d}\u{6f}\u{64}\u{69}\u{66}\u{69}\u{65}\u{64}\u{20}\u{3d}\u{20}\u{5c}\u{6e}"))


(assert (= x_53 (str.++ x_47 literal_46)))


(assert (= x_54 (str.++ x_43 x_48)))
(assert (= x_62 (str.replace x_58 "\u{3c}" "\u{26}\u{6c}\u{74}\u{3b}")))
(assert (= x_66 (str.replace x_62 "\u{3e}" "\u{26}\u{67}\u{74}\u{3b}")))
(assert (= x_70 (str.replace x_66 "\u{22}" "\u{26}\u{71}\u{75}\u{6f}\u{74}\u{3b}")))
(assert (= literal_71 "\u{5c}\u{6e}\u{5c}\u{6e}"))


(assert (= x_72 (str.++ x_70 literal_71)))
(assert (str.in_re x_72 (re.++ (re.* re.allchar) (re.++ (str.to_re "\u{5c}\u{3c}\u{53}\u{43}\u{52}\u{49}\u{50}\u{54}") (re.* re.allchar)))))
(check-sat)
(exit)
