; function definitions

(defun nat (x)
        (if (consp x)
            (and (equal (car x) nil)
                 (nat (cdr x)))
            (equal x nil)))

(defun mapnil (x)
        (if (consp x)
            (cons nil (mapnil (cdr x)))
            nil))
            
(defun plus (x y)
        (if (consp x)
            (cons nil (plus (cdr x) y))
            (mapnil y)))

(defun times (x y)
        (if (consp x)
            (plus y (times (cdr x) y))
            nil))

;-------------------------------------------------

; Problem 71

;(DEFTHM LEMMA1-71
;        (IMPLIES (AND (CONSP X) (EQUAL X Y))
;                 (EQUAL (CDR X) (CDR Y)))
;        :INSTRUCTIONS (:PROMOTE :S-PROP))


(DEFTHM PROBLEM71
        (IMPLIES (NAT I) (EQUAL (PLUS I NIL) I))
        :INSTRUCTIONS (:INDUCT (:DV 1)
                               :EXPAND :S-PROP :TOP (:DV 2)
                               (:DV 1)
                               :EXPAND :S-PROP :TOP (:DV 2 1)
                               :EXPAND :S-PROP :TOP :S-PROP (:DV 1)
                               :EXPAND :S-PROP :TOP (:DV 2 1)
                               :TOP :S-PROP (:DV 1)
                               :EXPAND :S-PROP :TOP (:DV 2 1)
                               :EXPAND :S-PROP :UP :TOP (:DV 2 1)
                               :TOP (:DEMOTE 3)
                               :SL))


;-------------------------------------------------

;problem 72

(DEFTHM LEMMA1-72
        (EQUAL (MAPNIL X) (MAPNIL (MAPNIL X)))
        :INSTRUCTIONS (:INDUCT (:DV 1)
                               :EXPAND :S-PROP :TOP (:DV 2 1)
                               :EXPAND
                               :S-PROP :UP :EXPAND :S-PROP (:DV 1)
                               :EXPAND :S-PROP :TOP (:DV 2 1)
                               :EXPAND
                               :S-PROP :UP :EXPAND :S-PROP (:DV 2)
                               (:DV 1)
                               (:REWRITE CDR-CONS)
                               :UP :TOP (:REWRITE CONS-EQUAL)
                               :S-PROP))

(DEFTHM LEMMA2-72
        (EQUAL (PLUS (MAPNIL I) J) (PLUS I J))
        :INSTRUCTIONS (:INDUCT (:DV 1 1)
                               :EXPAND
                               :S-PROP :UP :EXPAND :S-PROP :UP (:DV 2)
                               :EXPAND :S-PROP :TOP :S-PROP (:DV 1 1)
                               :EXPAND
                               :S-PROP :UP :EXPAND :S-PROP (:DV 2 1)
                               (:REWRITE CDR-CONS)
                               :TOP (:DV 2)
                               :EXPAND
                               :S-PROP :TOP (:REWRITE CONS-EQUAL)
                               :S-PROP))

(DEFTHM LEMMA3-72
        (EQUAL (MAPNIL (PLUS I J)) (PLUS I J))
        :INSTRUCTIONS (:INDUCT (:DV 1 1)
                               :EXPAND :S-PROP :UP :UP (:DV 2)
                               :EXPAND :S-PROP :TOP (:USE LEMMA1-72)
                               :PROMOTE (:DV 2)
                               (:REWRITE LEMMA1-72)
                               (:DV 1)
                               :TOP :S-PROP (:DV 1 1)
                               :EXPAND
                               :S-PROP :UP :EXPAND :S-PROP (:DV 2 1)
                               (:REWRITE CDR-CONS)
                               :TOP (:DV 2)
                               :EXPAND
                               :S-PROP :TOP (:REWRITE CONS-EQUAL)
                               :S-PROP))

(DEFTHM PROBLEM72
        (EQUAL (PLUS (PLUS I J) K)
               (PLUS I (PLUS J K)))
        :INSTRUCTIONS (:INDUCT (:DV 1 1)
                               :EXPAND :S-PROP :UP :UP (:DV 2 2)
                               :UP :EXPAND :S-PROP (:REWRITE LEMMA3-72)
                               :TOP (:DV 1)
                               (:REWRITE LEMMA2-72)
                               :TOP :S-PROP (:DV 1 1)
                               :EXPAND
                               :S-PROP :UP :EXPAND :S-PROP (:DV 2 1)
                               (:REWRITE CDR-CONS)
                               :TOP (:DV 2)
                               :EXPAND
                               :S-PROP :TOP (:REWRITE CONS-EQUAL)
                               :S-PROP))

;-------------------------------------------------

;problem 73

(DEFTHM LEMMA1-73
        (IMPLIES (NOT (CONSP Y))
                 (EQUAL (PLUS X Y) (MAPNIL X)))
        :INSTRUCTIONS (:INDUCT (:DV 2 1)
                               :EXPAND :S-PROP :TOP :PROMOTE (:DV 1)
                               :EXPAND :S-PROP :UP (:DV 2)
                               :EXPAND :S-PROP (:DV 2 1)
                               :EXPAND :S-PROP :UP (:DV 2)
                               :EXPAND
                               :S-PROP :UP (:REWRITE CONS-EQUAL)
                               :TOP (:DEMOTE 2)
                               :S-PROP))

(DEFTHM LEMMA2-73
        (EQUAL (CONS NIL (PLUS I J))
               (PLUS I (CONS X J)))
        :INSTRUCTIONS (:INDUCT (:DV 1 2)
                               :EXPAND :S-PROP :TOP (:DV 2)
                               :EXPAND
                               :S-PROP :EXPAND :S-PROP (:DV 2 1)
                               (:REWRITE CDR-CONS)
                               :TOP :S-PROP (:DV 1 2)
                               :EXPAND :S-PROP :TOP (:DV 2)
                               :EXPAND
                               :S-PROP :TOP (:REWRITE CONS-EQUAL)
                               :S-PROP))


(DEFTHM LEMMA3-73
        (IMPLIES (CONSP Y)
                 (EQUAL (PLUS X (CONS I (CDR Y)))
                        (PLUS X Y)))
        :INSTRUCTIONS (:INDUCT :PROMOTE (:DV 1)
                               :EXPAND
                               :S-PROP :EXPAND :S-PROP (:DV 2 1)
                               (:REWRITE CDR-CONS)
                               :TOP (:DV 2)
                               :EXPAND :S-PROP
                               :EXPAND :S-PROP :TOP :S-PROP (:DV 2 1)
                               :EXPAND :S-PROP :UP (:DV 2)
                               :EXPAND
                               :S-PROP :UP (:REWRITE CONS-EQUAL)
                               :TOP (:DEMOTE 2)
                               :S-PROP))


(DEFTHM PROBLEM73 (EQUAL (PLUS I J) (PLUS J I))
        :INSTRUCTIONS (:INDUCT (:DV 1)
                               :EXPAND :S-PROP :UP (:DV 2)
                               :EXPAND :TOP :SPLIT (:DV 2 2)
                               (:REWRITE LEMMA1-73)
                               :TOP (:DV 1)
                               :EXPAND :S-PROP :TOP :S-PROP (:DV 1)
                               :EXPAND :S-PROP :UP (:DV 2)
                               :EXPAND :S-PROP (:DV 1)
                               :TOP (:DV 1)
                               :EXPAND :S-PROP :TOP (:DV 2)
                               :EXPAND
                               :TOP :SPLIT (:REWRITE CONS-EQUAL)
                               (:DV 1)
                               :TOP (:DV 1)
                               :TOP (:DV 2)
                               (:DV 1)
                               :TOP :S-PROP (:DV 1)
                               :EXPAND :S-PROP :TOP (:DV 1)
                               (:REWRITE LEMMA2-73)
                               :TOP (:DV 1)
                               (:REWRITE LEMMA3-73)
                               :TOP :S-PROP (:DV 1 2)
                               :EXPAND
                               :S-PROP :UP
                               :UP (:DV 2)
                               :EXPAND :S-PROP
                               :TOP :S-PROP))

;-------------------------------------------------

;problem 74


(DEFTHM LEMMA1-74
        (EQUAL (TIMES (MAPNIL B) C) (TIMES B C))
        :INSTRUCTIONS (:INDUCT (:DV 1 1)
                               :EXPAND
                               :S-PROP :UP :EXPAND :S-PROP :UP (:DV 2)
                               :EXPAND :S-PROP (:DV 1)
                               (:DV 1)
                               :EXPAND
                               :S-PROP :UP :EXPAND :S-PROP (:DV 2 1)
                               (:REWRITE CDR-CONS)
                               :UP :UP (:REWRITE PROBLEM73)
                               :TOP (:DV 2)
                               :EXPAND
                               :S-PROP (:REWRITE PROBLEM73)
                               :TOP :S-PROP))


(DEFTHM LEMMA2-74
        (EQUAL (MAPNIL (TIMES B C)) (TIMES B C))
        :INSTRUCTIONS (:INDUCT (:DV 1 1)
                               :EXPAND
                               :S-PROP :UP :EXPAND :S-PROP :UP (:DV 2)
                               :EXPAND :S-PROP (:DV 1 1)
                               :EXPAND :S-PROP (:REWRITE PROBLEM73)
                               :UP (:REWRITE LEMMA3-72)
                               :TOP (:DV 2)
                               :EXPAND
                               :S-PROP (:REWRITE PROBLEM73)
                               :TOP :S-PROP))


(DEFTHM LEMMA3-74
        (EQUAL (TIMES (PLUS A B) C)
               (PLUS (TIMES A C) (TIMES B C)))
        :INSTRUCTIONS (:INDUCT (:DV 1 1)
                               :EXPAND :S-PROP :TOP (:DV 2 1)
                               :EXPAND
                               :S-PROP :UP :EXPAND :S-PROP :TOP (:DV 1)
                               (:REWRITE LEMMA1-74)
                               :TOP (:DV 2)
                               (:REWRITE LEMMA2-74)
                               :TOP :S-PROP (:DV 1 1)
                               :EXPAND
                               :S-PROP :UP :EXPAND :S-PROP (:DV 2 1)
                               (:REWRITE CDR-CONS)
                               :UP :UP (:REWRITE PROBLEM73)
                               :TOP (:DV 2 1)
                               :EXPAND :S-PROP :UP (:REWRITE PROBLEM72)
                               (:REWRITE PROBLEM73)
                               :TOP :S-PROP))


(DEFTHM PROBLEM74
        (EQUAL (TIMES (TIMES I J) K)
               (TIMES I (TIMES J K)))
        :INSTRUCTIONS (:INDUCT (:DV 1 1)
                               :EXPAND
                               :S-PROP :UP :EXPAND :S-PROP :UP (:DV 2)
                               :EXPAND :S-PROP (:DV 1 1)
                               :EXPAND :S-PROP :UP :TOP (:DV 2)
                               :EXPAND :S-PROP :TOP (:DV 1)
                               (:REWRITE LEMMA3-74)
                               (:REWRITE PROBLEM73)
                               :TOP (:DV 2)
                               (:REWRITE PROBLEM73)
                               :TOP :S-PROP))





