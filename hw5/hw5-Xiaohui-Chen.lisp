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

(DEFTHM LEMMA1-71
        (IMPLIES (AND (CONSP X) (EQUAL X Y))
                 (EQUAL (CDR X) (CDR Y)))
        :INSTRUCTIONS (:PROMOTE :S-PROP))


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

