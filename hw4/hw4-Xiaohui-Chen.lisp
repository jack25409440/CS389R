;definition of functions

(defun mem (e x)
  (if (consp x)
      (if (equal e (car x))
          t
        (mem e (cdr x)))
    nil))

(defun rmove (e x)
        (if (consp x)
            (if (equal e (car x))
                (cdr x)
                (cons (car x) (rmove e (cdr x))))
            nil))


(defun perm (x y)
        (if (consp x)
            (if (mem (car x) y)
                (perm (cdr x) (rmove (car x) y))
                nil)
            t))

;------------------------------------------------------

;Problem 53

(DEFTHM LEMMA1
        (IMPLIES (CONSP X) (MEM (CAR X) X))
        :INSTRUCTIONS (:INDUCT :S-PROP :S-PROP
                               :EXPAND :S-PROP))

(DEFTHM LEMMA2 (EQUAL (RMOVE (CAR X) X) (CDR X))
        :INSTRUCTIONS (:INDUCT (:DV 1)
                               :EXPAND :S-PROP :TOP (:DV 2)
                               (:REWRITE DEFAULT-CDR)
                               (:DV 1)
                               :EXPAND
                               :S-PROP (:DV 1)
                               :EXPAND :S-PROP
                               :TOP :S-PROP))

(DEFTHM PROBLEM-53 (PERM X X)
        :INSTRUCTIONS (:INDUCT :EXPAND
                               :S-PROP :EXPAND :S-PROP (:USE LEMMA1)
                               :EXPAND :S-PROP (:USE LEMMA1)
                               (:USE LEMMA2)
                               :S-PROP))

;------------------------------------------------------

;Problem 61

(defun app (x y)
  (if (consp x)
      (cons (car x) (app (cdr x) y))
    y))

(defun rev1 (x a)
        (if (consp x)
            (rev1 (cdr x) (cons (car x) a))
            a))

(defun rev (x)
  (if (consp x)
      (app (rev (cdr x)) (cons (car x) nil))
    nil))

(defun true-list (x)
  (if (consp x)
      (true-list (cdr x))
    (equal x nil)))


(DEFTHM problem-40 
        (EQUAL (APP (APP A B) C) 
	       (APP A (APP B C))))




(DEFTHM LEMMA3
        (EQUAL (REV1 X A) (APP (REV X) A))
        :INSTRUCTIONS (:INDUCT (:DV 2)
                               :EXPAND (:DV 1)
                               (:DV 1)
                               :EXPAND :S-PROP :UP :S-PROP :TOP (:DV 1)
                               :EXPAND :S-PROP :TOP :S-PROP (:DV 1)
                               :EXPAND :S-PROP :TOP (:DV 2)
                               (:DV 1)
                               :EXPAND :S-PROP :TOP (:DV 2)
                               :TOP (:USE PROBLEM-40)
                               :PROMOTE (:DV 1)
                               :TOP (:DV 2)
                               (:REWRITE PROBLEM-40)
                               (:DV 2)
                               :EXPAND :S-PROP (:DV 1)
                               (:REWRITE CAR-CONS)
                               :UP (:DV 2)
                               (:DV 1)
                               (:DV 1)
                               :UP (:REWRITE CDR-CONS)
                               :UP :EXPAND
                               :S-PROP :UP
                               :TOP :S-PROP))

(DEFTHM LEMMA4
        (EQUAL (TRUE-LIST (APP X Y))
               (TRUE-LIST Y))
        :INSTRUCTIONS ((:INDUCT (APP X Y))
                       (:DV 1)
                       (:DV 1)
                       :EXPAND :S-PROP :TOP :S-PROP (:DV 1 1)
                       :EXPAND :S-PROP :TOP (:DV 1)
                       :EXPAND :S-PROP (:DV 1)
                       (:REWRITE CDR-CONS)
                       :TOP :S-PROP))


(DEFTHM LEMMA5 (TRUE-LIST (REV X))
        :INSTRUCTIONS ((:INDUCT (REV X))
                       (:DV 1)
                       :EXPAND
                       :S-PROP :TOP :EXPAND :S-PROP (:DV 1)
                       :EXPAND :S-PROP :TOP (:USE LEMMA4)
                       :PROMOTE (:REWRITE LEMMA4)
                       :EXPAND :S-PROP (:DV 1)
                       (:REWRITE CDR-CONS)
                       :UP
                       :EXPAND :S-PROP))

(DEFTHM LEMMA6
        (IMPLIES (TRUE-LIST X)
                 (EQUAL (APP X NIL) X))
        :INSTRUCTIONS (:INDUCT (:DV 1)
                               :EXPAND :S-PROP :TOP (:DV 2)
                               (:DV 1)
                               :EXPAND :S-PROP :UP :UP :S-PROP (:DV 1)
                               :EXPAND :S-PROP :TOP (:DV 2 1)
                               :EXPAND :S-PROP (:DV 2)
                               :UP (:DV 2)
                               :TOP :PROMOTE (:DV 1)
                               (:DV 2)
                               :TOP (:DEMOTE 2)
                               :DEMOTE (:DV 2)
                               :TOP :PROMOTE
                               :PROMOTE :DEMOTE :PROMOTE (:DEMOTE 2)
                               (:DEMOTE 2)
                               :S))

(DEFTHM PROBLEM-61 (EQUAL (REV1 X NIL) (REV X))
        :INSTRUCTIONS (:INDUCT (:DV 2)
                               :EXPAND :S-PROP :TOP (:DV 1)
                               :EXPAND :S-PROP (:USE LEMMA3)
                               :PROMOTE (:DV 1)
                               (:REWRITE LEMMA3)
                               :TOP (:USE LEMMA5)
                               :PROMOTE (:USE LEMMA6)
                               :PROMOTE (:DV 1)
                               (:REWRITE LEMMA6)
                               :TOP :S-PROP))


