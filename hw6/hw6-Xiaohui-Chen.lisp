;-----------------Problem 1-------------------

;function definitions

(defun mc-flatten (x a)
	(if (atom x)
	    (cons x a)
	    (mc-flatten (car x)
			(mc-flatten (cdr x) a))))

;proof of theorem

(DEFTHM PROBLEM1
        (IMPLIES (TRUE-LISTP A)
                 (TRUE-LISTP (MC-FLATTEN X A)))
        :INSTRUCTIONS (:INDUCT (:DV 2 1)
                               :EXPAND
                               :S-PROP :TOP :PROMOTE (:FORWARDCHAIN 3)
                               (:FORWARDCHAIN 2)
                               :S-PROP (:DV 2 1)
                               :EXPAND
                               :S-PROP :UP
                               :EXPAND :S-PROP
                               :TOP :S-PROP))

;-----------------Problem 2-------------------

;function definitions

(defun app (x y)
	(if (atom x)
	    y
	    (cons (car x) (app (cdr x) y))))

(defun flatten (x)
	 (if (atom x)
	     (list x)
             (app (flatten (car x))
		  (flatten (cdr x)))))

(defthm problem40 (equal (app (app a b) c)
                             (app a (app b c))))


;proof of theorem

(DEFTHM PROBLEM2-LEMMA
        (IMPLIES (TRUE-LISTP Y)
                 (TRUE-LISTP (APP X Y)))
        :INSTRUCTIONS (:INDUCT (:DV 2 1)
                               :EXPAND
                               :S-PROP :UP :EXPAND :S-PROP (:DV 1)
                               (:REWRITE CDR-CONS)
                               :TOP :PROMOTE (:FORWARDCHAIN 2)
                               :S-PROP (:DV 2 1)
                               :EXPAND
                               :S-PROP :UP
                               :UP :S-PROP))

(DEFTHM PROBELM2
        (IMPLIES (TRUE-LISTP Y)
                 (EQUAL (MC-FLATTEN X Y)
                        (APP (FLATTEN X) Y)))
        :INSTRUCTIONS (:INDUCT :PROMOTE (:FORWARDCHAIN 3)
                               (:FORWARDCHAIN 2)
                               (:DV 1)
                               :EXPAND :S-PROP :TOP (:DV 2 1)
                               :EXPAND :S-PROP :UP (:REWRITE PROBLEM40)
                               (:DV 2)
                               :TOP :SL (:DV 2 1)
                               :EXPAND :S-PROP :UP (:DV 2 1)
                               :EXPAND
                               :S-PROP :UP :EXPAND :S-PROP (:DV 1)
                               (:REWRITE CAR-CONS)
                               :UP (:DV 2 1)
                               (:REWRITE CDR-CONS)
                               :UP :EXPAND
                               :S-PROP :UP
                               :TOP :S-PROP))

;-----------------Problem 3-------------------

;function definitions

(defun mem (x l)
	(if (atom l)
	    nil
            (if (equal x (car l))
	        l
		(mem x (cdr l)))))

;proof of actual theorem


(DEFTHM PROBLEM3
        (IFF (MEM E (APP A B))
             (OR (MEM E A) (MEM E B)))
        :INSTRUCTIONS ((:INDUCT (MEM E A))
                       (:DIVE 1 2)
                       :EXPAND
                       :S-PROP :UP :EXPAND :S-PROP (:DIVE 1 2)
                       (:REWRITE CAR-CONS)
                       :UP :S-PROP :UP :S-PROP (:DIVE 2)
                       (:REWRITE CDR-CONS)
                       :TOP (:DIVE 2 1)
                       :EXPAND :S-PROP :UP :S :UP (:DEMOTE 3)
                       :S-PROP (:DIVE 1 2)
                       :EXPAND
                       :S-PROP :UP :EXPAND :S-PROP (:DIVE 1 2)
                       (:REWRITE CAR-CONS)
                       :UP :S-PROP
                       :UP :S-PROP :UP :S-PROP (:DIVE 1)
                       :EXPAND :S-PROP :TOP :S-PROP (:DIVE 1 2)
                       :EXPAND
                       :S-PROP :UP
                       :TOP (:DIVE 2 1)
                       :EXPAND :S-PROP
                       :UP :S-PROP
                       :TOP :S-PROP))




;-----------------Problem 4-------------------

;function definitions

;symbol-listp is redundant. Therefore I used the abbreviation slp

(defun slp (lst)
	(cond ((atom lst) (eq lst nil))
	      (t (and (symbolp (car lst))
		      (slp (cdr lst))))))

;proof of actual theorem

(DEFTHM PROBLEM4
        (IMPLIES (SLP L)
                 (SYMBOLP (CAR (MEM X L))))
        :INSTRUCTIONS (:INDUCT (:DIVE 1)
                               :EXPAND :S-PROP :TOP (:DV 2 1 1)
                               :EXPAND
                               :S-PROP :TOP :PROMOTE (:FORWARDCHAIN 3)
                               :S-PROP (:DIVE 1)
                               :EXPAND :S-PROP :TOP (:DV 2 1 1)
                               :EXPAND :S-PROP :TOP (:DV 1 2)
                               :TOP
                               :S (:DV 2 1 1)
                               :EXPAND :S-PROP
                               :TOP :S-PROP))

;-----------------Problem 5------------------

;function definitions

(defun xor (p q)
    (if p 
	(if q nil t)
	(if q t nil)))

(defun for (x y)
    (if x t y))

(defun fand (x y)
    (if x y nil))

(defun b-carry (a b c)
    (if a 
        (for b c)
        (fand b c)))

(defun ln (x)
    (if (atom x)
	nil
	(cons nil (ln (cdr x)))))

(defun blp (x)
    (if (atom x)
	(null x)
	(and (or (equal (car x) t)
		 (equal (car x) nil))
	     (blp (cdr x)))))

(defun v-add (c a b)
    (if (atom a)
	(list c)
	(cons (xor c (xor (car a) (car b)))
	      (v-add (b-carry c (car a) (car b))
		     (cdr a)
		     (cdr b)))))

;proof of actual theorem

(DEFTHM PROBLEM5-LEMMA1
        (IMPLIES (AND (BLP A)
                      (BLP B)
                      (EQUAL (LN A) (LN B)))
                 (EQUAL (B-CARRY C (CAR A) (CAR B))
                        (B-CARRY C (CAR B) (CAR A))))
        :INSTRUCTIONS ((:DV 1 1)
                       :EXPAND :UP (:DV 2)
                       :EXPAND :TOP :PROMOTE (:DEMOTE 1)
                       (:DEMOTE 1)
                       :SPLIT (:DV 1)
                       :EXPAND :S-PROP (:DV 2)
                       :EXPAND :TOP (:DV 2)
                       :EXPAND
                       :S-PROP :TOP
                       :S (:DV 1)
                       :EXPAND :S-PROP
                       :TOP (:DV 2)
                       :EXPAND :S-PROP
                       :TOP :S
                       :S :S))

(DEFTHM PROBLEM5
        (IMPLIES (AND (BLP A)
                      (BLP B)
                      (EQUAL (LN A) (LN B)))
                 (EQUAL (V-ADD C A B) (V-ADD C B A)))
        :INSTRUCTIONS ((:INDUCT (V-ADD C A B))
                       :PROMOTE (:FORWARDCHAIN 2)
                       (:DV 1)
                       :EXPAND :S-PROP :TOP (:DV 2)
                       :EXPAND
                       :TOP :SPLIT (:REWRITE CONS-EQUAL)
                       (:DV 1)
                       :S :S :TOP :S-PROP (:DV 2 1)
                       (:REWRITE PROBLEM5-LEMMA1)
                       :TOP :S-PROP (:DEMOTE 4)
                       (:DV 1 1)
                       :EXPAND :S-PROP :UP (:DV 2)
                       :EXPAND :S-PROP
                       :UP :S-PROP :TOP :S-PROP (:DV 1 1)
                       :EXPAND :S-PROP :UP (:DV 2)
                       :EXPAND :S-PROP :TOP :SPLIT (:DEMOTE 4)
                       (:DV 1 1)
                       :EXPAND :S-PROP :UP (:DV 2)
                       :EXPAND :S-PROP
                       :UP :S-PROP :TOP :S-PROP (:DEMOTE 4)
                       (:DV 1)
                       (:DV 1)
                       :EXPAND :S-PROP
                       :UP (:DV 2)
                       :EXPAND :S-PROP
                       :UP :S-PROP
                       :TOP :S-PROP))




