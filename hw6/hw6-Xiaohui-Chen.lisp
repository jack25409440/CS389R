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

;proof of actual theorems


(DEFTHM PROBLEM3-PART2
        (IMPLIES (OR (MEM E A) (MEM E B))
                 (MEM E (APP A B)))
        :INSTRUCTIONS ((:INDUCT (MEM E A))
                       (:DIVE 1 1)
                       :EXPAND (:DV 1)
                       :S-PROP :UP (:DV 2)
                       :S-PROP :TOP (:DV 1 2)
                       :EXPAND (:DV 1)
                       :S-PROP :UP (:DV 2)
                       :S-PROP :UP :TOP (:DV 2 2)
                       :EXPAND :S-PROP :UP :EXPAND (:DV 1)
                       :S-PROP :UP (:DV 2)
                       (:DV 1 2)
                       (:REWRITE CAR-CONS)
                       :UP :UP :S-PROP (:DV 2)
                       (:REWRITE CDR-CONS)
                       :UP :UP :TOP (:DEMOTE 3)
                       :S-PROP (:DIVE 1 1)
                       :EXPAND (:DV 1)
                       :S-PROP :UP (:DV 2)
                       :S-PROP :UP :S-PROP :EXPAND (:DV 1)
                       :S-PROP :UP (:DV 2)
                       :S-PROP :UP :S-PROP (:DV 2)
                       :EXPAND :S-PROP :UP :EXPAND (:DV 1)
                       :S-PROP :UP (:DV 2)
                       (:DV 1 2)
                       (:REWRITE CAR-CONS)
                       :UP :S-PROP :TOP :S-PROP (:DIVE 1 1)
                       :EXPAND
                       :S-PROP :UP :S-PROP :TOP (:DV 2 2)
                       :EXPAND
                       :S-PROP :UP
                       :TOP :S-PROP))

(DEFTHM PROBLEM3-PART1
        (IMPLIES (MEM E (APP A B))
                 (OR (MEM E A) (MEM E B)))
        :INSTRUCTIONS ((:INDUCT (MEM E A))
                       (:DIVE 2 1)
                       :EXPAND :S-PROP :UP (:DV 2)
                       :EXPAND :S-PROP :UP :UP (:DV 1 2)
                       :EXPAND
                       :S-PROP :UP :EXPAND :S-PROP (:DV 1 2)
                       (:REWRITE CAR-CONS)
                       :UP :S-PROP :UP :S-PROP (:DV 2)
                       (:REWRITE CDR-CONS)
                       :TOP :DEMOTE :S-PROP (:DIVE 2 1)
                       :EXPAND
                       :S-PROP :UP :S-PROP :UP (:DV 1 2)
                       :EXPAND :S-PROP :UP :EXPAND (:DV 2)
                       (:DV 1 2)
                       (:REWRITE CAR-CONS)
                       :UP :UP :S-PROP :UP :UP :S (:DIVE 2 1)
                       :EXPAND
                       :S-PROP :UP :S-PROP :UP (:DV 1 2)
                       :EXPAND
                       :S-PROP :UP
                       :TOP :S-PROP))






;-----------------Problem 4-------------------

;function definitions





