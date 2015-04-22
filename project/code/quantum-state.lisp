;-----------------Quantum State----------------------

(defun get-jstate (x)
	(car x))

(defun get-coupled-state (x)
	(cdr x))

(defun sum-of-coupled-coefficient (a)
	(if (atom a)
	    0
	    (+ (first-coupled-coefficient a)
	       (sum-of-coupled-coefficient (cdr a)))))

(defun good-quantum-numbers-helper (x y)
	(if (atom y)
	    t
	    (and (equal (quantum-j x)
			(+ (first-coupled-l y)
			   (first-coupled-s y)))
		 (equal (quantum-mj x)
			(+ (first-coupled-ml y)
			   (first-coupled-ms y)))
		 (good-quantum-numbers-helper x (cdr y)))))

(defun good-quantum-numbers (x)
	(if (and (equal (get-jstate x) 0)
		 (equal (get-coupled-state x) 0))
	    t
	    (good-quantum-numbers-helper (get-jstate x) 
					 (get-coupled-state x))))
	
(defun equal-j (x y)
	(if (atom y)
	    t
	    (and (equal (quantum-j x)
			(+ (first-coupled-l y)
			   (first-coupled-s y)))
		 (equal-j x (cdr y)))))

(defun equal-mj (x y)
	(if (atom y)
	    t
	    (and (equal (quantum-mj x)
			(+ (first-coupled-ml y)
			   (first-coupled-ms y)))
		 (equal-mj x (cdr y)))))


(defun true-quantum-state (x)
	(xor (and (equal (get-jstate x) 0)
		  (equal (get-coupled-state x) 0))
	     (and (true-jstate (get-jstate x))
		  (true-coupled-state (get-coupled-state x))
		  (equal (sum-of-coupled-coefficient 
				(get-coupled-state x))
			 (caar x))
		  (equal-j (get-jstate x) 
			   (get-coupled-state x))
		  (equal-mj (get-jstate x)
			    (get-coupled-state x)))))

(defun normalize-helper (a y)
	(if (atom y)
	    y
	    (cons (cons (/ (first-coupled-coefficient y) a) 
		        (first-coupled-state-pair y))
		  (normalize-helper a (cdr y)))))

(defun normalize-state (x)
	(if (and (equal (get-jstate x) 0)
		 (equal (get-coupled-state x) 0))
	    x
	    (if (< 0 (car (get-jstate x)))
	        (cons (cons '1 (cdr (get-jstate x)))
		          (normalize-helper (car (get-jstate x)) 
					(get-coupled-state x)))
		(cons '0 '0))))	

(defthm normalize-lemma1 
	(implies (and (consp y)
		      (rationalp a))
		 (consp (normalize-helper a y))))

(defthm normalize-lemma2
	(implies (and (consp y)
		      (true-coupled-list y)
		      (rationalp a)
		      (< 0 a))
		 (equal (sum-of-coupled-coefficient 
				(normalize-helper a y))
			(/ (sum-of-coupled-coefficient y)
			   a))) 
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities))))

(defthm normalize-lemma3 
	(implies (and (consp y)
		      (true-coupled-list y)
		      (rationalp a)
		      (< 0 a))
		 (true-coupled-list (normalize-helper a y)))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities))))

(defun pairs-same (x y)
	(if (atom x)
	    (if (atom y)
	        t
		nil)
	    (and (equal (first-coupled-state-pair x)
			(first-coupled-state-pair y))
		 (pairs-same (cdr x) (cdr y)))))

(defthm normalize-lemma4
	(implies (and (true-quantum-state x)
		      (not (equal (get-jstate x) 0))
		      (not (equal (get-coupled-state x) 0))
		      (< 0 (car (get-jstate x))))
		 (and (equal (quantum-j 
			       (get-jstate (normalize-state x)))
		             (quantum-j 
			        (get-jstate x)))
		      (equal (quantum-mj 
				(get-jstate (normalize-state x)))
			     (quantum-mj
				(get-jstate x)))))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities))))

(defthm normalize-lemma5
	(implies (and (true-quantum-state x)
		      (not (equal (get-jstate x) 0))
		      (not (equal (get-coupled-state x) 0))
		      (< 0 (car (get-jstate x))))
		 (let ((a (get-coupled-state 
				(normalize-state x)))
		       (b (get-coupled-state x)))
	    	  (pairs-same a b))) 	
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities)
		:induct (pairs-same a b))))

(defthm normalize-lemma6
	(IMPLIES (AND (CONSP (CAR X))
              (RATIONALP (CAAR X))
              (<= 0 (CAAR X))
              (CONSP (CDAR X))
              (RATIONALP (CADAR X))
              (< 0 (CADAR X))
              (RATIONALP (CDDAR X))
              (< (CDDAR X) 0)
              (INTEGERP (+ (CADAR X) (CDDAR X)))
              (<= (- (CDDAR X)) (CADAR X))
              (NOT (INTEGERP (CADAR X)))
              (EQUAL (DENOMINATOR (CADAR X)) 2)
              (NOT (INTEGERP (CDDAR X)))
              (EQUAL (DENOMINATOR (CDDAR X)) 2)
              (CONSP (CDR X))
              (TRUE-COUPLED-LIST (CDR X))
              (EQUAL (SUM-OF-COUPLED-COEFFICIENT (CDR X))
                     (CAAR X))
              (EQUAL-J (CAR X) (CDR X))
              (EQUAL-MJ (CAR X) (CDR X))
              (< 0 (CAAR X)))
	 (let ((a (cons 1 (cdar x)))
	       (b (normalize-helper (caar x) (cdr x))))
               (EQUAL-J a b)))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities)
		:induct (equal-j a b))))

(defthm normalize-lemma7
	(IMPLIES (AND (CONSP (CAR X))
              (RATIONALP (CAAR X))
              (<= 0 (CAAR X))
              (CONSP (CDAR X))
              (RATIONALP (CADAR X))
              (< 0 (CADAR X))
              (RATIONALP (CDDAR X))
              (< (CDDAR X) 0)
              (INTEGERP (+ (CADAR X) (CDDAR X)))
              (<= (- (CDDAR X)) (CADAR X))
              (NOT (INTEGERP (CADAR X)))
              (EQUAL (DENOMINATOR (CADAR X)) 2)
              (NOT (INTEGERP (CDDAR X)))
              (EQUAL (DENOMINATOR (CDDAR X)) 2)
              (CONSP (CDR X))
              (TRUE-COUPLED-LIST (CDR X))
              (EQUAL (SUM-OF-COUPLED-COEFFICIENT (CDR X))
                     (CAAR X))
              (EQUAL-J (CAR X) (CDR X))
              (EQUAL-MJ (CAR X) (CDR X))
              (< 0 (CAAR X)))
	 (let ((a (cons 1 (cdar x)))
	       (b (normalize-helper (caar x) (cdr x))))
               (EQUAL-MJ a b)))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities)
		:induct (equal-j a b))))

(defthm normalize-lemma8
	(IMPLIES (AND (CONSP (CAR X))
              (RATIONALP (CAAR X))
              (<= 0 (CAAR X))
              (CONSP (CDAR X))
              (< 0 (CADAR X))
              (< (CDDAR X) 0)
              (<= (- (CDDAR X)) (CADAR X))
              (INTEGERP (CADAR X))
              (INTEGERP (CDDAR X))
              (CONSP (CDR X))
              (TRUE-COUPLED-LIST (CDR X))
              (EQUAL (SUM-OF-COUPLED-COEFFICIENT (CDR X))
                     (CAAR X))
              (EQUAL-J (CAR X) (CDR X))
              (EQUAL-MJ (CAR X) (CDR X))
              (< 0 (CAAR X)))
	 (let ((a (cons 1 (cdar x)))
	       (b (normalize-helper (caar x) (cdr x))))
               (EQUAL-MJ a b)))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities)
		:induct (equal-j a b))))

(defthm normalize-lemma9
	(IMPLIES (AND (CONSP (CAR X))
              (RATIONALP (CAAR X))
              (<= 0 (CAAR X))
              (CONSP (CDAR X))
              (< 0 (CADAR X))
              (< (CDDAR X) 0)
              (<= (- (CDDAR X)) (CADAR X))
              (INTEGERP (CADAR X))
              (INTEGERP (CDDAR X))
              (CONSP (CDR X))
              (TRUE-COUPLED-LIST (CDR X))
              (EQUAL (SUM-OF-COUPLED-COEFFICIENT (CDR X))
                     (CAAR X))
              (EQUAL-J (CAR X) (CDR X))
              (EQUAL-MJ (CAR X) (CDR X))
              (< 0 (CAAR X)))
	 (let ((a (cons 1 (cdar x)))
	       (b (normalize-helper (caar x) (cdr x))))
               (EQUAL-J a b)))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities)
		:induct (equal-j a b))))

(defthm normalize-lemma10
	(IMPLIES (AND (CONSP (CAR X))
              (RATIONALP (CAAR X))
              (<= 0 (CAAR X))
              (CONSP (CDAR X))
              (RATIONALP (CADAR X))
              (< 0 (CADAR X))
              (RATIONALP (CDDAR X))
              (<= 0 (CDDAR X))
              (INTEGERP (+ (CADAR X) (- (CDDAR X))))
              (<= (CDDAR X) (CADAR X))
              (NOT (INTEGERP (CADAR X)))
              (EQUAL (DENOMINATOR (CADAR X)) 2)
              (NOT (INTEGERP (CDDAR X)))
              (EQUAL (DENOMINATOR (CDDAR X)) 2)
              (CONSP (CDR X))
              (TRUE-COUPLED-LIST (CDR X))
              (EQUAL (SUM-OF-COUPLED-COEFFICIENT (CDR X))
                     (CAAR X))
              (EQUAL-J (CAR X) (CDR X))
              (EQUAL-MJ (CAR X) (CDR X))
              (< 0 (CAAR X)))
	 (let ((a (cons 1 (cdar x)))
	       (b (normalize-helper (caar x) (cdr x))))
               (EQUAL-J a b)))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities)
		:induct (equal-j a b))))

(defthm normalize-lemma11
	(IMPLIES (AND (CONSP (CAR X))
              (RATIONALP (CAAR X))
              (<= 0 (CAAR X))
              (CONSP (CDAR X))
              (RATIONALP (CADAR X))
              (< 0 (CADAR X))
              (RATIONALP (CDDAR X))
              (<= 0 (CDDAR X))
              (INTEGERP (+ (CADAR X) (- (CDDAR X))))
              (<= (CDDAR X) (CADAR X))
              (NOT (INTEGERP (CADAR X)))
              (EQUAL (DENOMINATOR (CADAR X)) 2)
              (NOT (INTEGERP (CDDAR X)))
              (EQUAL (DENOMINATOR (CDDAR X)) 2)
              (CONSP (CDR X))
              (TRUE-COUPLED-LIST (CDR X))
              (EQUAL (SUM-OF-COUPLED-COEFFICIENT (CDR X))
                     (CAAR X))
              (EQUAL-J (CAR X) (CDR X))
              (EQUAL-MJ (CAR X) (CDR X))
              (< 0 (CAAR X)))
	 (let ((a (cons 1 (cdar x)))
	       (b (normalize-helper (caar x) (cdr x))))
               (EQUAL-MJ a b)))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities)
		:induct (equal-j a b))))

(defthm normalize-lemma12
	(IMPLIES (AND (CONSP (CAR X))
              (RATIONALP (CAAR X))
              (<= 0 (CAAR X))
              (CONSP (CDAR X))
              (< 0 (CADAR X))
              (<= 0 (CDDAR X))
              (INTEGERP (+ (CADAR X) (- (CDDAR X))))
              (<= (CDDAR X) (CADAR X))
              (INTEGERP (CADAR X))
              (INTEGERP (CDDAR X))
              (CONSP (CDR X))
              (TRUE-COUPLED-LIST (CDR X))
              (EQUAL (SUM-OF-COUPLED-COEFFICIENT (CDR X))
                     (CAAR X))
              (EQUAL-J (CAR X) (CDR X))
              (EQUAL-MJ (CAR X) (CDR X))
              (< 0 (CAAR X)))
	 (let ((a (cons 1 (cdar x)))
	       (b (normalize-helper (caar x) (cdr x))))
               (EQUAL-J a b)))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities)
		:induct (equal-j a b))))

(defthm normalize-lemma13
	(IMPLIES (AND (CONSP (CAR X))
              (RATIONALP (CAAR X))
              (<= 0 (CAAR X))
              (CONSP (CDAR X))
              (< 0 (CADAR X))
              (<= 0 (CDDAR X))
              (INTEGERP (+ (CADAR X) (- (CDDAR X))))
              (<= (CDDAR X) (CADAR X))
              (INTEGERP (CADAR X))
              (INTEGERP (CDDAR X))
              (CONSP (CDR X))
              (TRUE-COUPLED-LIST (CDR X))
              (EQUAL (SUM-OF-COUPLED-COEFFICIENT (CDR X))
                     (CAAR X))
              (EQUAL-J (CAR X) (CDR X))
              (EQUAL-MJ (CAR X) (CDR X))
              (< 0 (CAAR X)))
	 (let ((a (cons 1 (cdar x)))
	       (b (normalize-helper (caar x) (cdr x))))
               (EQUAL-MJ a b)))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities)
		:induct (equal-j a b))))

(defthm normalize-valid
	(implies (true-quantum-state x)
		 (true-quantum-state (normalize-state x)))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities
				default-less-than-1
				default-less-than-2
				default-plus-1
				default-rational-denominator
				|(+ x (if a b c))|
				|(- (if a b c))|
				|(< (if a b c) x)|
				|(< x (if a b c))|
				DEFAULT-MINUS
				DEFAULT-PLUS-2))))

;-----------------Quantum Operator---------------

(defun quantum-operator-helper (x)
       (cons (j-lowering-operator (get-jstate x))
	     (append-and-merge-states 
		(l-lowering-operator (get-coupled-state x))
		(s-lowering-operator (get-coupled-state x)))))

(defun quantum-operator (x)
	(if (and (equal (get-jstate x) 0)
		 (equal (get-coupled-state x) 0))
	    x
	    (quantum-operator-helper (normalize-state x))))

(defun initial-quantum-state (x)
	(and (equal (j-coefficient (get-jstate x)) 1)
	     (equal (first-coupled-coefficient 
			    (get-coupled-state x)) 
		    1)
	     (equal (len (get-coupled-state x)) 1)
	     (equal (quantum-j (get-jstate x))
		    (quantum-mj (get-jstate x)))
	     (equal (first-coupled-l (get-coupled-state x))
		    (first-coupled-ml (get-coupled-state x)))
	     (equal (first-coupled-s (get-coupled-state x))
		    (first-coupled-ms (get-coupled-state x)))
	     (true-quantum-state x)))


(defthm initial-quantum-state-valid 
	(implies (initial-quantum-state x)
		 (true-quantum-state x))
:hints (("Goal" :in-theory (disable same-denominator-add 
			        remove-strict-inequalities 
				remove-weak-inequalities))))
(defthm initial-state-lemma-1
	(implies (initial-quantum-state x)
		 (not (initial-quantum-state 
			   (quantum-operator x))))
:hints (("Goal" :in-theory (disable same-denominator-add 
			        remove-strict-inequalities 
				remove-weak-inequalities
				calculate-merge-coefficient))))

(defthm initial-state-lemma-2
	(implies (equal (len x) 1)
		 (atom (cdr x)))
:hints (("Goal" :in-theory (disable same-denominator-add 
			        remove-strict-inequalities 
				remove-weak-inequalities
				calculate-merge-coefficient))))

(DEFTHM
 INITIAL-STATE-LEMMA-3
 (IMPLIES (AND (EQUAL (CAAR X) 1)
               (EQUAL (CAADR X) 1)
               (EQUAL (LEN (CDR X)) 1)
               (EQUAL (CADAR X) (CDDAR X))
               (EQUAL (CAADAR (CDR X))
                      (CDADAR (CDR X)))
               (EQUAL (CADDAR (CDR X))
                      (CDDDAR (CDR X)))
               (CONSP (CAR X))
               (CONSP (CDAR X))
               (RATIONALP (CADAR X))
               (< 0 (CADAR X))
               (NOT (INTEGERP (CADAR X)))
               (EQUAL (DENOMINATOR (CADAR X)) 2)
               (CONSP (CDR X))
               (TRUE-COUPLED-LIST (CDR X))
               (EQUAL (SUM-OF-COUPLED-COEFFICIENT (CDR X))
                      1))
          (EQUAL (NORMALIZE-HELPER 1 (CDR X))
                 (CDR X)))
 :INSTRUCTIONS (:PROMOTE (:DV 1)
                         :EXPAND :S-PROP (:DV 1 1)
                         (:= (FIRST-COUPLED-COEFFICIENT (CDR X)))
                         :TOP (:DV 1 1)
                         (:DV 1)
                         :EXPAND (:DV 1)
                         :EXPAND :UP :UP (:DV 2)
                         :EXPAND :UP
                         (:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD))
                         (:= (CADR X))
                         :UP (:DV 2)
                         :TOP (:DV 1 2)
                         :EXPAND :TOP
                         (:USE (:INSTANCE INITIAL-STATE-LEMMA-2 (X (CDR X))))
                         :PROMOTE (:FORWARDCHAIN 1)
                         (:DV 1 2)
                         :S-PROP
                         :UP (:= (CDR X))
                         :TOP :S-PROP))

(DEFTHM
 INITIAL-STATE-LEMMA-4
 (IMPLIES (AND (EQUAL (CAAR X) 1)
               (EQUAL (CAADR X) 1)
               (EQUAL (LEN (CDR X)) 1)
               (EQUAL (CADAR X) (CDDAR X))
               (EQUAL (CAADAR (CDR X))
                      (CDADAR (CDR X)))
               (EQUAL (CADDAR (CDR X))
                      (CDDDAR (CDR X)))
               (CONSP (CAR X))
               (CONSP (CDAR X))
               (< 0 (CADAR X))
               (INTEGERP (CADAR X))
               (CONSP (CDR X))
               (TRUE-COUPLED-LIST (CDR X))
               (EQUAL (SUM-OF-COUPLED-COEFFICIENT (CDR X))
                      1))
          (EQUAL (NORMALIZE-HELPER 1 (CDR X))
                 (CDR X)))
 :INSTRUCTIONS (:PROMOTE (:DV 1)
                         :EXPAND :S-PROP (:DV 1 1)
                         (:= (FIRST-COUPLED-COEFFICIENT (CDR X)))
                         :EXPAND (:DV 1)
                         :EXPAND :UP :UP (:DV 2)
                         :EXPAND :UP
                         (:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD))
                         (:= (CADR X))
                         :UP (:DV 2)
                         :EXPAND :TOP
                         (:USE (:INSTANCE INITIAL-STATE-LEMMA-2 (X (CDR X))))
                         :PROMOTE (:FORWARDCHAIN 1)
                         (:DV 1 2)
                         :S-PROP
                         :UP (:= (CDR X))
                         :TOP :S-PROP))

(defthm initial-state-lemma-5
	(implies (initial-quantum-state x)
		(equal (normalize-helper 1 (get-coupled-state x))
		       (get-coupled-state x)))
:hints (("Goal" :in-theory (disable same-denominator-add 
			        remove-strict-inequalities 
				remove-weak-inequalities
				calculate-merge-coefficient))))

(defun none-zero (x)
	(if (atom x)
	    t
	    (and (not (equal (car x) 0))
		 (none-zero (cdr x)))))

(defthm non-zero-property-1 
	(implies (and (none-zero x)
		      (consp x))
		 (not (all-zeros x)))
:hints (("Goal" :in-theory (disable same-denominator-add 
			        remove-strict-inequalities 
				remove-weak-inequalities
				calculate-merge-coefficient))))



(defthm initial-state-lemma-6
	(implies (and (none-zero x)
		      (consp x)
		      (true-coupled-list x))
		 (equal (clean-up-zero x) x))
:hints (("Goal" :in-theory (disable same-denominator-add 
			        remove-strict-inequalities 
				remove-weak-inequalities
				calculate-merge-coefficient))))

(DEFTHM
 INITIAL-STATE-LEMMA-7
 (IMPLIES (AND (EQUAL (CAAR X) 1)
               (EQUAL (CAADR X) 1)
               (EQUAL (LEN (CDR X)) 1)
               (EQUAL (CADAR X) (CDDAR X))
               (EQUAL (CAADAR (CDR X))
                      (CDADAR (CDR X)))
               (EQUAL (CADDAR (CDR X))
                      (CDDDAR (CDR X)))
               (CONSP (CAR X))
               (CONSP (CDAR X))
               (RATIONALP (CADAR X))
               (< 0 (CADAR X))
               (NOT (INTEGERP (CADAR X)))
               (EQUAL (DENOMINATOR (CADAR X)) 2)
               (CONSP (CDR X))
               (TRUE-COUPLED-LIST (CDR X))
               (EQUAL (SUM-OF-COUPLED-COEFFICIENT (CDR X))
                      1))
          (NONE-ZERO (L-LOWERING-OPERATOR-HELPER (CDR X))))
 :INSTRUCTIONS (:PROMOTE (:DV 1)
                         :EXPAND :S-PROP (:DV 2)
                         :EXPAND (:DV 1)
                         :TOP
                         (:USE (:INSTANCE INITIAL-STATE-LEMMA-2 (X (CDR X))))
                         :PROMOTE (:FORWARDCHAIN 1)
                         (:DV 1)
                         (:DV 2)
                         (:DV 1)
                         (:= NIL)
                         :UP
                         :S-PROP :UP :TOP :EXPAND :S-PROP (:DV 2)
                         (:DV 1)
                         (:REWRITE CDR-CONS)
                         :UP :EXPAND :S-PROP :UP (:DV 1 1)
                         (:REWRITE CAR-CONS)
                         :UP
                         (:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD))
                         (:= NIL)))


(DEFTHM
 INITIAL-STATE-LEMMA-8
 (IMPLIES (AND (EQUAL (CAAR X) 1)
               (EQUAL (CAADR X) 1)
               (EQUAL (LEN (CDR X)) 1)
               (EQUAL (CADAR X) (CDDAR X))
               (EQUAL (CAADAR (CDR X))
                      (CDADAR (CDR X)))
               (EQUAL (CADDAR (CDR X))
                      (CDDDAR (CDR X)))
               (CONSP (CAR X))
               (CONSP (CDAR X))
               (< 0 (CADAR X))
               (INTEGERP (CADAR X))
               (CONSP (CDR X))
               (TRUE-COUPLED-LIST (CDR X))
               (EQUAL (SUM-OF-COUPLED-COEFFICIENT (CDR X))
                      1))
          (NONE-ZERO (L-LOWERING-OPERATOR-HELPER (CDR X))))
 :INSTRUCTIONS (:PROMOTE (:DV 1)
                         :EXPAND :S-PROP :TOP
                         (:USE (:INSTANCE INITIAL-STATE-LEMMA-2 (X (CDR X))))
                         :PROMOTE (:FORWARDCHAIN 1)
                         (:DV 1 2)
                         :EXPAND :S-PROP
                         :UP :UP :EXPAND :S-PROP (:DV 2 1)
                         (:REWRITE CDR-CONS)
                         :UP :S :UP (:DV 1 1)
                         (:REWRITE CAR-CONS)
                         :UP
                         (:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD))
                         (:= NIL)))



(defthm initial-state-lemma-9 
	(implies (and (consp x))
		 (equal (true-coupled-state x)
			(true-coupled-list x)))
:hints (("Goal" :in-theory (disable same-denominator-add 
			        remove-strict-inequalities 
				remove-weak-inequalities
				calculate-merge-coefficient))))

(defthm initial-state-lemma-10
	(implies (initial-quantum-state x)
		 (none-zero 
			(l-lowering-operator-helper (cdr x))))
:hints (("Goal" :in-theory (disable same-denominator-add 
			        remove-strict-inequalities 
				remove-weak-inequalities
				calculate-merge-coefficient
		FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))))

(DEFTHM
 INITIAL-STATE-LEMMA-11
 (IMPLIES (AND (EQUAL (CAAR X) 1)
               (EQUAL (CAADR X) 1)
               (EQUAL (LEN (CDR X)) 1)
               (EQUAL (CADAR X) (CDDAR X))
               (EQUAL (CAADAR (CDR X))
                      (CDADAR (CDR X)))
               (EQUAL (CADDAR (CDR X))
                      (CDDDAR (CDR X)))
               (CONSP (CAR X))
               (CONSP (CDAR X))
               (RATIONALP (CADAR X))
               (< 0 (CADAR X))
               (NOT (INTEGERP (CADAR X)))
               (EQUAL (DENOMINATOR (CADAR X)) 2)
               (CONSP (CDR X))
               (TRUE-COUPLED-LIST (CDR X))
               (EQUAL (SUM-OF-COUPLED-COEFFICIENT (CDR X))
                      1))
          (NONE-ZERO (S-LOWERING-OPERATOR-HELPER (CDR X))))
 :INSTRUCTIONS (:PROMOTE (:DV 1)
                         :EXPAND :S-PROP (:DV 2)
                         :TOP
                         (:USE (:INSTANCE INITIAL-STATE-LEMMA-2 (X (CDR X))))
                         :PROMOTE (:FORWARDCHAIN 1)
                         (:DV 1 2)
                         :EXPAND
                         :S-PROP :UP :UP :EXPAND :S-PROP (:DV 2)
                         (:DV 1)
                         (:REWRITE CDR-CONS)
                         :UP :EXPAND :S-PROP :UP (:DV 1 1)
                         (:REWRITE CAR-CONS)
                         :UP
                         (:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD))
                         (:= NIL)))

(DEFTHM
 INITIAL-STATE-LEMMA-12
 (IMPLIES (AND (EQUAL (CAAR X) 1)
               (EQUAL (CAADR X) 1)
               (EQUAL (LEN (CDR X)) 1)
               (EQUAL (CADAR X) (CDDAR X))
               (EQUAL (CAADAR (CDR X))
                      (CDADAR (CDR X)))
               (EQUAL (CADDAR (CDR X))
                      (CDDDAR (CDR X)))
               (CONSP (CAR X))
               (CONSP (CDAR X))
               (< 0 (CADAR X))
               (INTEGERP (CADAR X))
               (CONSP (CDR X))
               (TRUE-COUPLED-LIST (CDR X))
               (EQUAL (SUM-OF-COUPLED-COEFFICIENT (CDR X))
                      1))
          (NONE-ZERO (S-LOWERING-OPERATOR-HELPER (CDR X))))
 :INSTRUCTIONS (:PROMOTE (:DV 1)
                         :EXPAND :S-PROP (:DV 2)
                         :EXPAND :TOP
                         (:USE (:INSTANCE INITIAL-STATE-LEMMA-2 (X (CDR X))))
                         :PROMOTE (:DV 1 2)
                         (:FORWARDCHAIN 1)
                         :S-PROP
                         :UP :UP :EXPAND :S-PROP (:DV 2 1)
                         (:REWRITE CDR-CONS)
                         :UP :EXPAND :S-PROP :UP (:DV 1 1)
                         (:REWRITE CAR-CONS)
                         :UP
                         (:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD))
                         (:= NIL)))





(defthm initial-state-lemma-15
	(implies (initial-quantum-state x)
		 (none-zero 
			(s-lowering-operator-helper (cdr x))))
:hints (("Goal" :in-theory (disable same-denominator-add 
			        remove-strict-inequalities 
				remove-weak-inequalities
				calculate-merge-coefficient
		FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))))

(defthm initial-state-lemma-16
	(implies (initial-quantum-state x)
		 (consp (l-lowering-operator (cdr x))))
:hints (("Goal" :in-theory (disable same-denominator-add 
			        remove-strict-inequalities 
				remove-weak-inequalities
				calculate-merge-coefficient
		FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))))


(DEFTHM
    INITIAL-STATE-LEMMA-17
    (IMPLIES (AND (EQUAL (CAAR X) 1)
                  (EQUAL (CAADR X) 1)
                  (EQUAL (LEN (CDR X)) 1)
                  (EQUAL (CADAR X) (CDDAR X))
                  (EQUAL (CAADAR (CDR X))
                         (CDADAR (CDR X)))
                  (EQUAL (CADDAR (CDR X))
                         (CDDDAR (CDR X)))
                  (CONSP (CAR X))
                  (CONSP (CDAR X))
                  (RATIONALP (CADAR X))
                  (< 0 (CADAR X))
                  (NOT (INTEGERP (CADAR X)))
                  (EQUAL (DENOMINATOR (CADAR X)) 2)
                  (CONSP (CDR X))
                  (TRUE-COUPLED-LIST (CDR X))
                  (EQUAL (SUM-OF-COUPLED-COEFFICIENT (CDR X))
                         1))
             (EQUAL (CLEAN-UP-ZERO-LIST (L-LOWERING-OPERATOR-HELPER (CDR X)))
                    (L-LOWERING-OPERATOR-HELPER (CDR X))))
    :INSTRUCTIONS
    (:PROMOTE (:DV 1)
              :EXPAND (:DV 1)
              (:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD |(- (* c x))|
                                   FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))
              (:= T)
              :UP :S-PROP (:DV 1)
              (:DV 1 1)
              :EXPAND :S-PROP :UP (:REWRITE CAR-CONS)
              :UP (:= NIL)
              :UP :S-PROP (:DV 2 1 1)
              :EXPAND :S-PROP :UP (:REWRITE CDR-CONS)
              :EXPAND (:DV 1)
              :TOP
              (:USE (:INSTANCE INITIAL-STATE-LEMMA-2 (X (CDR X))))
              :PROMOTE (:FORWARDCHAIN 1)
              (:DV 1 1)
              :UP (:DV 2 1)
              :S-PROP
              :UP :EXPAND :S-PROP :UP (:DV 1 1)
              :EXPAND :S-PROP :UP (:REWRITE CAR-CONS)
              :UP :UP (:DV 2)
              :EXPAND :S-PROP (:DV 2)
              :EXPAND
              :S-PROP :UP
              :UP :S-PROP))


(DEFTHM
    INITIAL-STATE-LEMMA-18
    (IMPLIES (AND (EQUAL (CAAR X) 1)
                  (EQUAL (CAADR X) 1)
                  (EQUAL (LEN (CDR X)) 1)
                  (EQUAL (CADAR X) (CDDAR X))
                  (EQUAL (CAADAR (CDR X))
                         (CDADAR (CDR X)))
                  (EQUAL (CADDAR (CDR X))
                         (CDDDAR (CDR X)))
                  (CONSP (CAR X))
                  (CONSP (CDAR X))
                  (< 0 (CADAR X))
                  (INTEGERP (CADAR X))
                  (CONSP (CDR X))
                  (TRUE-COUPLED-LIST (CDR X))
                  (EQUAL (SUM-OF-COUPLED-COEFFICIENT (CDR X))
                         1))
             (EQUAL (CLEAN-UP-ZERO-LIST (L-LOWERING-OPERATOR-HELPER (CDR X)))
                    (L-LOWERING-OPERATOR-HELPER (CDR X))))
    :INSTRUCTIONS
    (:PROMOTE (:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD |(- (* c x))|
                                   FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))
              (:DV 1)
              :EXPAND (:DV 1)
              (:= T)
              :UP :S-PROP (:DV 1 1)
              (:DV 1)
              :EXPAND :S-PROP :UP (:REWRITE CAR-CONS)
              :UP (:= NIL)
              :UP :S-PROP (:DV 1 1)
              :EXPAND :S-PROP :UP (:REWRITE CAR-CONS)
              :UP (:DV 2)
              (:DV 1 1)
              :EXPAND :S-PROP :UP (:REWRITE CDR-CONS)
              :EXPAND (:= NIL)
              :UP :EXPAND :S-PROP :UP :UP (:DV 2)
              :EXPAND :S-PROP (:DV 2)
              :EXPAND (:= NIL)
              :UP
              :UP :S-PROP))



(defthm initial-state-lemma-19 
	(implies (initial-quantum-state x)
		 (equal (clean-up-zero-list
 			  (l-lowering-operator-helper
				(get-coupled-state x)))
			(l-lowering-operator-helper 
				(get-coupled-state x))))
:hints (("Goal" :in-theory (disable same-denominator-add 
			        remove-strict-inequalities 
				remove-weak-inequalities
				calculate-merge-coefficient
		FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))))

(defthm initial-state-lemma-20
	(implies (initial-quantum-state x)
		 (consp (l-lowering-operator (cdr x))))
:hints (("Goal" :in-theory (disable same-denominator-add 
			        remove-strict-inequalities 
				remove-weak-inequalities
				calculate-merge-coefficient
		FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))))

(DEFTHM
    INITIAL-STATE-LEMMA-21
    (IMPLIES (AND (EQUAL (CAAR X) 1)
                  (EQUAL (CAADR X) 1)
                  (EQUAL (LEN (CDR X)) 1)
                  (EQUAL (CADAR X) (CDDAR X))
                  (EQUAL (CAADAR (CDR X))
                         (CDADAR (CDR X)))
                  (EQUAL (CADDAR (CDR X))
                         (CDDDAR (CDR X)))
                  (CONSP (CAR X))
                  (CONSP (CDAR X))
                  (RATIONALP (CADAR X))
                  (< 0 (CADAR X))
                  (NOT (INTEGERP (CADAR X)))
                  (EQUAL (DENOMINATOR (CADAR X)) 2)
                  (CONSP (CDR X))
                  (TRUE-COUPLED-LIST (CDR X))
                  (EQUAL (SUM-OF-COUPLED-COEFFICIENT (CDR X))
                         1))
             (EQUAL (CLEAN-UP-ZERO-LIST (S-LOWERING-OPERATOR-HELPER (CDR X)))
                    (S-LOWERING-OPERATOR-HELPER (CDR X))))
    :INSTRUCTIONS
    (:PROMOTE (:DV 1)
              :EXPAND (:DV 1)
              (:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD |(- (* c x))|
                                   FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))
              (:= T)
              :UP :S-PROP (:DV 1 1)
              (:DV 1)
              :EXPAND :S-PROP :UP (:REWRITE CAR-CONS)
              :UP (:= NIL)
              :UP :S-PROP (:DV 2)
              (:DV 1 1)
              :EXPAND :S-PROP :UP (:REWRITE CDR-CONS)
              :EXPAND (:= NIL)
              :UP (:= NIL)
              :UP (:DV 1 1)
              :EXPAND :S-PROP :UP (:REWRITE CAR-CONS)
              :UP :UP (:DV 2)
              :EXPAND :S-PROP (:DV 2)
              :EXPAND (:= NIL)
              :UP
              :UP :S-PROP))


(DEFTHM
    INITIAL-STATE-LEMMA-22
    (IMPLIES (AND (EQUAL (CAAR X) 1)
                  (EQUAL (CAADR X) 1)
                  (EQUAL (LEN (CDR X)) 1)
                  (EQUAL (CADAR X) (CDDAR X))
                  (EQUAL (CAADAR (CDR X))
                         (CDADAR (CDR X)))
                  (EQUAL (CADDAR (CDR X))
                         (CDDDAR (CDR X)))
                  (CONSP (CAR X))
                  (CONSP (CDAR X))
                  (< 0 (CADAR X))
                  (INTEGERP (CADAR X))
                  (CONSP (CDR X))
                  (TRUE-COUPLED-LIST (CDR X))
                  (EQUAL (SUM-OF-COUPLED-COEFFICIENT (CDR X))
                         1))
             (EQUAL (CLEAN-UP-ZERO-LIST (S-LOWERING-OPERATOR-HELPER (CDR X)))
                    (S-LOWERING-OPERATOR-HELPER (CDR X))))
    :INSTRUCTIONS
    (:PROMOTE (:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD |(- (* c x))|
                                   FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))
              (:DV 1)
              :EXPAND (:DV 1)
              (:= T)
              :UP :S-PROP (:DV 1)
              (:= NIL)
              :UP :S-PROP (:DV 2 1)
              (:DV 1)
              :EXPAND :S-PROP :UP (:REWRITE CDR-CONS)
              :EXPAND (:= NIL)
              :UP (:= NIL)
              :UP (:DV 1 1)
              :EXPAND :S-PROP :UP (:REWRITE CAR-CONS)
              :UP :UP (:DV 2)
              :EXPAND :S-PROP (:DV 1)
              :UP (:DV 2)
              :EXPAND (:= NIL)
              :UP
              :TOP :S-PROP))




(defthm initial-state-lemma-23 
	(implies (initial-quantum-state x)
		 (equal (clean-up-zero-list
 			  (s-lowering-operator-helper
				(get-coupled-state x)))
			(s-lowering-operator-helper 
				(get-coupled-state x))))
:hints (("Goal" :in-theory (disable same-denominator-add 
			        remove-strict-inequalities 
				remove-weak-inequalities
				calculate-merge-coefficient
		FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))))

(DEFTHM
 INITIAL-STATE-LEMMA-24
 (IMPLIES
  (AND (EQUAL (CAAR X) 1)
       (EQUAL (CAADR X) 1)
       (EQUAL (LEN (CDR X)) 1)
       (EQUAL (CADAR X) (CDDAR X))
       (EQUAL (CAADAR (CDR X))
              (CDADAR (CDR X)))
       (EQUAL (CADDAR (CDR X))
              (CDDDAR (CDR X)))
       (CONSP (CAR X))
       (CONSP (CDAR X))
       (RATIONALP (CADAR X))
       (< 0 (CADAR X))
       (NOT (INTEGERP (CADAR X)))
       (EQUAL (DENOMINATOR (CADAR X)) 2)
       (CONSP (CDR X))
       (TRUE-COUPLED-LIST (CDR X))
       (EQUAL (SUM-OF-COUPLED-COEFFICIENT (CDR X))
              1)
       (EQUAL-J (CAR X) (CDR X))
       (EQUAL-MJ (CAR X) (CDR X))
       (CONSP (L-LOWERING-OPERATOR-HELPER (CDR X)))
       (CONSP (S-LOWERING-OPERATOR-HELPER (CDR X))))
  (EQUAL
   (SUM-OF-COUPLED-COEFFICIENT
       (APPEND-AND-MERGE-STATES-HELPER (L-LOWERING-OPERATOR-HELPER (CDR X))
                                       (S-LOWERING-OPERATOR-HELPER (CDR X))))
   (* 2 (CADAR X))))
 :INSTRUCTIONS
 (:PROMOTE
  (:DV 1 1)
  :EXPAND :S-PROP (:DV 2)
  (:DV 2)
  (:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD))
  (:IN-THEORY (DISABLE |(- (* c x))|
                       FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))
  :S (:DV 1)
  (:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD |(- (* c x))|
                       FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))
  (:= NIL)
  :UP :S-PROP :EXPAND :S-PROP (:DV 1)
  (:= NIL)
  :UP :S-PROP (:DV 2 2)
  (:DV 1)
  :EXPAND :S-PROP :UP (:REWRITE CDR-CONS)
  :EXPAND (:= NIL)
  :UP :EXPAND :S-PROP :UP (:DV 1 1)
  :EXPAND :S-PROP :UP (:REWRITE CAR-CONS)
  :UP :UP (:DV 1 1)
  :EXPAND :S-PROP :UP (:REWRITE CDR-CONS)
  :UP :EXPAND (:DV 1)
  (:DV 1)
  :EXPAND (:= NIL)
  :UP :S-PROP :UP (:DV 1 1 1)
  :EXPAND
  :S-PROP :UP :EXPAND (:REWRITE CAR-CONS)
  :UP :EXPAND :S-PROP (:DV 1)
  (:= NIL)
  :UP :S-PROP (:DV 2 1)
  :EXPAND :S-PROP :UP (:REWRITE CDR-CONS)
  :UP :EXPAND (:DV 1)
  (:DV 1)
  :EXPAND (:= NIL)
  :UP
  :S-PROP :UP :UP :EXPAND :S-PROP (:DV 1)
  :EXPAND (:DV 1)
  :EXPAND (:REWRITE CAR-CONS)
  :EXPAND (:DV 1)
  (:= T)
  :UP :S-PROP (:DV 1)
  (:= NIL)
  :UP :S-PROP :UP (:REWRITE CAR-CONS)
  (:= (* 2 (FIRST-COUPLED-L (CDR X))))
  :UP (:DV 2)
  :EXPAND (:DV 1 1)
  (:REWRITE CDR-CONS)
  :UP :S-PROP :UP :S-PROP (:DV 2)
  (:DV 1)
  :S :UP :S :UP
  (:= (FIRST-COUPLED-COEFFICIENT (CDR (LIST (L-LOWERING-TO-STATE (CDR X))
                                            (S-LOWERING-TO-STATE (CDR X))))))
  (:DV 1)
  (:REWRITE CDR-CONS)
  :UP :EXPAND (:DV 1)
  :EXPAND (:REWRITE CAR-CONS)
  :EXPAND (:DV 1)
  (:= T)
  :UP :S-PROP (:DV 1)
  (:= NIL)
  :UP :S-PROP :UP (:REWRITE CAR-CONS)
  (:= (* 2 (FIRST-COUPLED-S (CDR X))))
  :UP
  :TOP (:= T)))


;change it to proof checker
(defthm initial-state-lemma-25 
	(implies (initial-quantum-state x)
		 (equal (APPEND-AND-MERGE-STATES-HELPER 
			  (L-LOWERING-OPERATOR-HELPER (CDR X))
                          (S-LOWERING-OPERATOR-HELPER (CDR X)))
			(list (l-lowering-operator-helper 
				 (cdr x))
			      (s-lowering-operator-helper
				 (cdr x)))))
	:hints (("Goal" :in-theory (disable same-denominator-add 
			        remove-strict-inequalities 
				remove-weak-inequalities
				|(- (* c x))|
		FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))))




;TODO Add more lemma here if necessary


(defthm initial-state-lowering-valid 
	(implies (initial-quantum-state x)
		 (true-quantum-state (quantum-operator x)))
:hints (("Goal" :in-theory (disable same-denominator-add 
			        remove-strict-inequalities 
				remove-weak-inequalities
				|(- (* c x))|
				calculate-merge-coefficient
			REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL
			REDUCE-MULTIPLICATIVE-CONSTANT-<
		REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))))

(I-AM-HERE)
	
(skip-proofs
(defun all-lowering-valid (x)
	(if (equal x (cons '0 '0))
	    t
	    (and (true-quantum-state 
			(quantum-operator x))
		 (all-lowering-valid 
			(quantum-operator x)))))

(defthm all-quantum-lowering-valid 
	(implies (inital-quantum-state x)
		 (all-lowering-valid x))
:hints (("Goal" :in-theory (disable same-denominator-add 
			        remove-strict-inequalities 
				remove-weak-inequalities
				|(- (* c x))|
				calculate-merge-coefficient
			REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL
			REDUCE-MULTIPLICATIVE-CONSTANT-<
		REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))))


