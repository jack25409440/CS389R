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

(ld "initial-quantum-state.lisp")



