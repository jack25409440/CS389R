(defthm normalize-lemma1 
	(implies (and (consp y)
		      (rationalp a))
		 (consp (normalize-helper a y))))

(defthm normalize-lemma2 
	(implies (and (true-coupled-list y)
		      (rationalp a)
		      (< 0 a))
		 (all-non-negative-coefficient 
			(normalize-helper a y)))
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


#||
(defun all-state-pairs-same (x y)
	(if (atom x)
	    (if (atom y)
		t
		nil)
	    (and (equal (first-coupled-l-state x)
			(first-coupled-l-state y))
		 (equal (first-coupled-s-state x)
			(first-coupled-s-state y))
		(all-state-pairs-same (cdr x) (cdr y)))))


(defthm normalize-lemma3 
	(implies (and (rationalp a)
		      (< 0 a)
		      (consp x)
		      (true-coupled-list x))
		 (all-state-pairs-same x 
			   (normalize-helper a x)))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities))))

||#

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


#||
(defun normalize-helper (a y)
	(if (atom y)
	    nil
	    (cons (cons (/ (first-coupled-coefficient y) a) 
		        (first-coupled-state y))
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


(defthm normalize-coupled 
	(implies (and (consp x)
		      (true-coupled-list x)
		      (rationalp a)
		      (< 0 a))
		 (true-coupled-list (normalize-helper a x)))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities)
		:induct (normalize-helper a x))))

				default-less-than-1
				default-less-than-2
				default-plus-1
				default-rational-denominator
				|(+ x (if a b c))|
				|(- (if a b c))|
				|(< (if a b c) x)|
				|(< x (if a b c))|
				DEFAULT-MINUS
				DEFAULT-PLUS-2
			FUNCTIONAL-SELF-INVERSION-OF-MINUS
			INTEGERP==>DENOMINATOR-=-1
			EQUAL-DENOMINATOR-1
			/-PRESERVES-NEGATIVE))))

||#
