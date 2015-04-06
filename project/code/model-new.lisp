#||

			Spring 2015 CS 389R Model
			     Xiaohui Chen
		      Department of Computer Science
		    The University of Texas at Austin

For each state, the model is with the form
((A . (j . m_j)) . ((B . ((l . m_l) .  (s . m_s)))
		    (C . ((l . m_l) .  (s . m_s)))
		    ...))
||#


(local (include-book "arithmetic/inequalities" :dir :system))

(local (include-book "arithmetic/equalities" :dir :system))

;------------basic Mathematical theorems------------------

(defthm opposite-eliminate 
	(implies (and (rationalp a)
	              (rationalp b))
	 	 (equal (+ a (- b) b a)
			(* a 2))))

(defthm integer-times-numerator 
	(implies (and (rationalp x)
		      (equal (denominator x) n))
		 (integerp (* x n)))) 		    


(defthm positive-half-integer-add 
	(implies (and (rationalp x)
		      (< 0 x)
		      (rationalp y)
		      (<= 0 y)
		      (equal (denominator x) 2)
		      (equal (denominator y) 2))
		  (< 0 (+ x y))))

(defthm integer-sum 
	(implies (and (rationalp x)
		      (rationalp y)
		      (integerp (+ x y))
		      (< 0 (+ x y)))
		 (<= 1 (+ x y))))

(defthm opposite-rationals
	(implies (and (rationalp x)
		      (rationalp y)
		      (equal x (- y)))
		 (= (+ x y) 0)))
;-------------The j-state-------------------------------

(defun j-coefficient (x) 
	(car x))

(defun quantum-j (x)
	(car (cdr x)))

(defun quantum-mj (x)
	(cdr (cdr x)))

(defun lower-or-lowest-jstate (x)
	 (or (>= (abs (quantum-mj x)) (quantum-j x))
	     (equal (j-coefficient x) 0)))

(defun half-or-full-integer (x)
	(xor (equal (denominator x) 1)
	     (equal (denominator x) 2)))

(defun half-full-match (x y)
	(and (iff (equal (denominator x) 1)
		  (equal (denominator y) 1))
	     (iff (equal (denominator x) 2)
		  (equal (denominator y) 2))))

(defun rational-pair (x)
	(if (atom x) 
	    nil
	    (and (rationalp (car x))
		 (< 0 (car x))
		 (rationalp (cdr x))
		 (natp (- (car x) (abs (cdr x))))
		 (half-or-full-integer (car x))
		 (half-or-full-integer (cdr x))
		 (half-full-match (car x) (cdr x))
		 (<= (abs (cdr x)) (car x)))))

(defun true-jstate (a)
	(if (atom a)
	    (equal a 0)
	    (and (rationalp (car a))
		 (<= 0 (car a))
	         (rational-pair (cdr a)))))

(defun j-lowering-operator (x) 
	(if (atom x)
	    0
	    (if (lower-or-lowest-jstate x)
		0
	  	(cons (* (j-coefficient x)
			 (+ (expt (quantum-j x) 2) 
		    	    (quantum-j x)
		            (- (expt (quantum-mj x) 2))
		            (quantum-mj x)))
	              (cons (quantum-j x)
		            (- (quantum-mj x) 1))))))

;---------------Theroems for j-state-----------------------

(defthm lowest-j-state-property 
	(implies (and (true-jstate x)
		      (equal (- (quantum-mj x)) (quantum-j x)))
		 (equal (+ (quantum-mj x) (quantum-j x)) 0)))

(defthm j-lowering-lemma1 
	(implies (and (rationalp a)
		      (rationalp b)
		      (< b 0)
		      (< 0 a)
		      (<= (- b) a))
		 (<= 0 (+ a b))))

(local (include-book "arithmetic-5/top" :dir :system))

(DEFTHM J-LOWERING-LEMMA2
        (IMPLIES (AND (RATIONALP A)
                      (RATIONALP B)
                      (< B 0)
                      (< 0 A)
                      (<= (- B) A))
                 (<= (EXPT B 2) (EXPT A 2)))
        :INSTRUCTIONS (:PROMOTE (:= (<= (* (- B) (- B)) (* A A)))
                                (:REWRITE NOT)
                                (:DV 1)
                                (:REWRITE *-PRESERVES->=-FOR-NONNEGATIVES)))

(DEFTHM J-LOWERING-LEMMA3
        (IMPLIES (AND (RATIONALP A)
                      (RATIONALP B)
                      (<= 0 B)
                      (< 0 A)
                      (<= B A))
                 (<= (EXPT B 2) (EXPT A 2)))
        :INSTRUCTIONS (:PROMOTE :DEMOTE :PROMOTE (:DEMOTE 3)
                                (:DV 1)
                                (:= (OR (< 0 B) (= 0 B)))
                                :TOP :SPLIT (:= (<= (* B B) (* A A)))
                                (:REWRITE NOT)
                                (:DV 1)
                                (:REWRITE *-PRESERVES->=-FOR-NONNEGATIVES)
                                :S))


(defthm j-lowering-lemma4
	(implies (and (rationalp a)
		      (rationalp b)
		      (rationalp c)
		      (rationalp d)
		      (<= (expt b 2) (expt a 2))
		      (<= 0 (+ c d)))
		 (<= (expt b 2) 
		     (+ c d (expt a 2)))))


(defthm j-lowering-lemma5 
	(implies (and (true-jstate x)
		      (consp x)
		      (not (equal (quantum-j x) (quantum-mj x))))
	     (> (quantum-j x) (quantum-mj x))))	  
		      


(defthm same-denominator-add 
	(implies (and (rationalp x)
		      (rationalp y)
		      (equal (denominator x) (denominator y)))
		 (equal (+ x y)
		        (/ (+ (numerator x) (numerator y))
			   (denominator x)))))

(DEFTHM
     J-LOWERING-LEMMA6
     (IMPLIES (AND (CONSP X)
                   (RATIONALP (CAR X))
                   (<= 0 (CAR X))
                   (CONSP (CDR X))
                   (RATIONALP (CADR X))
                   (< 0 (CADR X))
                   (RATIONALP (CDDR X))
                   (<= 0 (CDDR X))
                   (INTEGERP (+ (CADR X) (- (CDDR X))))
                   (<= (CDDR X) (CADR X))
                   (NOT (INTEGERP (CADR X)))
                   (EQUAL (DENOMINATOR (CADR X)) 2)
                   (NOT (INTEGERP (CDDR X)))
                   (EQUAL (DENOMINATOR (CDDR X)) 2)
                   (NOT (EQUAL (CAR X) 0))
                   (< (CDDR X) 1))
              (INTEGERP (+ (CADR X) (CDDR X))))
     :INSTRUCTIONS (:PROMOTE (:REWRITE REDUCE-INTEGERP-+
                                       ((Z (+ (CADR X) (- (CDDR X)))))
                                       T)
                             (:DV 1)
                             (:REWRITE |(+ (+ x y) z)|)
                             :UP (:DV 1)
                             :TOP
                             (:USE (:INSTANCE OPPOSITE-ELIMINATE (A (CADR X))
                                              (B (CDDR X))))
                             :PROMOTE (:FORWARDCHAIN 1)
                             (:DV 1)
                             (:= (* (CADR X) 2))
                             :TOP (:REWRITE INTEGER-TIMES-NUMERATOR)))



(defthm j-lowering-valid 
	(implies (true-jstate x)
	         (true-jstate (j-lowering-operator x)))
    :hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities))))


