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

;-------------model-------------------------------------

(defun j-coefficient (x) 
	(car x))

(defun quantum-j (x)
	(car (cdr x)))

(defun quantum-mj (x)
	(cdr (cdr x)))

(defun lower-or-lowest-jstate (x)
	 (or (>= (- (quantum-mj x)) (quantum-j x))
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


;verify the j-lowering-operator is valid
(defthm j-lowering-valid 
	(implies (true-jstate x)
	         (true-jstate (j-lowering-operator x)))
    :hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities))))

;--------------Coupled state-------------------------

;--------------Coupled model------------------------

(defun first-coupled-state (x)
	(car x))

(defun first-coupled-coefficient (x)
	(car (first-coupled-state x)))

(defun first-coupled-l-state (x)
	(car (cdr (first-coupled-state x))))

(defun first-coupled-s-state (x)
	(cdr (cdr (first-coupled-state x))))

(defun first-coupled-l (x)
	(car (first-coupled-l-state x)))

(defun first-coupled-ml (x)
	(cdr (first-coupled-l-state x)))

(defun first-coupled-s (x)
	(car (first-coupled-s-state x)))

(defun first-coupled-ms (x)
	(cdr (first-coupled-s-state x)))

;------verify that a state is real coupled state-------

(defun true-coupled-list (x)
	(if (atom x)
	    t
	    (and (rationalp (first-coupled-coefficient x))
		 (<= 0 (first-coupled-coefficient x))
	         (rational-pair (first-coupled-l-state x))
		 (rational-pair (first-coupled-s-state x))
		 (true-coupled-list (cdr x)))))


(defun true-coupled-state (x)
	(if (atom x)
	    (equal x 0)
	    (true-coupled-list x)))
	    
;clean up 0s in the list

(defun all-zeros (x)
	(if (atom x)
	    t
	    (and (equal (car x) 0)
		 (all-zeros (cdr x)))))

(defun clean-up-zero-list (x) 
	(if (atom x)
	    0
            (if (equal (car x) 0)
		(clean-up-zero-list (cdr x))
	        (cons (car x)
		      (clean-up-zero-list (cdr x))))))

(defun clean-up-zero (x)
	(if (atom x)
	    0
	    (if (all-zeros x)
		0
	        (clean-up-zero-list x))))

(defthm clean-up-zero-valid 
	(implies (true-coupled-state x)
		 (true-coupled-state (clean-up-zero x)))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities))))

;-------l-lowering-operator---------------------------

(defun lower-or-lowest-l-state (x)
	(or (equal (first-coupled-coefficient x) 0)
	    (>= (- (first-coupled-ml x)) (first-coupled-l x))))


(defun l-lowering-to-state (x)
	(if (atom (first-coupled-state x))
	    0 
	    (if (lower-or-lowest-l-state x)
		0
		(cons (* (first-coupled-coefficient x)
			 (+ (expt (first-coupled-l x) 2)
			    (- (expt (first-coupled-ml x) 2))
			    (first-coupled-l x)
			    (first-coupled-ml x)))
		      (cons (cons (first-coupled-l x)
				  (- (first-coupled-ml x) 1)) 
			    (first-coupled-s-state x)))))) 


(defun l-lowering-operator-helper (x)
	(if (atom x)
	    nil
	    (cons (l-lowering-to-state x) 
		  (l-lowering-operator-helper (cdr x)))))

(defun l-lowering-operator (x)
	(if (atom x)
	    0
	    (clean-up-zero (l-lowering-operator-helper x))))

(DEFTHM L-LOWERING-LEMMA1
        (IMPLIES (AND (RATIONALP X)
                      (RATIONALP Y)
                      (< 0 X)
                      (<= 0 Y)
                      (<= Y X)
                      (INTEGERP (+ X (- Y)))
                      (EQUAL (DENOMINATOR X) 2)
                      (EQUAL (DENOMINATOR Y) 2))
                 (INTEGERP (+ X Y)))
        :INSTRUCTIONS (:PROMOTE (:REWRITE REDUCE-INTEGERP-+ ((Z (+ X (- Y))))
                                          T)
                                (:DV 1)
                                (:REWRITE |(+ (+ x y) z)|)
                                :TOP
                                (:USE (:INSTANCE OPPOSITE-ELIMINATE (A X)
                                                 (B Y)))
                                :PROMOTE (:FORWARDCHAIN 1)
                                (:DV 1)
                                (:= (* X 2))
                                :TOP (:REWRITE INTEGER-TIMES-NUMERATOR)))


;Remove the commend when finish
#||
(defthm l-lowering-valid 
	(implies (true-coupled-state x)
		 (true-coupled-state (l-lowering-operator x)))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities))))
||#

;-------s-lowering-operator---------------------------

(defun lower-or-lowest-s-state (x)
	(or (equal (first-coupled-coefficient x) 0)
	    (>= (- (first-coupled-ms x)) (first-coupled-s x))))


(defun s-lowering-to-state (x)
	(if (atom (first-coupled-state x))
	    0 
	    (if (lower-or-lowest-s-state x)
		0
		(cons (* (first-coupled-coefficient x)
			 (+ (expt (first-coupled-s x) 2)
			    (- (expt (first-coupled-ms x) 2))
			    (first-coupled-s x)
			    (first-coupled-ms x)))
		      (cons (first-coupled-l-state x) 
			    (cons (first-coupled-s x) 
				  (- (first-coupled-ms x) 1))))))) 


(defun s-lowering-operator-helper (x)
	(if (atom x)
	    nil
	    (cons (s-lowering-to-state x) 
		  (s-lowering-operator-helper (cdr x)))))

(defun s-lowering-operator (x)
	(if (atom x)
	    0
	    (clean-up-zero (s-lowering-operator-helper x))))

(defthm s-lowering-valid 
	(implies (true-coupled-state x)
		 (true-coupled-state (s-lowering-operator x)))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities))))


