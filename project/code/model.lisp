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



(defthm square-larger-positive
        (implies (and (<= a b)
		      (< 0 b)
		      (< 0 a)
		      (rationalp a)
		      (rationalp b))
		 (<= (* a a) (* b b)))
  :hints (("Goal" :use *-preserves->=-for-nonnegatives)))

(DEFTHM SQUARE-LARGER-NEGATIVE
        (IMPLIES (AND (<= (- A) B)
                      (< 0 B)
                      (< A 0)
                      (RATIONALP A)
                      (RATIONALP B))
                 (<= (* A A) (* B B)))
        :INSTRUCTIONS (:PROMOTE (:REWRITE NOT)
                                (:DV 1)
                                (:DV 2)
                                (:= (* (- A) (- A)))
                                :UP (:REWRITE SQUARE-LARGER-POSITIVE)))



(defthm square-larger 
	(implies (and (<= (abs a) b)
		      (< 0 b)
		      (rationalp a)
		      (rationalp b))
		 (<= (* a a) (* b b))))

;(local (include-book "arithmetic-5/top" :dir :system))

;definitions for the j-state

(defun rational-pair (x)
	(if (atom x) nil
	    (and (rationalp (car x))
		 (< 0 (car x))
		 (rationalp (cdr x))
		 (>= (car x) (cdr x))
		 (>= (car x) (- (cdr x))))))

(defun true-jstate (a)
	(if (atom a)
	    (equal a 0)
	    (and (rationalp (car a))
		 (< 0 (car a))
	         (rational-pair (cdr a)))))


(DEFTHM J-LOWERING-LEMMA1
        (IMPLIES (AND (CONSP X)
                      (RATIONALP (CAR X))
                      (< 0 (CAR X))
                      (CONSP (CDR X))
                      (RATIONALP (CADR X))
                      (< 0 (CADR X))
                      (ACL2-NUMBERP (CDDR X))
                      (<= (CDDR X) (CADR X))
                      (RATIONALP (CDDR X))
                      (< (- (CDDR X)) (CADR X)))
                 (< 0 (+ (CADR X) (CDDR X))))
        :INSTRUCTIONS (:PROMOTE :PROVE))


(DEFTHM J-LOWERING-LEMMA2
        (IMPLIES (AND (CONSP X)
                      (RATIONALP (CAR X))
                      (< 0 (CAR X))
                      (CONSP (CDR X))
                      (RATIONALP (CADR X))
                      (< 0 (CADR X))
                      (<= (CDDR X) (CADR X))
                      (RATIONALP (CDDR X))
                      (<= (- (CDDR X)) (CADR X)))
                 (<= (* (CDDR X) (CDDR X))
                     (* (CADR X) (CADR X))))
        :INSTRUCTIONS (:SPLIT (:REWRITE NOT)
                              (:DV 1)
                              (:REWRITE SQUARE-LARGER)
                              :PROVE))



(defun j-lowering (x)
	(if (<= (car (cdr x)) (- (cdr (cdr x))))
	    0
	    (cons (* (car x)
		     (- (*  (car (cdr x)) (+ (car (cdr x)) 1))
		        (* (cdr (cdr x)) (- (cdr (cdr x)) 1))))
		  (cons (car (cdr x)) (- (cdr (cdr x)) 1)))))

(defthm j-lowering-coefficient 
	(implies (true-jstate x)
		 (<= (* (cddr x) (cddr x)) 
		     (* (cadr x) (cadr x)))))

(defthm inequality-property 
	(implies (and (rationalp a)
		      (rationalp b)
		      (rationalp c)
		      (rationalp d)
		      (< 0 (+ c d))
		      (<= b a))
		 (< b (+ c d a))))

(local (include-book "arithmetic-5/top" :dir :system))

(DEFTHM J-LOWERING-LEMMA3
        (IMPLIES (AND (CONSP X)
                      (RATIONALP (CAR X))
                      (< 0 (CAR X))
                      (CONSP (CDR X))
                      (RATIONALP (CADR X))
                      (< 0 (CADR X))
                      (RATIONALP (CDDR X))
                      (<= (CDDR X) (CADR X))
                      (< (- (CDDR X)) (CADR X)))
                 (< (EXPT (CDDR X) 2)
                    (+ (CADR X)
                       (CDDR X)
                       (EXPT (CADR X) 2))))
        :INSTRUCTIONS (:PROMOTE (:REWRITE INEQUALITY-PROPERTY)
                                (:REWRITE J-LOWERING-LEMMA1)
                                (:= (<= (* (CDDR X) (CDDR X))
                                        (* (CADR X) (CADR X))))
                                (:REWRITE NOT)
                                (:DV 1)
                                (:REWRITE J-LOWERING-LEMMA2)
                                :PROVE))



(defthm j-lowering-valid
	(implies (true-jstate x)
		 (true-jstate (j-lowering x))))
		   
;definitions for the coupled states

(defun good-quantum-coupled-list (x)
	(if (atom x)
	    t
	    (and (rationalp (car (car x)))
		 (rational-pair (car (cdr (car x))))
	         (rational-pair (cdr (cdr (car x))))
	         (good-quantum-coupled-list (cdr x)))))
	

(defun good-quantumcoupled (x)
	(if (atom x)
	    (= x 0)
	    (good-quantum-coupled-list x)))


;l-lowering operator

(defun l-lowering-helper (x)
	(if (< (car (car (cdr x)))
	       (abs (- (cdr (car (cdr x))) 1)))
	    0
	    (cons (* (car x)
		     (- (* (car (car (cdr x))) 
			   (+ (car (car (cdr x))) 1))
			(* (cdr (car (cdr x)))
			   (- (cdr (car (cdr x))) 1))))
		   (cons (cons (car (car (cdr x)))
			       (- (cdr (car (cdr x))) 1))
			 (cdr (cdr x)))))) 

(defun l-lowering (x)
	(if (atom x)
	    nil
	    (cons (l-lowering-helper (car x))
		  (l-lowering (cdr x)))))

;s-lowering operator

(defun s-lowering-helper (x)
	(if (< (car (cdr (cdr x)))
	       (abs (- (cdr (cdr (cdr x))) 1)))
	    0
	    (cons (* (car x)
		     (- (* (car (cdr (cdr x))) 
			   (+ (car (cdr (cdr x))) 1))
			(* (cdr (cdr (cdr x)))
			   (- (cdr (cdr (cdr x))) 1))))
		   (cons (car (cdr x))
			 (cons (car (cdr (cdr x)))
			       (- (cdr (cdr (cdr x))) 1)))))) 

(defun s-lowering (x)
	(if (atom x)
	    nil
	    (cons (s-lowering-helper (car x))
		  (s-lowering (cdr x)))))

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

 
(defthm clean-up-zero-s-lowering-valid
	(implies (good-quantumcoupled x)
		 (good-quantumcoupled (clean-up-zero 
					   (s-lowering x)))))

(defthm clean-up-zero-l-lowering-valid 
	(implies (good-quantumcoupled x)
		 (good-quantumcoupled (clean-up-zero 
					   (l-lowering x)))))

;merge the same state

(defun coupled-coefficient (x)
	(car x))

(defun coupled-state (x)
	(cdr x))

(defun add-same-state (x y)
	(if (atom y)
	    x
	    (if (equal (coupled-state x)
		       (coupled-state (car y)))
	        (add-same-state (cons (+ (coupled-coefficient x)
					 (coupled-coefficient 
							(car y)))
			      	      (coupled-state x))
			 	(cdr y))
		(add-same-state x (cdr y)))))

(defun delete-same-state (x y)
	(if (atom y)
	    y
	    (if (equal (coupled-state x)
		       (coupled-state (car y)))
		(delete-same-state x (cdr y))
		(cons (car y) (delete-same-state x (cdr y))))))

(defun merge-same (x)
	(if (atom x)
	    x
	    (cons (add-same-state (car x) (cdr x))
	 	  (merge-same 
			(delete-same-state (car x) (cdr x))))))
	    
;verify l-lowering-valid and s-lowering-valid

(defthm l-lowering-valid 
	(implies (good-quantumcoupled x)
	         (good-quantumcoupled (clean-up-zero 
					(l-lowering x)))))

(defthm s-lowering-valid 
	(implies (good-quantumcoupled x)
		 (good-quantumcoupled (clean-up-zero 
					 (s-lowering x)))))

;Veriy the sum of coefficients of B,C,... equals to A

(defun state-append (x y)
	(if (atom x)
	    y
	    (if (atom y)
		x
	        (cons (car x) (state-append (cdr x) y)))))

(defthm good-quantumcoupled-append 
	(implies (and (good-quantumcoupled x)
		      (good-quantumcoupled y))
		 (good-quantumcoupled (state-append x y))))

(defun sum-of-coefficients (x)
    (if (atom x)
	0
	(+ (abs (car (car x)))
	   (sum-of-coefficients (cdr x)))))

(defun get-jcoefficient (x)
	(if (atom x)
	    0
	    (car x)))

(defun true-state (x)
    (if (atom x)
	nil
	(and (true-jstate (car x))
	     (good-quantumcoupled (cdr x))
	     (iff (consp (car x)) (consp (cdr x)))
	     (iff (equal (car x) 0) (equal (cdr x) 0))
  	     (= (sum-of-coefficients (cdr x))
		(get-jcoefficient (car x))))))

;before applying the operators, we have to normalize the states
(defun j-coefficient (x)
	 (car (car x)))

(defun j-state (x)
	(cdr (car x)))

(defun normalize-j (a)
	(if (atom a)
	    0
	    (cons (/ (car a) (car a)) (cdr a))))

(defun divide-coefficient (x y)
	(cons (/ (car y) x)
	      (cdr y)))

(defun normalize-coupled-helper (x y)
	(if (atom y)
	    nil
	    (cons (divide-coefficient x (car y))
		  (normalize-coupled-helper x (cdr y)))))

(defun normalize-coupled (x y)
	(if (atom y)
	    0
	    (normalize-coupled-helper x y)))

(defun normalize-state (x)
	(if (equal (j-coefficient x) 0)
	    x
	    (cons (normalize-j (car x))
	          (normalize-coupled (j-coefficient x) (cdr x)))))

(defthm normalize-coupled-valid-trivial
	(implies (and (atom x)
		      (rationalp a)
		      (good-quantumcoupled x))
		 (atom (normalize-coupled a x))))

(defthm normalize-coupled-valid-non-trival
	(implies (and (good-quantumcoupled x)
		      (rationalp a)
		      (consp x))
		 (good-quantumcoupled 
			(normalize-coupled-helper a x))))

(defthm normalize-coupled-valid 
	(implies (and (good-quantumcoupled x)
		      (rationalp a))
		 (good-quantumcoupled 
		      (normalize-coupled a x))))

(defthm normalize-j-valid 
	(implies (true-jstate x)
		 (true-jstate (normalize-j x))))

(defthm true-state-trival
	(implies (true-state x)
		 (xor (and (equal (car x) 0)
			  (equal (cdr x) 0))
		     (and (consp (car x))
			  (consp (cdr x))))))

(defthm normalize-state-car
	(implies (true-state x)
		 (true-jstate (car (normalize-state x)))))

(defthm normalize-state-cdr 
	(implies (true-state x)
		 (good-quantumcoupled (cdr (normalize-state x)))))

#||
(defthm sum-of-coefficient-div-multiply
	(implies (and (good-quantumcoupled x)
		      (rationalp a)
		      (rationalp b)
		      (> a 0)
		      (> b 0)
		      (equal (sum-of-coefficients x) b))
		 (equal (/ b a) (sum-of-coefficients
				   (normalize-coupled a x)))))
		      
(defthm sum-of-coefficient-valid 
	(implies  (true-state x)
		(= (sum-of-coefficients (cdr (normalize-state x)))
		   (get-jcoefficient (car (normalize-state x))))))


(DEFTHM NORMALIZE-STATE-VALID-LEMMA1
        (IMPLIES (AND (CONSP X)
                      (CONSP (CAR X))
                      (RATIONALP (CAAR X))
                      (CONSP (CDAR X))
                      (RATIONALP (CADAR X))
                      (RATIONALP (CDDAR X))
                      (< (CDDAR X) 0)
                      (<= (- (CDDAR X)) (CADAR X))
                      (GOOD-QUANTUM-COUPLED-LIST (CDR X))
                      (CONSP (CDR X))
                      (EQUAL (SUM-OF-COEFFICIENTS (CDR X))
                             (CAAR X)))
                 (CONSP (NORMALIZE-COUPLED-HELPER (CAAR X)
                                                  (CDR X))))
        :INSTRUCTIONS (:PROMOTE (:DV 1)
                                :EXPAND :S-PROP
                                :TOP :S))

		      

||#

(defthm sum-multiply-div 
	(implies (and (good-quantumcoupled x)
		      (rationalp a)
		      (< 0 a))
		 (equal (sum-of-coefficients 
				(normalize-coupled a x))
			(/ (sum-of-coefficients x) a)))) 


(defthm normalize-state-valid
	(implies (true-state x)
		 (true-state (normalize-state x))))


;applying the lowering operators
(defun state-lowering-helper (x)
	(if (atom x)
	    0
	    (cons (j-lowering (car x))
		  (merge-same (state-append (clean-up-zero 
				   (l-lowering (cdr x)))
			         (clean-up-zero
				   (s-lowering (cdr x))))))))

(defun state-lowering (x)
	(state-lowering-helper (normalize-state x)))


#||
(defthm sum-equal 
	(implies (true-state x)
		 (true-state (state-lowering x)))) 
||#

;(state-lowering '((1 . (3/2 . 3/2)) . ((1 . ((1 . 1) . (1/2 . 1/2))))))

;(state-lowering (state-lowering '((1 . (3/2 . 3/2)) . ((1 . ((1 . 1) . (1/2 . 1/2)))))))

