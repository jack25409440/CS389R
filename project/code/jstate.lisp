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

#||
(local (in-theory (disable |(+ x (if a b c))| 
			   |(- (if a b c))|
			   |(< (if a b c) x)| 
			   |(< x (if a b c))|)))
||#


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


(DEFTHM J-LOWERING-LEMMA6
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



;verify the j-lowering-operator is valid
(defthm j-lowering-valid 
	(implies (true-jstate x)
	         (true-jstate (j-lowering-operator x)))
    :hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities))))

(ld "coupled-state.lisp")
