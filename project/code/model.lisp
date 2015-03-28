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

;definitions for the j-state

(defun rational-pair (x)
	(if (atom x)
	    nil
	    (and (rationalp (car x))
		 (rationalp (cdr x))
		 (>= (car x) (abs (cdr x))))))

(defun good-quantumj (x)
	(if (atom x)
	    nil
	    (>= (car x) (abs (cdr x)))))

(defun true-jstate (a)
	(if (atom a)
	    (if (= a 0)
		t
		nil)
	    (and (rationalp (car a))
	         (rational-pair (cdr a)))))

(defun j-state (a j m_j)
      (declare (xargs :guard (and (rationalp a)
				  (rationalp j)
				  (rationalp m_j))))
      (cons a (cons j m_j)))


(defun j-lowering (x)
	(if (< (car (cdr x)) (abs (- (cdr (cdr x)) 1)))
	    0
	    (cons (* (car x)
		     (- (*  (car (cdr x)) (+ (car (cdr x)) 1))
		        (* (cdr (cdr x)) (- (cdr (cdr x)) 1))))
		  (cons (car (cdr x)) (- (cdr (cdr x)) 1)))))

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

(defun clean-up-zero (x)
	(if (atom x)
	    nil
	    (if (= (car x) 0)
		(clean-up-zero (cdr x))
	        (cons (car x)
		      (clean-up-zero (cdr x))))))

;TODO: verify l-lowering-valid and s-lowering-valid

;TODO: veriy the sum of coefficients of B,C,... equals to A

