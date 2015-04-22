;--------------Coupled state-------------------------

;--------------Coupled model------------------------

(defun first-coupled-state (x)
	(car x))

(defun first-coupled-state-pair (x)
	(cdr (car x)))

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

(defun true-coupled-element (x)
	(and (rationalp (car x))
	     (<= 0 (car x))
	     (rational-pair (car (cdr x)))
	     (rational-pair (cdr (cdr x)))))

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
	    x
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

(defthm clean-up-zero-lemma-1
	(implies (and (consp x)
		      ;(true-coupled-list x)
		      (not (all-zeros x)))
		 (consp (clean-up-zero-list x)))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities))))


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


;Remove the comment when finish
(defthm l-lowering-valid 
	(implies (true-coupled-state x)
		 (true-coupled-state (l-lowering-operator x)))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities))))

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

;Remove the comment when finish

(defthm s-lowering-valid 
	(implies (true-coupled-state x)
		 (true-coupled-state (s-lowering-operator x)))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities))))

;---------Factorial---------------------------

(defun factorial (n)
	(if (zp n)
	    1
	    (* n (factorial (- n 1)))))

(defthm factorial-property 
	(implies (rationalp n)
		 (rationalp (factorial n))))

;---------Calculate merge coefficient---------

(defun calculate-merge-coefficient-factor (l ml s ms)
	(+ (expt (+ l s) 2)
	   (- (expt (+ ml ms) 2))
	   (+ l s)
	   (- (+ ml ms))))

(defun calculate-merge-coefficient-helper (l ml s ms)
	(/ (* (factorial (* 2 l)) (factorial (* 2 s)) 
	      (factorial (+ l s ml ms)) 
	      (factorial (+ l s (- ml) (- ms))))
	   (* (factorial (* 2 (+ l s)))
	      (factorial (+ l ml))
	      (factorial (- l ml))
	      (factorial (+ s ms))
	      (factorial (- s ms)))))

(defun calculate-merge-coefficient (l ml s ms)
	(* (calculate-merge-coefficient-factor l ml s ms)
	   (calculate-merge-coefficient-helper l ml s ms)))

#||
(defthm denominator-add-integer 
	(implies (and (rationalp ml)
		      (rationalp ms)
		      (equal (denominator ml) 2)
		      (equal (denominator ms) 2))
		 (integerp (+ ml ms)))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities))))


(defthm rational-pair-property 
	(implies (and (rational-pair (cons l ml))
		      (rational-pair (cons s ms)))
		 (rational-pair (cons (+ l s) (+ ml ms))))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities
				|(- (+ x y))|
				|(- (* c x))|
				PREFER-POSITIVE-ADDENDS-EQUAL))))

||#


(defthm calculate-merge-lemma1
	(implies (and (rational-pair (cons l ml))
		      (rational-pair (cons s ms)))
		 (rationalp (calculate-merge-coefficient-factor 
				l ml s ms)))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities
				|(- (+ x y))|
				|(- (* c x))|
				PREFER-POSITIVE-ADDENDS-EQUAL))))

(DEFTHM CALCULATE-MERGE-LEMMA2
        (IMPLIES (AND (RATIONALP L)
                      (< 0 L)
                      (RATIONALP ML)
                      (< ML 0)
                      (<= (- ML) L)
                      (RATIONALP S)
                      (< 0 S)
                      (RATIONALP MS)
                      (< MS 0)
                      (<= (- MS) S))
                 (<= (+ ML MS) (+ L S)))
        :INSTRUCTIONS (:PROMOTE (:REWRITE NOT)
                                (:DV 1)
                                (:REWRITE REMOVE-WEAK-INEQUALITIES)))


(DEFTHM CALCULATE-MERGE-LEMMA3
        (IMPLIES (AND (RATIONALP L)
                      (< 0 L)
                      (RATIONALP ML)
                      (< ML 0)
                      (<= (- ML) L)
                      (RATIONALP S)
                      (< 0 S)
                      (RATIONALP MS)
                      (< MS 0)
                      (<= (- MS) S))
                 (<= (* 2 ML MS) (* 2 L S)))
        :INSTRUCTIONS (:PROMOTE (:REWRITE NOT)
                                (:DV 1)
                                (:DV 2)
                                (:= (* 2 (- ML) (- MS)))
                                :UP (:= (< (* L S) (* (- ML) (- MS))))
                                (:REWRITE *-PRESERVES->=-FOR-NONNEGATIVES)))

(DEFTHM
     CALCULATE-MERGE-LEMMA4
     (IMPLIES (AND (RATIONALP L)
                   (< 0 L)
                   (RATIONALP ML)
                   (< ML 0)
                   (<= (- ML) L)
                   (RATIONALP S)
                   (< 0 S)
                   (RATIONALP MS)
                   (< MS 0)
                   (<= (- MS) S))
              (<= (EXPT ML 2) (EXPT L 2)))
     :INSTRUCTIONS (:PROMOTE (:REWRITE NOT)
                             (:DV 1)
                             (:= (< (* L L) (* ML ML)))
                             (:DV 2)
                             (:= (* (- ML) (- ML)))
                             :UP (:REWRITE *-PRESERVES->=-FOR-NONNEGATIVES)))

(DEFTHM
     CALCULATE-MERGE-LEMMA5
     (IMPLIES (AND (RATIONALP L)
                   (< 0 L)
                   (RATIONALP ML)
                   (< ML 0)
                   (<= (- ML) L)
                   (RATIONALP S)
                   (< 0 S)
                   (RATIONALP MS)
                   (< MS 0)
                   (<= (- MS) S))
              (<= (EXPT MS 2) (EXPT S 2)))
     :INSTRUCTIONS (:PROMOTE (:REWRITE NOT)
                             (:DV 1 1)
                             (:= (* S S))
                             :UP (:DV 2)
                             (:= (* (- MS) (- MS)))
                             :UP (:REWRITE *-PRESERVES->=-FOR-NONNEGATIVES)))

(DEFTHM CALCULATE-MERGE-LEMMA6
        (IMPLIES (AND (RATIONALP L)
                      (< 0 L)
                      (RATIONALP ML)
                      (< ML 0)
                      (<= (- ML) L)
                      (RATIONALP S)
                      (< 0 S)
                      (RATIONALP MS)
                      (< MS 0)
                      (<= (- MS) S))
                 (<= (+ ML MS (EXPT ML 2)
                        (EXPT MS 2)
                        (* 2 ML MS))
                     (+ L S (EXPT L 2)
                        (EXPT S 2)
                        (* 2 L S))))
        :INSTRUCTIONS (:PROMOTE (:REWRITE NOT)
                                (:DV 1)
                                :TOP (:USE CALCULATE-MERGE-LEMMA2)
                                :PROMOTE (:FORWARDCHAIN 1)
                                (:USE CALCULATE-MERGE-LEMMA3)
                                :PROMOTE (:FORWARDCHAIN 1)
                                (:USE CALCULATE-MERGE-LEMMA4)
                                :PROMOTE (:FORWARDCHAIN 1)
                                (:USE CALCULATE-MERGE-LEMMA5)
                                :PROMOTE (:FORWARDCHAIN 1)
                                (:DV 1)
                                (:= NIL)))

(DEFTHM CALCULATE-MERGE-LEMMA7
        (IMPLIES (AND (RATIONALP L)
                      (< 0 L)
                      (RATIONALP ML)
                      (< ML 0)
                      (<= (- ML) L)
                      (RATIONALP S)
                      (< 0 S)
                      (RATIONALP MS)
                      (<= 0 MS)
                      (<= MS S))
                 (<= (+ ML MS) (+ L S)))
        :INSTRUCTIONS (:PROMOTE (:REWRITE NOT)
                                (:DV 1)
                                (:= NIL)))

(DEFTHM CALCULATE-MERGE-LEMMA8
        (IMPLIES (AND (RATIONALP L)
                      (< 0 L)
                      (RATIONALP ML)
                      (< ML 0)
                      (<= (- ML) L)
                      (RATIONALP S)
                      (< 0 S)
                      (RATIONALP MS)
                      (<= 0 MS)
                      (<= MS S))
                 (<= (* 2 ML MS) (* 2 L S)))
        :INSTRUCTIONS (:PROMOTE :PROVE))

(DEFTHM CALCULATE-MERGE-LEMMA9
        (IMPLIES (AND (RATIONALP L)
                      (< 0 L)
                      (RATIONALP ML)
                      (< ML 0)
                      (<= (- ML) L)
                      (RATIONALP S)
                      (< 0 S)
                      (RATIONALP MS)
                      (<= 0 MS)
                      (<= MS S))
                 (<= (EXPT ML 2) (EXPT L 2)))
        :INSTRUCTIONS (:PROMOTE :PROVE))

(DEFTHM CALCULATE-MERGE-LEMMA10
        (IMPLIES (AND (RATIONALP L)
                      (< 0 L)
                      (RATIONALP ML)
                      (< ML 0)
                      (<= (- ML) L)
                      (RATIONALP S)
                      (< 0 S)
                      (RATIONALP MS)
                      (<= 0 MS)
                      (<= MS S))
                 (<= (EXPT MS 2) (EXPT S 2)))
        :INSTRUCTIONS (:PROMOTE :PROVE))



(DEFTHM CALCULATE-MERGE-LEMMA11
        (IMPLIES (AND (RATIONALP L)
                      (< 0 L)
                      (RATIONALP ML)
                      (< ML 0)
                      (<= (- ML) L)
                      (RATIONALP S)
                      (< 0 S)
                      (RATIONALP MS)
                      (<= 0 MS)
                      (<= MS S))
                 (<= (+ ML MS (EXPT ML 2)
                        (EXPT MS 2)
                        (* 2 ML MS))
                     (+ L S (EXPT L 2)
                        (EXPT S 2)
                        (* 2 L S))))
        :INSTRUCTIONS (:PROMOTE (:USE CALCULATE-MERGE-LEMMA7)
                                (:USE CALCULATE-MERGE-LEMMA8)
                                (:USE CALCULATE-MERGE-LEMMA9)
                                (:USE CALCULATE-MERGE-LEMMA10)
                                :PROMOTE :PROMOTE
                                :PROMOTE :PROMOTE (:FORWARDCHAIN 1)
                                (:FORWARDCHAIN 1)
                                (:FORWARDCHAIN 1)
                                (:FORWARDCHAIN 1)
                                :PROVE))

(defthm calculate-merge-lemma12
	(IMPLIES (AND (RATIONALP L)
              (< 0 L)
              (RATIONALP ML)
              (<= 0 ML)
              (<= ML L)
              (RATIONALP S)
              (< 0 S)
              (RATIONALP MS)
              (< MS 0)
              (<= (- MS) S))
         (<= (+ ML MS)
             (+ L S ))))

(defthm calculate-merge-lemma13
	(IMPLIES (AND (RATIONALP L)
              (< 0 L)
              (RATIONALP ML)
              (<= 0 ML)
              (<= ML L)
              (RATIONALP S)
              (< 0 S)
              (RATIONALP MS)
              (< MS 0)
              (<= (- MS) S))
         (<= (* 2 ML MS)
             (* 2 L S))))

(defthm calculate-merge-lemma14
	(IMPLIES (AND (RATIONALP L)
              (< 0 L)
              (RATIONALP ML)
              (<= 0 ML)
              (<= ML L)
              (RATIONALP S)
              (< 0 S)
              (RATIONALP MS)
              (< MS 0)
              (<= (- MS) S))
         (<= (expt ML 2)
             (expt L 2))))	

(defthm calculate-merge-lemma15
	(IMPLIES (AND (RATIONALP L)
              (< 0 L)
              (RATIONALP ML)
              (<= 0 ML)
              (<= ML L)
              (RATIONALP S)
              (< 0 S)
              (RATIONALP MS)
              (< MS 0)
              (<= (- MS) S))
         (<= (expt MS 2)
             (expt S 2))))	

(DEFTHM CALCULATE-MERGE-LEMMA16
        (IMPLIES (AND (RATIONALP L)
                      (< 0 L)
                      (RATIONALP ML)
                      (<= 0 ML)
                      (<= ML L)
                      (RATIONALP S)
                      (< 0 S)
                      (RATIONALP MS)
                      (< MS 0)
                      (<= (- MS) S))
                 (<= (+ ML MS (EXPT ML 2)
                        (EXPT MS 2)
                        (* 2 ML MS))
                     (+ L S (EXPT L 2)
                        (EXPT S 2)
                        (* 2 L S))))
        :INSTRUCTIONS (:PROMOTE (:USE CALCULATE-MERGE-LEMMA12)
                                (:USE CALCULATE-MERGE-LEMMA13)
                                (:USE CALCULATE-MERGE-LEMMA14)
                                (:USE CALCULATE-MERGE-LEMMA15)
                                :PROMOTE :PROMOTE
                                :PROMOTE :PROMOTE (:FORWARDCHAIN 1)
                                (:FORWARDCHAIN 1)
                                (:FORWARDCHAIN 1)
                                (:FORWARDCHAIN 1)
                                :PROVE))

(defthm calculate-merge-lemma17
	(IMPLIES (AND (RATIONALP L)
              (< 0 L)
              (RATIONALP ML)
              (<= 0 ML)
              (<= ML L)
              (RATIONALP S)
              (< 0 S)
              (RATIONALP MS)
              (<= 0 MS)
              (<= MS S))
         (<= (+ ML MS)
             (+ L S ))))

(defthm calculate-merge-lemma18
	(IMPLIES (AND (RATIONALP L)
              (< 0 L)
              (RATIONALP ML)
              (<= 0 ML)
              (<= ML L)
              (RATIONALP S)
              (< 0 S)
              (RATIONALP MS)
              (<= 0 MS)
              (<= MS S))
         (<= (* 2 ML MS)
             (* 2 L S))))

(defthm calculate-merge-lemma19
	(IMPLIES (AND (RATIONALP L)
              (< 0 L)
              (RATIONALP ML)
              (<= 0 ML)
              (<= ML L)
              (RATIONALP S)
              (< 0 S)
              (RATIONALP MS)
              (<= 0 MS)
              (<= MS S))
         (<= (expt ML 2)
             (expt L 2))))	

(defthm calculate-merge-lemma20
	(IMPLIES (AND (RATIONALP L)
              (< 0 L)
              (RATIONALP ML)
              (<= 0 ML)
              (<= ML L)
              (RATIONALP S)
              (< 0 S)
              (RATIONALP MS)
              (<= 0 MS)
              (<= MS S))
         (<= (expt MS 2)
             (expt S 2))))	

(DEFTHM CALCULATE-MERGE-LEMMA21
        (IMPLIES (AND (RATIONALP L)
                      (< 0 L)
                      (RATIONALP ML)
                      (<= 0 ML)
                      (<= ML L)
                      (RATIONALP S)
                      (< 0 S)
                      (RATIONALP MS)
                      (<= 0 MS)
                      (<= MS S))
                 (<= (+ ML MS (EXPT ML 2)
                        (EXPT MS 2)
                        (* 2 ML MS))
                     (+ L S (EXPT L 2)
                        (EXPT S 2)
                        (* 2 L S))))
        :INSTRUCTIONS (:PROMOTE (:USE CALCULATE-MERGE-LEMMA17)
                                (:USE CALCULATE-MERGE-LEMMA18)
                                (:USE CALCULATE-MERGE-LEMMA19)
                                (:USE CALCULATE-MERGE-LEMMA20)
                                :PROMOTE :PROMOTE
                                :PROMOTE :PROMOTE (:FORWARDCHAIN 1)
                                (:FORWARDCHAIN 1)
                                (:FORWARDCHAIN 1)
                                (:FORWARDCHAIN 1)
                                :PROVE))

(defthm calculate-merge-lemma22
	(implies (and (rational-pair (cons l ml))
		      (rational-pair (cons s ms)))
		 (<= 0 (calculate-merge-coefficient-factor 
				l ml s ms)))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities
				|(- (+ x y))|
				|(- (* c x))|
				PREFER-POSITIVE-ADDENDS-EQUAL))))

(defthm calculate-merge-lemma23
	(implies (and (rational-pair (cons l ml))
		      (rational-pair (cons s ms)))
		 (rationalp (calculate-merge-coefficient-helper 
				l ml s ms)))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities
				|(- (+ x y))|
				|(- (* c x))|
				PREFER-POSITIVE-ADDENDS-EQUAL))))

(DEFTHM CALCULATE-MERGE-LEMMA24
        (IMPLIES (AND (RATIONAL-PAIR (CONS L ML))
                      (RATIONAL-PAIR (CONS S MS)))
                 (RATIONALP (CALCULATE-MERGE-COEFFICIENT L ML S MS)))
        :INSTRUCTIONS (:PROMOTE (:DV 1)
                                :EXPAND
                                :TOP (:USE CALCULATE-MERGE-LEMMA23)
                                :PROMOTE (:FORWARDCHAIN 1)
                                (:USE CALCULATE-MERGE-LEMMA1)
                                :PROMOTE (:FORWARDCHAIN 1)
                                :PROVE))

(defthm calculate-merge-lemma25
	(implies (and (rational-pair (cons l ml))
		      (rational-pair (cons s ms)))
		 (<= 0 (calculate-merge-coefficient-helper 
				l ml s ms)))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities
				|(- (+ x y))|
				|(- (* c x))|
				PREFER-POSITIVE-ADDENDS-EQUAL))))

(DEFTHM CALCULATE-MERGE-LEMMA26
        (IMPLIES (AND (RATIONAL-PAIR (CONS L ML))
                      (RATIONAL-PAIR (CONS S MS)))
                 (<= 0
                     (CALCULATE-MERGE-COEFFICIENT L ML S MS)))
        :INSTRUCTIONS (:PROMOTE (:USE CALCULATE-MERGE-LEMMA25)
                                (:USE CALCULATE-MERGE-LEMMA22)
                                :PROMOTE :PROMOTE (:FORWARDCHAIN 1)
                                (:FORWARDCHAIN 1)
                                (:DV 2)
                                :EXPAND :TOP (:REWRITE NOT)
                                (:DV 1)
                                :TOP (:USE CALCULATE-MERGE-LEMMA23)
                                (:USE CALCULATE-MERGE-LEMMA1)
                                :PROMOTE :PROMOTE (:FORWARDCHAIN 1)
                                (:FORWARDCHAIN 1)
                                (:DV 1)
                                (:REWRITE TWO-POSIITVE-PRODUCT)))

;---------append and merge states--------------

(defun all-different (b y)
	(if (atom y)
	    t
	    (and (not (equal b (first-coupled-state-pair y)))
		 (all-different b (cdr y)))))

(defun all-same (b y)
	(if (atom y)
	    t
	    (and (equal b (first-coupled-state-pair y))
		 (all-same b (cdr y)))))

(defun delete-same-helper (b y)
	(if (atom y)
	    nil
	    (if (equal b (first-coupled-state-pair y))
		(delete-same-helper b (cdr y))
		(cons (car y) (delete-same-helper b (cdr y))))))


(defun delete-same (b y)
	(if (atom y)
	    0
	    (if (all-same b y)
		0
		(delete-same-helper b y))))

(defun equal-list (x y)
	(if (atom x)
	    (if (atom y)
		t
		nil)
	    (and (equal (car x) (car y))
		 (equal-list (cdr x) (cdr y)))))

(defthm all-same-property-1
	(implies (all-same b y)
		 (all-same b (cdr y))))
  
(defthm delete-same-property-1 
	(implies (and ;(rational-pair (car b))
		      ;(rational-pair (cdr b))
		      (true-coupled-list y)
		      (not (atom y)))
		 (true-coupled-list (delete-same-helper b y)))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities
			 	|(+ x (if a b c))|
				|(- (if a b c))|
				|(< (if a b c) x)|
				|(< x (if a b c))|
				|(equal (if a b c) x)|
				DEFAULT-RATIONAL-DENOMINATOR
				DEFAULT-LESS-THAN-1))))


(defthm delete-same-property-2
	(implies (and (true-coupled-state y)
		      (not (atom y))
		      (not (true-coupled-list (delete-same x y))))
		 (equal (delete-same x y) 0))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities))))


(defthm delete-same-property-3 
	(implies (and (true-coupled-state y)
		      (consp y)
		      (not (all-same b y)))
		 (equal (delete-same b y)
			(delete-same-helper b y)))
	:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities))))

	 

#||
(defthm detele-same-property-3
	(implies (and (true-coupled-list y)
		      (consp y)
		      (rational-pair (car b))
		      (rational-pair (cdr b))
		      (all-different b y))
		 (consp (delete-same-helper b y) y))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities))))
||#



(defthm detele-same-property-4
	(implies (and (true-coupled-list y)
		      (consp y)
		      ;(rational-pair (car b))
		      ;(rational-pair (cdr b))
		      (all-different b y))
		 (equal-list (delete-same-helper b y) y))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities))))


(defthm all-different-property-1
	(implies (and (consp y)
		      (true-coupled-list y)
		      (all-different (cdr x) y))
		 (all-different (cdr x) (cdr y)))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities))))
(defun quantum-pair (a)
	(cdr a))

(defun l-pair (a)
	(car (quantum-pair a)))

(defun s-pair (a)
	(cdr (quantum-pair a)))

(defun l-number (a)
	(car (l-pair a)))

(defun ml-number (a)
	(cdr (l-pair a)))

(defun s-number (a)
	(car (s-pair a)))

(defun ms-number (a)
	(cdr (s-pair a)))



(defun merge-same (a y)
	(if (atom y)
	    a
	    (if (equal (cdr a) (first-coupled-state-pair y))
		(cons (calculate-merge-coefficient 
				    (l-number a)
				    (ml-number a)
				    (s-number a)
				    (ms-number a))
		      (cdr a))
		(merge-same a (cdr y)))))


(defun all-non-negative-coefficient (x)
	(if (atom x)
	    t
	    (and (<= 0 (first-coupled-coefficient x))
		 (rationalp (first-coupled-coefficient x))
		 (all-non-negative-coefficient (cdr x)))))

(defthm true-coupled-list-property 
	(implies (and (consp x)
		      (true-coupled-state x))
		 (all-non-negative-coefficient x))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities))))


(defthm merge-same-property-1 
	(implies (atom y)
		 (equal (merge-same x y)
			x))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities
				|(- (+ x y))|
				|(- (* c x))|))))

(defthm true-coupled-lemma1
	(implies (and (true-coupled-list y)
		      (consp y))
		 (true-coupled-list (cdr y)))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities
				|(- (+ x y))|
				|(- (* c x))|))))


(DEFTHM MERGE-SAME-EQUAL-1
        (IMPLIES (AND (<= 0 (CAR X))
                      (RATIONALP (CAR X))
                      (CONSP Y)
                      (TRUE-COUPLED-LIST Y)
                      (ALL-DIFFERENT (CDR X) Y))
                 (EQUAL (MERGE-SAME X Y) X))
        :INSTRUCTIONS ((:INDUCT (MERGE-SAME X Y))
                       :PROMOTE (:USE MERGE-SAME-PROPERTY-1)
                       :PROMOTE (:USE TRUE-COUPLED-LEMMA1)
                       :PROMOTE (:FORWARDCHAIN 1)
                       :SPLIT (:DV 1)
                       :EXPAND :S-PROP
                       :EXPAND :S-PROP :TOP :S-PROP (:DV 1)
                       :EXPAND :S-PROP :TOP
                       :S-PROP (:USE ALL-DIFFERENT-PROPERTY-1)
                       :PROMOTE (:DV 1)
                       :TOP (:DEMOTE 7)
                       (:DV 1)
                       :EXPAND :S-PROP
                       :TOP :S-PROP))

(defthm merge-same-property-2
	(implies (and (consp y)
		      (true-coupled-list y)
		      (equal (cdr x)
			     (first-coupled-state-pair y))
		      (<= 0 (car x))
		      (rationalp (car x)))
		 (and (rational-pair (cons (l-number x)
				            (ml-number x)))
		      (rational-pair (cons (s-number x)
					    (ms-number x)))))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities
				|(- (+ x y))|
				|(- (* c x))|))))

(DEFTHM MERGE-SAME-PROPERTY-3
        (IMPLIES (AND (<= 0 (CAR X))
                      (RATIONALP (CAR X))
                      (CONSP Y)
                      (TRUE-COUPLED-LIST Y))
                 (RATIONALP (CAR (MERGE-SAME X Y))))
        :INSTRUCTIONS ((:INDUCT (MERGE-SAME X Y))
                       :SPLIT (:DV 1 1)
                       :EXPAND :S-PROP
                       :EXPAND :S-PROP :TOP :S-PROP (:DV 1 1)
                       :EXPAND :S-PROP :TOP :S-PROP (:DEMOTE 6)
                       (:USE TRUE-COUPLED-LEMMA1)
                       :PROMOTE (:DV 1 1)
                       :EXPAND :S-PROP :UP (:REWRITE CAR-CONS)
                       :TOP (:USE MERGE-SAME-PROPERTY-2)
                       :PROMOTE (:FORWARDCHAIN 1)
                       (:DEMOTE 7)
                       :PROMOTE (:REWRITE CALCULATE-MERGE-LEMMA24)))

(DEFTHM MERGE-SAME-PROPERTY-4
        (IMPLIES (AND (<= 0 (CAR X))
                      (RATIONALP (CAR X))
                      (CONSP Y)
                      (TRUE-COUPLED-LIST Y))
                 (<= 0 (CAR (MERGE-SAME X Y))))
        :INSTRUCTIONS ((:INDUCT (MERGE-SAME X Y))
                       :PROMOTE :SPLIT (:DV 2 1)
                       :EXPAND :S-PROP
                       :EXPAND :S-PROP :TOP :S-PROP (:DV 2 1)
                       :EXPAND :S-PROP :TOP :S-PROP (:DEMOTE 6)
                       (:DV 1)
                       :EXPAND
                       :S-PROP :TOP :S-PROP :PROMOTE (:DV 2 1)
                       :EXPAND :S-PROP :UP (:REWRITE CAR-CONS)
                       :TOP (:USE MERGE-SAME-PROPERTY-2)
                       :PROMOTE (:FORWARDCHAIN 1)
                       (:DEMOTE 7)
                       :PROMOTE (:REWRITE NOT)
                       (:DV 1)
                       (:REWRITE CALCULATE-MERGE-LEMMA26)))

(DEFTHM MERGE-SAME-PROPERTY-5
        (EQUAL (CDR (MERGE-SAME X Y)) (CDR X))
        :INSTRUCTIONS ((:INDUCT (MERGE-SAME X Y))
                       (:DV 1 1)
                       :EXPAND :S-PROP :TOP :S-PROP (:DV 1 1)
                       :EXPAND :S-PROP :UP (:REWRITE CDR-CONS)
                       :TOP
                       :S-PROP (:DV 1 1)
                       :EXPAND :S-PROP
                       :TOP :S-PROP))

(defthm merge-same-property-6 
	(implies (rational-pair x)
		 (rational-pair (cons (car x) (cdr x))))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities))))
	
(DEFTHM MERGE-SAME-PROPERTY
        (IMPLIES (AND (TRUE-COUPLED-ELEMENT X)
                      (TRUE-COUPLED-LIST Y)
                      (CONSP Y))
                 (TRUE-COUPLED-ELEMENT (MERGE-SAME X Y)))
        :INSTRUCTIONS ((:INDUCT (MERGE-SAME X Y))
                       :SPLIT (:DEMOTE 5)
                       (:DV 1)
                       :EXPAND :S-PROP :TOP :S-PROP (:DV 1)
                       :EXPAND :S-PROP :TOP :S-PROP (:DV 1)
                       :EXPAND :S-PROP :EXPAND
                       :S-PROP :TOP :S-PROP :PROMOTE (:DV 1)
                       :EXPAND :S-PROP :UP (:DEMOTE 3)
                       (:DV 1)
                       :EXPAND :TOP :PROMOTE :EXPAND (:DV 1 1)
                       (:REWRITE CAR-CONS)
                       (:DV 1)
                       :EXPAND (:DV 1)
                       :EXPAND (:DV 1)
                       :EXPAND :UP :UP :UP (:DV 2)
                       :EXPAND (:DV 1)
                       :EXPAND (:DV 1)
                       :EXPAND :UP :UP :UP (:DV 3)
                       :EXPAND (:DV 1)
                       :EXPAND (:DV 1)
                       :EXPAND :UP :UP :UP (:DV 4)
                       :EXPAND (:DV 1)
                       :EXPAND (:DV 1)
                       :EXPAND :UP :UP :UP
                       :UP (:REWRITE CALCULATE-MERGE-LEMMA24)
                       :TOP :S-PROP (:DIVE 1)
                       (:DV 1)
                       (:REWRITE CAR-CONS)
                       (:DV 1)
                       :EXPAND (:DV 1)
                       :EXPAND (:DV 1)
                       :EXPAND :UP :UP :UP (:DV 2)
                       :EXPAND (:DV 1)
                       :EXPAND (:DV 1)
                       :EXPAND :UP :UP :UP (:DV 3)
                       :EXPAND (:DV 1)
                       :EXPAND (:DV 1)
                       :EXPAND :UP :UP :UP (:DV 4)
                       :EXPAND (:DV 1)
                       :EXPAND (:DV 1)
                       :EXPAND :UP :UP :UP
                       :UP (:REWRITE CALCULATE-MERGE-LEMMA26)
                       :TOP :S-PROP (:DV 1)
                       (:DV 1 1)
                       :UP (:REWRITE CDR-CONS)
                       :TOP (:DV 2 1 1)
                       :UP (:REWRITE CDR-CONS)
                       :TOP
                       :S-PROP (:REWRITE MERGE-SAME-PROPERTY-6)
                       (:REWRITE MERGE-SAME-PROPERTY-6)
                       (:REWRITE MERGE-SAME-PROPERTY-6)
                       (:REWRITE MERGE-SAME-PROPERTY-6)))






(defun append-and-merge-states-helper (x y)
	(if (atom x)
	    y
	    (if (atom y)
		nil
	    (cons (merge-same (first-coupled-state x) y) 
		  (append-and-merge-states-helper (cdr x)
		  (delete-same (first-coupled-state-pair x) y))))))

(defthm append-and-merge-property-1
	(implies (and (consp x)
		      (true-coupled-list x))
		      (true-coupled-element 
				(first-coupled-state x)))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities))))

(defthm append-and-merge-property-2 
	(implies (and (true-coupled-list x)
		      (true-coupled-element a))
		 (true-coupled-list (cons a x)))
:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities))))


(defthm append-and-merge-property-3
	(true-coupled-list 0))


(DEFTHM APPEND-AND-MERGE-PROPERTY-4
        (IMPLIES (AND (CONSP X)
                      (TRUE-COUPLED-LIST X)
                      (CONSP Y)
                      (TRUE-COUPLED-LIST Y))
                 (TRUE-COUPLED-LIST (APPEND-AND-MERGE-STATES-HELPER X Y)))
        :INSTRUCTIONS ((:INDUCT (APPEND-AND-MERGE-STATES-HELPER X Y))
                       :PROMOTE :SPLIT (:DV 1)
                       :EXPAND :S-PROP :TOP
                       (:REWRITE APPEND-AND-MERGE-PROPERTY-2)
                       (:USE APPEND-AND-MERGE-PROPERTY-1)
                       :PROMOTE (:FORWARDCHAIN 1)
                       (:DV 1)
                       :EXPAND :S-PROP :EXPAND
                       :S-PROP :TOP :SPLIT :EXPAND :S-PROP
                       (:REWRITE DELETE-SAME-PROPERTY-1)
                       (:REWRITE MERGE-SAME-PROPERTY)
                       (:REWRITE APPEND-AND-MERGE-PROPERTY-1)
                       (:DV 1)
                       :EXPAND :S-PROP :TOP
                       (:REWRITE APPEND-AND-MERGE-PROPERTY-2)
                       (:REWRITE MERGE-SAME-PROPERTY)
                       (:REWRITE APPEND-AND-MERGE-PROPERTY-1)
                       (:DEMOTE 4)
                       (:DV 1)
                       :EXPAND :S-PROP :TOP :S-PROP (:DV 1)
                       :EXPAND :S-PROP (:DV 2 2)
                       (:REWRITE DELETE-SAME-PROPERTY-2)
                       :UP :EXPAND :TOP :SPLIT
                       (:REWRITE APPEND-AND-MERGE-PROPERTY-2)
                       :EXPAND
                       :S-PROP (:REWRITE MERGE-SAME-PROPERTY)
                       (:REWRITE APPEND-AND-MERGE-PROPERTY-1)
                       (:REWRITE APPEND-AND-MERGE-PROPERTY-2)
                       (:REWRITE APPEND-AND-MERGE-PROPERTY-3)
                       (:REWRITE MERGE-SAME-PROPERTY)
                       (:REWRITE APPEND-AND-MERGE-PROPERTY-1)
                       :EXPAND :S-PROP (:DV 1)
                       :EXPAND :S-PROP (:DV 2)
                       :EXPAND :S-PROP :TOP :SPLIT
                       (:REWRITE APPEND-AND-MERGE-PROPERTY-2)
                       :EXPAND
                       :S-PROP (:REWRITE MERGE-SAME-PROPERTY)
                       (:REWRITE APPEND-AND-MERGE-PROPERTY-1)
                       (:REWRITE APPEND-AND-MERGE-PROPERTY-2)
                       :EXPAND
                       :S-PROP (:REWRITE MERGE-SAME-PROPERTY)
                       (:REWRITE APPEND-AND-MERGE-PROPERTY-1)))


(defun append-and-merge-states (x y)
	(if (atom x)
	    (if (atom y)
		0
		y)
	    (if (atom y)
		x
		(append-and-merge-states-helper x y))))

(defthm append-valid-lemma1
	(implies (and (atom x)
		      (not (atom y)))
		 (equal (append-and-merge-states x y)
			y)))



(defthm append-valid-lemma2 
	(implies (and (not (atom x))
		      (atom y))
		 (equal (append-and-merge-states x y)
			x)))


(defthm append-valid-lemma3
	(implies (and (atom x)
		      (atom y))
		 (equal (append-and-merge-states x y)
			0)))


(DEFTHM APPEND-VALID-LEMMA4
        (IMPLIES (AND (CONSP X) (CONSP Y))
                 (EQUAL (APPEND-AND-MERGE-STATES X Y)
                        (APPEND-AND-MERGE-STATES-HELPER X Y)))
        :INSTRUCTIONS (:PROMOTE (:DV 1)
                                :EXPAND :S-PROP
                                :TOP :S-PROP))


(DEFTHM APPEND-VALID-LEMMA5
        (IMPLIES (AND (CONSP X)
                      (TRUE-COUPLED-LIST X)
                      (CONSP Y)
                      (TRUE-COUPLED-LIST Y))
                 (CONSP (APPEND-AND-MERGE-STATES-HELPER X Y)))
        :INSTRUCTIONS (:PROMOTE (:DV 1)
                                :EXPAND :S-PROP
                                :TOP :S-PROP))

(defthm append-valid
        (implies (and (true-coupled-state x)
		      (true-coupled-state y))
	     (true-coupled-state (append-and-merge-states x y)))
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
				DEFAULT-PLUS-2
			calculate-merge-coefficient
			REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))))

(ld "quantum-state.lisp")
