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


(defthm initial-state-lemma-25 
	(implies (initial-quantum-state x)
		 (not (consp (cddr x))))
	:hints (("Goal" :in-theory (disable same-denominator-add 
			        remove-strict-inequalities 
				remove-weak-inequalities
				|(- (* c x))|
		FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT)
		:use (:instance initial-state-lemma-2 
				(x (cdr x))))))

(DEFTHM
 INITIAL-STATE-LEMMA-26
 (IMPLIES
   (INITIAL-QUANTUM-STATE X)
   (EQUAL
        (APPEND-AND-MERGE-STATES-HELPER (L-LOWERING-OPERATOR-HELPER (CDR X))
                                        (S-LOWERING-OPERATOR-HELPER (CDR X)))
        (LIST (L-LOWERING-TO-STATE (CDR X))
              (S-LOWERING-TO-STATE (CDR X)))))
 :INSTRUCTIONS
 (:PROMOTE (:DV 1)
           :EXPAND
           (:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD |(- (* c x))|
                                FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))
           (:DV 1)
           (:= T)
           :UP :S-PROP (:DV 1)
           (:= T)
           :UP :S-PROP (:DV 2 2)
           (:DV 1 1)
           :EXPAND (:DV 1)
           (:= T)
           :UP :UP :EXPAND (:DV 1)
           :UP (:= (L-LOWERING-TO-STATE (CDR X)))
           :UP :UP :EXPAND (:DV 1)
           (:= T)
           :UP :S-PROP (:DV 1)
           (:= NIL)
           :UP :S-PROP :EXPAND (:DV 1)
           (:= T)
           :UP :S-PROP (:DV 1)
           (:= NIL)
           :UP :S-PROP (:DV 1 1)
           :EXPAND (:DV 1)
           (:= T)
           :UP :S-PROP :UP (:REWRITE CAR-CONS)
           :UP (:DV 2)
           :EXPAND (:DV 1)
           (:DV 1 1)
           :EXPAND (:DV 1)
           (:= T)
           :UP :S-PROP :UP (:REWRITE CDR-CONS)
           :EXPAND (:= NIL)
           :UP :S-PROP :UP :UP :EXPAND (:DV 1)
           (:DV 1)
           (:DV 1)
           :EXPAND (:DV 1)
           (:= T)
           :UP :S-PROP :UP (:REWRITE CDR-CONS)
           :EXPAND (:= NIL)
           :UP :S-PROP :UP (:DV 1)
           (:DV 1 1)
           :EXPAND (:DV 1)
           (:= T)
           :UP
           :S-PROP :UP :EXPAND (:REWRITE CAR-CONS)
           :UP :EXPAND (:DV 1)
           (:= T)
           :UP :S-PROP (:DV 1)
           (:= NIL)
           :UP :S-PROP :EXPAND (:DV 1 1)
           (:DV 1)
           :EXPAND (:DV 1)
           (:= T)
           :UP :S-PROP :UP (:REWRITE CDR-CONS)
           :EXPAND (:= NIL)
           :UP
           :S-PROP :UP
           :UP :S-PROP))

(DEFTHM
 INITIAL-STATE-LEMMA-27
 (IMPLIES
  (INITIAL-QUANTUM-STATE X)
  (EQUAL-J
      (LIST* (* 2 (CADAR X))
             (CADAR X)
             (+ -1 (CADAR X)))
      (APPEND-AND-MERGE-STATES-HELPER (L-LOWERING-OPERATOR-HELPER (CDR X))
                                      (S-LOWERING-OPERATOR-HELPER (CDR X)))))
 :INSTRUCTIONS
 (:PROMOTE (:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD |(- (* c x))|
                                FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))
           (:DV 2)
           (:REWRITE INITIAL-STATE-LEMMA-26)
           :TOP (:= T)))

(DEFTHM
 INITIAL-STATE-LEMMA-28
 (IMPLIES
  (INITIAL-QUANTUM-STATE X)
  (EQUAL-MJ
      (LIST* (* 2 (CADAR X))
             (CADAR X)
             (+ -1 (CADAR X)))
      (APPEND-AND-MERGE-STATES-HELPER (L-LOWERING-OPERATOR-HELPER (CDR X))
                                      (S-LOWERING-OPERATOR-HELPER (CDR X)))))
 :INSTRUCTIONS
 (:PROMOTE (:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD |(- (* c x))|
                                FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))
           (:DV 2)
           (:REWRITE INITIAL-STATE-LEMMA-26)
           :TOP (:= T)))


(DEFTHM
    INITIAL-STATE-LEMMA-29
    (IMPLIES (INITIAL-QUANTUM-STATE X)
             (TRUE-COUPLED-LIST (L-LOWERING-OPERATOR-HELPER (CDR X))))
    :INSTRUCTIONS
    (:PROMOTE (:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD |(- (* c x))|
                                   FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))
              (:USE (:INSTANCE L-LOWERING-VALID (X (CDR X))))
              :PROMOTE (:FORWARDCHAIN 1)
              (:DEMOTE 2)
              (:DV 1)
              :EXPAND (:DV 1)
              (:= T)
              :UP :S-PROP (:DV 1)
              :EXPAND (:DV 1)
              (:= T)
              :UP :S-PROP
              (:= (L-LOWERING-OPERATOR-HELPER (CDR X)))
              :UP
              :UP :S-PROP))

(DEFTHM
    INITIAL-STATE-LEMMA-30
    (IMPLIES (INITIAL-QUANTUM-STATE X)
             (TRUE-COUPLED-LIST (S-LOWERING-OPERATOR-HELPER (CDR X))))
    :INSTRUCTIONS
    (:PROMOTE (:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD |(- (* c x))|
                                   FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))
              (:USE (:INSTANCE S-LOWERING-VALID (X (CDR X))))
              :PROMOTE (:FORWARDCHAIN 1)
              (:DEMOTE 2)
              (:= T)))


(DEFTHM
 INITIAL-STATE-LEMMA-31
 (IMPLIES
  (INITIAL-QUANTUM-STATE X)
  (RATIONALP
   (CAAR
     (APPEND-AND-MERGE-STATES-HELPER (L-LOWERING-OPERATOR-HELPER (CDR X))
                                     (S-LOWERING-OPERATOR-HELPER (CDR X))))))
 :INSTRUCTIONS
 (:PROMOTE (:DV 1 1)
           (:REWRITE INITIAL-STATE-LEMMA-26)
           :UP (:REWRITE CAR-CONS)
           :EXPAND (:DV 1)
           (:= T)
           :UP :S-PROP (:DV 1)
           (:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD))
           (:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD |(- (* c x))|
                                FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))
           (:= NIL)
           :UP :S-PROP
           :UP (:REWRITE CAR-CONS)
           :UP (:= T)))

(DEFTHM
 INITIAL-STATE-LEMMA-32
 (IMPLIES
  (INITIAL-QUANTUM-STATE X)
  (<=
   0
   (CAAR
     (APPEND-AND-MERGE-STATES-HELPER (L-LOWERING-OPERATOR-HELPER (CDR X))
                                     (S-LOWERING-OPERATOR-HELPER (CDR X))))))
 :INSTRUCTIONS
 ((:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD |(- (* c x))|
                       FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))
  :PROMOTE (:DV 2)
  (:DV 1)
  (:REWRITE INITIAL-STATE-LEMMA-26)
  :UP (:REWRITE CAR-CONS)
  :UP :UP
  :UP (:= T)))


(DEFTHM
 INITIAL-STATE-LEMMA-33
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
  (EQUAL-J
      (LIST* (* 2 (CADAR X))
             (CADAR X)
             (+ -1 (CADAR X)))
      (APPEND-AND-MERGE-STATES-HELPER (L-LOWERING-OPERATOR-HELPER (CDR X))
                                      (S-LOWERING-OPERATOR-HELPER (CDR X)))))
 :INSTRUCTIONS
 (:PROMOTE (:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD |(- (* c x))|
                                FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))
           (:REWRITE INITIAL-STATE-LEMMA-27)
           :PROVE))

(DEFTHM
 INITIAL-STATE-LEMMA-34
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
  (EQUAL-MJ
      (LIST* (* 2 (CADAR X))
             (CADAR X)
             (+ -1 (CADAR X)))
      (APPEND-AND-MERGE-STATES-HELPER (L-LOWERING-OPERATOR-HELPER (CDR X))
                                      (S-LOWERING-OPERATOR-HELPER (CDR X)))))
 :INSTRUCTIONS
 (:PROMOTE (:REWRITE INITIAL-STATE-LEMMA-28)
           (:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD |(- (* c x))|
                                FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))
           (:= T)))

(defthm initial-state-lemma-35 
	(implies (rational-pair x)
		 (integerp (+ (car x) (cdr x))))
	:hints (("Goal" :in-theory (disable same-denominator-add 
			        remove-strict-inequalities 
				remove-weak-inequalities))))

(defthm initial-state-lemma-36 
	(implies (initial-quantum-state x)
		 (not (lower-or-lowest-l-state (cdr x))))
	:hints (("Goal" :in-theory (disable same-denominator-add 
			        remove-strict-inequalities 
				remove-weak-inequalities
				|(- (* c x))|
		FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))))

(DEFTHM INITIAL-STATE-LEMMA-37
        (IMPLIES (AND (RATIONALP X)
                      (EQUAL (DENOMINATOR X) 2))
                 (INTEGERP (* 2 X)))
        :INSTRUCTIONS (:PROMOTE (:DV 1)
                                (:REWRITE COMMUTATIVITY-OF-*)
                                :UP (:REWRITE INTEGER-TIMES-NUMERATOR)))


(DEFTHM INITIAL-STATE-LEMMA-38
        (IMPLIES (AND (RATIONALP (CADDAR (CDR X)))
                      (< 0 (CADDAR (CDR X)))
                      (EQUAL (DENOMINATOR (CADDAR (CDR X)))
                             2))
                 (<= 1 (* 2 (CADDAR (CDR X)))))
        :INSTRUCTIONS
        ((:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD |(- (* c x))|
                              FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))
         :PROMOTE (:DV 2)
         (:= (+ (CADDAR (CDR X)) (CADDAR (CDR X))))
         :UP (:REWRITE INTEGER-SUM)
         (:DV 1)
         (:= (* (CADDAR (CDR X)) 2))
         :UP (:REWRITE INTEGER-TIMES-NUMERATOR)))


(DEFTHM
    INITIAL-STATE-LEMMA-39
    (IMPLIES (AND (EQUAL (CAAR X) 1)
                  (EQUAL (CAADR X) 1)
                  (CONSP (CDR X))
                  (EQUAL (LEN (CDDR X)) 0)
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
                  (CONSP (CADADR X))
                  (RATIONALP (CAADAR (CDR X)))
                  (< 0 (CAADAR (CDR X)))
                  (EQUAL (DENOMINATOR (CAADAR (CDR X))) 2)
                  (CONSP (CDDADR X))
                  (< 0 (CADDAR (CDR X)))
                  (INTEGERP (CADDAR (CDR X)))
                  (TRUE-COUPLED-LIST (CDDR X))
                  (EQUAL (SUM-OF-COUPLED-COEFFICIENT (CDDR X))
                         0)
                  (EQUAL (CADAR X)
                         (+ (CAADAR (CDR X)) (CADDAR (CDR X))))
                  (EQUAL-J (CAR X) (CDDR X))
                  (EQUAL-MJ (CAR X) (CDDR X)))
             (<= 1 (* 2 (CAADAR (CDR X)))))
    :INSTRUCTIONS
    (:PROMOTE (:DV 2)
              (:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD |(- (* c x))|
                                   FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))
              (:= (+ (CAADAR (CDR X)) (CAADAR (CDR X))))
              :UP (:REWRITE INTEGER-SUM)
              (:DV 1)
              (:= (* (CAADAR (CDR X)) 2))
              :UP (:REWRITE INTEGER-TIMES-NUMERATOR)))

(DEFTHM
    INITIAL-STATE-LEMMA-40
    (IMPLIES (AND (EQUAL (CAAR X) 1)
                  (EQUAL (CAADR X) 1)
                  (CONSP (CDR X))
                  (EQUAL (LEN (CDDR X)) 0)
                  (EQUAL (CADAR X) (CDDAR X))
                  (EQUAL (CAADAR (CDR X))
                         (CDADAR (CDR X)))
                  (EQUAL (CADDAR (CDR X))
                         (CDDDAR (CDR X)))
                  (CONSP (CAR X))
                  (CONSP (CDAR X))
                  (< 0 (CADAR X))
                  (INTEGERP (CADAR X))
                  (CONSP (CADADR X))
                  (RATIONALP (CAADAR (CDR X)))
                  (< 0 (CAADAR (CDR X)))
                  (EQUAL (DENOMINATOR (CAADAR (CDR X))) 2)
                  (CONSP (CDDADR X))
                  (RATIONALP (CADDAR (CDR X)))
                  (< 0 (CADDAR (CDR X)))
                  (EQUAL (DENOMINATOR (CADDAR (CDR X))) 2)
                  (TRUE-COUPLED-LIST (CDDR X))
                  (EQUAL (SUM-OF-COUPLED-COEFFICIENT (CDDR X))
                         0)
                  (EQUAL (CADAR X)
                         (+ (CAADAR (CDR X)) (CADDAR (CDR X))))
                  (EQUAL-J (CAR X) (CDDR X))
                  (EQUAL-MJ (CAR X) (CDDR X)))
             (<= 1 (* 2 (CAADAR (CDR X)))))
    :INSTRUCTIONS
    (:PROMOTE (:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD |(- (* c x))|
                                   FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))
              (:DV 2)
              (:= (+ (CAADAR (CDR X)) (CAADAR (CDR X))))
              :UP (:REWRITE INTEGER-SUM)
              (:DV 1)
              (:= (* (CAADAR (CDR X)) 2))
              :TOP (:REWRITE INTEGER-TIMES-NUMERATOR)))

(DEFTHM INITIAL-STATE-LEMMA-41
        (IMPLIES (AND (EQUAL (CAAR X) 1)
                      (EQUAL (CAADR X) 1)
                      (CONSP (CDR X))
                      (EQUAL (LEN (CDDR X)) 0)
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
                      (CONSP (CADADR X))
                      (RATIONALP (CAADAR (CDR X)))
                      (< 0 (CAADAR (CDR X)))
                      (EQUAL (DENOMINATOR (CAADAR (CDR X))) 2)
                      (CONSP (CDDADR X))
                      (RATIONALP (CADDAR (CDR X)))
                      (< 0 (CADDAR (CDR X)))
                      (EQUAL (DENOMINATOR (CADDAR (CDR X))) 2)
                      (TRUE-COUPLED-LIST (CDDR X))
                      (EQUAL (SUM-OF-COUPLED-COEFFICIENT (CDDR X))
                             0)
                      (EQUAL (CADAR X)
                             (+ (CAADAR (CDR X)) (CADDAR (CDR X))))
                      (EQUAL-J (CAR X) (CDDR X))
                      (EQUAL-MJ (CAR X) (CDDR X)))
                 (<= 1 (* 2 (CADAR X))))
        :INSTRUCTIONS
        ((:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD |(- (* c x))|
                              FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))
         :PROMOTE (:DV 2)
         (:= (+ (CADAR X) (CADAR X)))
         :UP (:REWRITE INTEGER-SUM)
         (:DV 1)
         (:= (* (CADAR X) 2))
         :TOP (:REWRITE INTEGER-TIMES-NUMERATOR)))

(DEFTHM
    INITIAL-STATE-LEMMA-42
    (IMPLIES (AND (EQUAL (CAAR X) 1)
                  (EQUAL (CAADR X) 1)
                  (CONSP (CDR X))
                  (EQUAL (LEN (CDDR X)) 0)
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
                  (CONSP (CADADR X))
                  (RATIONALP (CAADAR (CDR X)))
                  (< 0 (CAADAR (CDR X)))
                  (EQUAL (DENOMINATOR (CAADAR (CDR X))) 2)
                  (CONSP (CDDADR X))
                  (RATIONALP (CADDAR (CDR X)))
                  (< 0 (CADDAR (CDR X)))
                  (EQUAL (DENOMINATOR (CADDAR (CDR X))) 2)
                  (TRUE-COUPLED-LIST (CDDR X))
                  (EQUAL (SUM-OF-COUPLED-COEFFICIENT (CDDR X))
                         0)
                  (EQUAL (CADAR X)
                         (+ (CAADAR (CDR X)) (CADDAR (CDR X))))
                  (EQUAL-J (CAR X) (CDDR X))
                  (EQUAL-MJ (CAR X) (CDDR X)))
             (<= 1 (* 2 (CAADAR (CDR X)))))
    :INSTRUCTIONS
    (:PROMOTE (:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD |(- (* c x))|
                                   FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))
              (:DV 2)
              (:= (+ (CAADAR (CDR X)) (CAADAR (CDR X))))
              :UP (:REWRITE INTEGER-SUM)
              (:DV 1)
              (:= (* (CAADAR (CDR X)) 2))
              :UP (:REWRITE INTEGER-TIMES-NUMERATOR)))




	
(ld "main-theorem-1.lisp")
