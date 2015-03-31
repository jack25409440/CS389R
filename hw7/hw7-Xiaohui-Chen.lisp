;----From v-adder-example.lisp. Courtesy to Dr. Hunt------

(defthm fold-constants-in-plus
  (implies (and (syntaxp (quotep x))
                (syntaxp (quotep y)))
           (equal (+ x y z)
                  (+ (+ x y) z))))

(defthm nth-add1-bdd
  (equal (nth (+ 1 n) x)
         (if* (zp (1+ n))
              (car x)
              (nth n (cdr x)))))

(defun div-2 (x)
  (declare (xargs :guard t))
  (if (<= (nfix x) 1)
      0
    (+ 1 (div-2 (- x 2)))))

(defun one-at-a-time (x)
  (if (zp x)
      0
    (one-at-a-time (- x 1))))

(defthm div-2-lemma-0
  (implies (natp x)
           (equal (div-2 (* 2 x))
                  x))
  :hints (("Goal" :induct (one-at-a-time x))))

(defthm div-2-lemma-1
  (implies (natp x)
           (equal (div-2 (+ 1 (* 2 x)))
                  x))
  :hints (("Goal" :induct (one-at-a-time x))))

(defun rem-2 (x)
  (declare (xargs :guard t))
  (if (<= (nfix x) 1)
      (nfix x)
    (rem-2 (- x 2))))

(defthm rem-2-lemma-0
  (implies (natp x)
           (equal (rem-2 (* 2 x))
                  0))
  :hints (("Goal" :induct (one-at-a-time x))))

(defthm rem-2-lemma-1
  (implies (natp x)
           (equal (rem-2 (+ 1 (* 2 x)))
                  1))
  :hints (("Goal" :induct (one-at-a-time x))))

;---------Small Endian Notation-----------
;uncomment this if necessary

(defun v-to-nat (a)
  (declare (xargs :guard t))
  (if (atom a)
      0
    (+ (if (car a) 1 0)
       (* 2 (v-to-nat (cdr a))))))

(defun nat-to-v (x l)
  (declare (xargs :guard (and (natp x)
                              (natp l))))
  (if (zp l)
      nil
    (cons (if (= (rem-2 x) 1) t nil)
	  (nat-to-v (div-2 x) (1- l)))))


;------------Big Endian Noation-----------------

;delte the last element of a list
(defun delete-last (x)
	(declare (xargs :guard (consp x)))
	(if (atom (cdr x))
	    (cdr x)
	    (cons (car x) (delete-last (cdr x)))))

;big Endian version of v-to-nat
(defun v-to-nat-big (a)
	(declare (xargs :guard t))
	(if (atom a)
	    0
	    (+ (if (car (last a)) 1 0)
	       (* 2 (v-to-nat-big (delete-last a))))))

;insert an element as the last element of the list
(defun affix-v (a b)
    (declare (xargs :guard (not (consp b))))
    (if (atom a)
	(cons b nil)
	(cons (car a) (affix-v (cdr a) b))))

;big Endian version of nat-to-v
(defun nat-to-v-big (x l)
    (declare (xargs :guard (and (natp x)
				(natp l))))
    (if (zp l)
	nil
        (if (<= (nfix l) 1)
	    (cons (if (= (rem-2 x) 1) t nil) nil)
	    (affix-v (nat-to-v-big (div-2 x) (1- l))
	             (if (= (rem-2 x) 1) t nil)))))

;calculate the length of the binary bit string
(defun length-binary-nat (x)
	(declare (xargs :guard (natp x)))
	(if (zp x)
	    0
	    (+ 1 (length-binary-nat (div-2 x)))))

(thm (implies (natp x)
	      (natp (length-binary-nat x))))

;This theorem proves that my implementation is correct
(defthm length-valid 
	(implies (natp x)
		 (= (len (nat-to-v-big x (length-binary-nat x)))
	            (length-binary-nat x))))

;prove an equivalence of affix-v
(defthm affix-property 
	(implies (not (consp b))
	         (equal (affix-v a b)
		        (append a (list b)))))


;----Lemmas needed to prove v-to-nat-of-nat-to-v-big------

;nat-to-v always returns a true list
(defthm true-listp-nat-to-v 
	(implies (and (natp x)
		      (natp l))
	         (true-listp (nat-to-v-big x l))))

;if x is odd, the following is true
(defthm odd-multiply 
	(implies (and (natp x)
		      (= (rem-2 x) 1))
		 (= (+ 1 (* 2 (div-2 x)))
		    x)))

;if x is even, the following is true
(defthm even-multiply 
	(implies (and (natp x)
		      (= (rem-2 x) 0))
		 (= (* 2 (div-2 x))
		    x)))

(defthm last-append 
	(equal (last (append a (list b)))
	       (list b)))

;deleting the last element of (append a (list b) is equivalent 
;to a, given a is not an atom and a is a boolean list 
(defthm delete-last-append 
	(implies (and (consp a)
	              (boolean-listp a))
		 (equal (delete-last (append a (list b)))
		 	a)))

;function (rem-2 x) returns either 0 or 1
(defthm exclusive-rem-2 
	(implies (not (= (rem-2 x) 1))
		 (= (rem-2 x) 0)))

;A lemma proved by proof-checker
;Note: we are allowed to use full power of ACL2, so I use 
;:prove and :s commands here
(DEFTHM
 V-TO-NAT-OF-NAT-TO-V-BIG-LEMMA1
 (IMPLIES
    (AND (NOT (ZP X))
         (EQUAL (V-TO-NAT-BIG (NAT-TO-V-BIG (DIV-2 X)
                                            (LENGTH-BINARY-NAT (DIV-2 X))))
                (DIV-2 X))
         (<= 0 X)
         (< 1 (+ 1 (LENGTH-BINARY-NAT (DIV-2 X)))))
    (EQUAL (V-TO-NAT-BIG (APPEND (NAT-TO-V-BIG (DIV-2 X)
                                               (LENGTH-BINARY-NAT (DIV-2 X)))
                                 (LIST (EQUAL (REM-2 X) 1))))
           X))
 :INSTRUCTIONS (:PROMOTE (:DV 1)
                         :EXPAND :S-PROP (:DV 1 1)
                         (:REWRITE LAST-APPEND)
                         :UP (:REWRITE CAR-CONS)
                         :UP :TOP :SPLIT (:DV 1 2 1)
                         :UP (:DV 2 1)
                         (:REWRITE DELETE-LAST-APPEND)
                         :UP :=
                         :UP :TOP :S :PROVE :PROVE :S (:DV 1 2 1)
                         (:REWRITE DELETE-LAST-APPEND)
                         :UP := :UP (:REWRITE EVEN-MULTIPLY)
                         :UP :S (:DEMOTE 5)
                         :S
                         :PROVE :PROVE))

;The throrem to be proved
(defthm v-to-nat-of-nat-to-v-big 
    (implies (natp x)
	     (equal (v-to-nat-big (nat-to-v-big x
			                   (length-binary-nat x)))
                    x)))

;----Lemmas needed to prove v-to-nat-of-nat-to-v-big------

(DEFTHM V-TO-NAT-OF-NAT-TO-V-LEMMA1
     (IMPLIES (AND (NOT (ZP X))
                   (EQUAL (V-TO-NAT (NAT-TO-V (DIV-2 X)
                                              (LENGTH-BINARY-NAT (DIV-2 X))))
                          (DIV-2 X))
                   (<= 0 X)
                   (NOT (EQUAL (REM-2 X) 1)))
              (EQUAL (* 2 (DIV-2 X)) X))
     :INSTRUCTIONS (:PROMOTE (:DV 1)
                             (:REWRITE EVEN-MULTIPLY)
                             :UP
                             :S-PROP :S))

(defthm v-to-nat-of-nat-to-v 
    (implies (natp x)
	     (equal (v-to-nat (nat-to-v x
			             (length-binary-nat x)))
                    x)))


