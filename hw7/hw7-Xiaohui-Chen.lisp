;  The next theorem is used to help prove the following theorem.

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


;----------Big Endian Notation-------------
(defun v-to-nat-big-helper (a n)
	(if (atom a)
	    n
	    (v-to-nat-big-helper (cdr a)
		          (+ (* n 2)
			     (if (car a) 1 0)))))

(defun v-to-nat-big (a)
       (v-to-nat-big-helper a 0))

(defun affix-v (a b)
    (declare (xargs :guard t))
    (if (atom a)
	(cons b nil)
	(cons (car a) (affix-v (cdr a) b))))

(defun nat-to-v-big (x)
    (declare (xargs :guard (natp x)))
    (if (<= (nfix x) 1)
	(cons (if (= (rem-2 x) 1) t nil) nil)
	    (affix-v (nat-to-v-big (div-2 x))
	             (if (= (rem-2 x) 1) t nil))))
#||
(defthm v-to-nat-of-nat-to-v
	(implies (natp x)
		 (equal (v-to-nat-big (nat-to-v-big x))
			x))
         :hints (("Goal" :induct (one-at-a-time x))))
||#
