(local (include-book "arithmetic/inequalities" :dir :system))

(local (include-book "arithmetic/equalities" :dir :system))

;------------basic Mathematical theorems------------------

(defthm two-posiitve-product 
	(implies (and (<= 0 a)
		      (rationalp a)
		      (<= 0 b)
		      (rationalp b))
		 (<= 0 (* a b))))

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

(defthm sum-of-two-rationals 
	(implies (and (rationalp a)
		      (rationalp b))
		 (rationalp (+ a b))))

(defthm sum-of-two-non-negative-rationals 
	(implies (and (rationalp a)
		      (rationalp b)
		      (<= 0 a)
		      (<= 0 b))
		 (<= 0 (+ a b))))

(defthm abs-property 
	(equal (<= (abs a) b)
	       (and (<= a b)
		    (<= (- a) b))))

(ld "jstate.lisp")
