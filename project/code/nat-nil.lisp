; A natural number is a list of nils. Each nil is considered a half integer

;map all the elements in the list to nil
(defun mapnil (x)
	(if (consp x)
	    (cons nil (mapnil (cdr x)))
	    nil))

;append two nil-lists together
(defun nil-list-plus (x y)
	(if (consp x)
	    (cons nil (nil-list-plus (cdr x) y))
	    (mapnil y)))

;multiply two nil-lists
(defun nil-list-times (x y)
	(if (consp x)
	    (append (mapnil y) (nil-list-times (cdr x) y))
	    nil))

;add two natural numbers
(defun nat-plus (a b)
	(if (consp a)
	    (cons (nil-list-plus (nil-list-times (car a) (cdr b))
				 (nil-list-times (cdr a) (car b)))
	          (nil-list-times (cdr a) (cdr b)))
	    nil))

;multiply two natural numbers
(defun nat-times (a b)
	(if (consp a)
	    (cons (nil-list-times (car a) (car b))
	          (nil-list-times (cdr a) (cdr b)))
	    nil))

;determine if all elements in the list are nil
(defun true-nilp (x)
	(if (consp x)
	    (and (not (car x))
		 (true-nilp (cdr x)))
            (not x)))

;determine if a pair represent a natural number
(defun true-nil-natpair (x)
	(and (true-nilp (car x))
	     (true-nilp (cdr x))))

;determine if a pair represents a natural number
(defun equal-nat (x y)
	(if (consp x)
	    (equal (/ (len (car x)) (len (car y)))
		   (/ (len (cdr x)) (len (cdr y))))
	    nil))

(defthm equal-nilp
	(implies (true-nilp x)
		 (equal (mapnil x) x)))
