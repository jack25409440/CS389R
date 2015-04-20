;-----------------Quantum Operator---------------

(defun quantum-operator-helper (x)
       (cons (j-lowering-operator (get-jstate x))
	     (append-and-merge-states 
		(l-lowering-operator (get-coupled-state x))
		(s-lowering-operator (get-coupled-state x)))))

(defun quantum-operator (x)
	(if (and (equal (get-jstate x) 0)
		 (equal (get-coupled-state x) 0))
	    x
	    (quantum-operator-helper (normalize-state x))))

(defthm quantum-operator-valid 
	(implies (true-quantum-state x)
		 (true-quantum-state (quantum-operator x)))
	:hints (("Goal" :in-theory (disable same-denominator-add 
				remove-strict-inequalities 
				remove-weak-inequalities))))

	


