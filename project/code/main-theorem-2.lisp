(skip-proofs
(defun all-lowering-valid (x)
	(if (equal x (cons '0 '0))
	    t
	    (and (true-quantum-state 
			(quantum-operator x))
		 (all-lowering-valid 
			(quantum-operator x)))))

(defthm all-quantum-lowering-valid 
	(implies (inital-quantum-state x)
		 (all-lowering-valid x))
:hints (("Goal" :in-theory (disable same-denominator-add 
			        remove-strict-inequalities 
				remove-weak-inequalities
				|(- (* c x))|
				calculate-merge-coefficient
			REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL
			REDUCE-MULTIPLICATIVE-CONSTANT-<
		REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<
		COMMUTATIVITY-OF-MINUS-*-LEFT))))


