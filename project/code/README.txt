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

Please use (ld "initialize.txt")

test values:

(quantum-operator '((1 . (3/2 . 3/2)) . ((1 . ((1 . 1) . (1/2 . 1/2))))))

(quantum-operator (quantum-operator '((1 . (3/2 . 3/2)) . ((1 . ((1 . 1) . (1/2 . 1/2)))))))

(quantum-operator (quantum-operator (quantum-operator '((1 . (3/2 . 3/2)) . ((1 . ((1 . 1) . (1/2 . 1/2))))))))

(quantum-operator (quantum-operator (quantum-operator (quantum-operator '((1 . (3/2 . 3/2)) . ((1 . ((1 . 1) . (1/2 . 1/2)))))))))
