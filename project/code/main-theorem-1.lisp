;Main Theorem 1

(DEFTHM INITIAL-STATE-LOWERING-VALID
        (IMPLIES (INITIAL-QUANTUM-STATE X)
                 (TRUE-QUANTUM-STATE (QUANTUM-OPERATOR X)))
        :INSTRUCTIONS
        ((:DV 1)
         :EXPAND :TOP :PROMOTE (:DV 1)
         :EXPAND (:DV 1)
         (:= NIL)
         :UP :S-PROP (:DV 1)
         :EXPAND (:DIVE 1)
         (:= NIL)
         :UP :S-PROP (:DV 1)
         (:= T)
         :UP :S-PROP :UP :EXPAND (:DV 1 1)
         :EXPAND (:REWRITE CAR-CONS)
         :UP :UP (:DV 2)
         (:DV 1 1)
         :EXPAND (:REWRITE CDR-CONS)
         :EXPAND (:DV 1)
         (:= T)
         :UP :S-PROP :UP (:DV 1 2)
         :EXPAND (:DV 1)
         (:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD |(- (* c x))|
                              FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))
         (:= NIL)
         :UP :S-PROP (:DV 1)
         :EXPAND :UP :UP :UP :EXPAND :S-PROP
         (:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD |(- (* c x))|
                              FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT
                              REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
         (:DV 1)
         :EXPAND :S-PROP (:DV 2)
         :EXPAND (:DV 1)
         (:DV 1)
         (:REWRITE CDR-CONS)
         :UP (:= NIL)
         :UP :S-PROP :UP (:DV 1)
         :UP :UP :EXPAND :S-PROP (:DV 1)
         (:= NIL)
         :UP :S-PROP :EXPAND (:DV 1)
         :S-PROP :UP :S-PROP (:DV 1)
         (:= NIL)
         :UP :S-PROP (:DV 1)
         (:REWRITE CAR-CONS)
         :UP (:DV 2)
         (:DV 1)
         (:REWRITE CDR-CONS)
         :UP :EXPAND :S-PROP :UP :UP (:DV 2 1)
         :EXPAND (:REWRITE CDR-CONS)
         :EXPAND (:DV 1)
         (:= T)
         :UP :S-PROP :UP :EXPAND :S-PROP (:DV 1)
         :EXPAND :S-PROP (:DV 2 1)
         (:REWRITE CDR-CONS)
         (:DV 2)
         (:DV 1)
         :EXPAND :UP :UP :EXPAND (:DV 1)
         (:= NIL)
         :UP :S-PROP :UP :EXPAND (:DV 1)
         (:= NIL)
         :UP
         :S-PROP :UP :UP :EXPAND :S-PROP (:DV 1)
         (:= NIL)
         :UP :S-PROP :EXPAND :S-PROP (:DV 1)
         (:= NIL)
         :UP :S-PROP (:DV 1)
         (:REWRITE CAR-CONS)
         :UP (:DV 2)
         (:DV 1)
         (:REWRITE CDR-CONS)
         :UP (:= NIL)
         :UP :UP (:DV 2)
         (:DV 1)
         (:DV 1 2)
         :EXPAND (:DV 1)
         (:= NIL)
         :UP :S-PROP (:DV 1)
         :EXPAND :UP :UP :UP
         :UP :UP :EXPAND :S-PROP :EXPAND (:DV 2)
         :S-PROP (:DV 2)
         (:DV 2)
         (:DV 1)
         :EXPAND (:DV 1)
         :UP (:REWRITE CAR-CONS)
         :UP :UP :EXPAND :S-PROP (:DV 1)
         (:= NIL)
         :UP :S-PROP :EXPAND :S-PROP (:DV 1)
         (:= NIL)
         :UP :S-PROP (:DV 1)
         (:REWRITE CAR-CONS)
         :UP (:DV 2)
         (:DV 2)
         (:REWRITE CDR-CONS)
         :UP
         :EXPAND :S-PROP :UP :UP :EXPAND (:DV 1)
         (:DV 1 1)
         :UP (:REWRITE CDR-CONS)
         :UP :S-PROP :UP (:DV 1)
         (:DV 1)
         :EXPAND (:REWRITE CAR-CONS)
         :UP :EXPAND :S-PROP (:DV 1)
         (:= NIL)
         :UP :S-PROP (:DV 2)
         (:REWRITE CDR-CONS)
         :UP
         :EXPAND :S-PROP :UP :UP :S-PROP :UP :UP
         (:IN-THEORY (DISABLE SAME-DENOMINATOR-ADD |(- (* c x))|
                              FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT
                              REDUCE-MULTIPLICATIVE-CONSTANT-<
                              REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL
                              REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
         :PROVE))






