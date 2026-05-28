# Short introduction #
Proof checker is an engine that provides infrostructure for building proves and prove-tactics.
The goal of this project is to make a Haskell-implementation of that engine.<br />

This engine is a machine that obtains expressions defining theorems and their proves. The language of such expressions is High Order Logic (HOL).<br />
Curry-Howard correspondance states that type and its expression-habitants are equivalent to theorems and its evidences. 
The engine translates statements, theorems and operations into HOL-expressions. So the proof checking depends on type 
inferring and verification.<br />
Therefore the project also include Coq-files that proves the correctness of engine's operations.

# Structure of the project #
It consists of:
1. Coq and LaTex files which define expressions, engine operations and prove its properties;
2. Haskell files with engine's implementation;
3. Haskell files with basic logical constructions: forall, exists, and, or, not, implies.
