# Formal-Logic
## Propositional Logic Natural Deduction Fitch-style proof generator
The algorithm classifies introduction steps (I-steps) and elimination steps (E-steps) and sequentially applies BFS on the finite E-steps with a 1 step lookahead of I-steps to see if elimination is possible. 
## Areas of further improvement
I have not been able to prove the completeness and finiteness of this algorithm due to my lack of knowledge. The algorithm can solve simple PL logic predicates, but fails on proofs that require proof by contradiction. 
