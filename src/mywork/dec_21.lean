/-
prove P O 
assume n' and P n'
assume ind_hypothesis for p(n') = 2^0 + 2^1 + 2^n' = 2^(n'+1)

show P(n'+1) = 2^0 + 2^1 = 2^(n')
rw ind_hypothesis 2^(n'+1) - 1 + 2^(n'+1) = 2^(n'+1+1) -1
2^(n'+1) + 2^(n'+1) = 2^(n'+1+1)
2*2^(n'+1) = 2^(n'+1) * 2^1
-/


