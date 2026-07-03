# Formally certifying invariants of number fields in Lean
This extends the work in [RingOfIntegersProject
](https://github.com/alainchmt/RingOfIntegersProject). In addition to verifying the ring of integers of number fields, this project aims to certify the discriminant, signature, the class group structure, and class number of number fields. We can also certify generators of the group of units modulo $p$-th powers. 

**This is work in progress.**

## Some examples in Lean
The following files certify the ring of integers, discriminant, number of complex places, the class group structure, and class number of the corresponding number fields.  

- `IdealArithmetic/Examples/NF2_0_231_1/Results2_0_231_1`: defining polynomial $X^2 - X + 58$. 
- `IdealArithmetic/Examples/NF3_1_24843_1/Results3_1_24843_1`: defining polynomial $X^3 - 91$
- `IdealArithmetic/Examples/NF4_0_76176_2/Results4_0_76176_2`: defining polynomial $X^4 - 2X^3 + 7X^2 - 6X + 78$
- `IdealArithmetic/Examples/NF4_4_54381317_1/Results4_4_54381317_1` : defining polynomial $X^4 - X^3 - 80X^2 - 332X - 383$
- `IdealArithmetic/Examples/NF5_1_3790297_2/Results5_1_3790297_2` : defining polynomial $X^5 - X^4 + 3X^2 + 21X + 4$.
