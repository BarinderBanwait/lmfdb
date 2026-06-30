import IdealArithmetic.Examples.NF5_1_3790297_2.Invariants5_1_3790297_2

noncomputable section

open Polynomial NumberField

/- Number field `K(α)` with `α` root of the polynomial `X^5 - X^4 + 3*X^2 + 21*X + 4`. -/

lemma T_def' : K = AdjoinRoot (map (algebraMap ℤ ℚ) (X^5 - X^4 + 3*X^2 + 21*X + 4)) := rfl

lemma T_irreducible' : Irreducible (X^5 - X^4 + 3*X^2 + 21*X + 4 : ℤ[X]) := irreducible_T

theorem O_ringOfIntegers : O = RingOfIntegers K := O_ringOfIntegers'

-- `LMFDB_discriminant` and `LMFDB_classNumber` below are PLACEHOLDERS: this source
-- file deliberately contains no discriminant / class-number values of its own.
-- The LMFDB download endpoint substitutes the live values from the `nf_fields`
-- database table here.  The proof terms (`K_discr`, `class_number_K_eq_4`) are
-- fixed and independently checked, so the resulting file compiles if and only if
-- the substituted database values are the true ones.
theorem K_discr' : discr K = LMFDB_discriminant := K_discr

lemma K_nrComplexPlaces' : InfinitePlace.nrComplexPlaces K = 2 := K_nrComplexPlaces

def class_group_equiv' :
  (∀ i : Fin 2 , (ZMod (![2, 2] i))) ≃+ Additive (ClassGroup (RingOfIntegers K)) := class_group_equiv

theorem class_number_K_eq_4' : classNumber K = LMFDB_classNumber := class_number_K_eq_4 