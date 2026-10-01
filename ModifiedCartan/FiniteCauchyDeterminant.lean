import ModifiedCartan.FiniteCauchyPivot
import Mathlib.LinearAlgebra.Vandermonde

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def finiteVandermondeProduct {K : Type*} [CommRing K] {n : ℕ} (x : Fin n → K) : K :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (x j - x i)

def finiteCauchyDenominator {K : Type*} [CommRing K] {n : ℕ}
    (x y : Fin n → K) : K := ∏ i : Fin n, ∏ j : Fin n, (1 - x i * y j)

theorem finiteVandermondeProduct_succ {K : Type*} [CommRing K] {n : ℕ}
    (x : Fin (n + 1) → K) :
    finiteVandermondeProduct x = (∏ i : Fin n, (x i.succ - x 0)) *
      finiteVandermondeProduct (x ∘ Fin.succ) := by
  simp [finiteVandermondeProduct, Fin.prod_univ_succ, Fin.Ioi_zero_eq_map,
    Finset.prod_map, Fin.coe_succEmb, Fin.prod_Ioi_succ, Function.comp_apply]

theorem finiteCauchyDenominator_succ {K : Type*} [CommRing K] {n : ℕ}
    (x y : Fin (n + 1) → K) :
    finiteCauchyDenominator x y =
      (1 - x 0 * y 0) * (∏ i : Fin n, (1 - x i.succ * y 0)) *
        (∏ j : Fin n, (1 - x 0 * y j.succ)) *
          finiteCauchyDenominator (x ∘ Fin.succ) (y ∘ Fin.succ) := by
  simp only [finiteCauchyDenominator, Fin.prod_univ_succ, Finset.prod_mul_distrib,
    Function.comp_apply]
  ring

theorem firstPivot_product_cancel {K : Type*} [Field K] (a b c p q d t : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a⁻¹ * (p / b * (q / c * d)) * (a * b * c * t) = (p * q) * (d * t) := by
  field_simp

/-- Finite Cauchy determinant with denominators cleared. Auxiliary to the
    Schur identification for paper `lem:KP-correspondence`. -/
theorem finiteCauchyMatrix_det_mul_denominator {K : Type*} [Field K] {n : ℕ}
    (x y : Fin n → K) (h : ∀ i j, 1 - x i * y j ≠ 0) :
    (finiteCauchyMatrix x y).det * finiteCauchyDenominator x y =
      finiteVandermondeProduct x * finiteVandermondeProduct y := by
  induction n with
  | zero => simp [finiteCauchyDenominator, finiteVandermondeProduct]
  | succ n ih =>
    have hi : (∏ i : Fin n, (1 - x i.succ * y 0)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => h i.succ 0)
    have hj : (∏ j : Fin n, (1 - x 0 * y j.succ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun j _ => h 0 j.succ)
    rw [finiteCauchyMatrix_det_succ x y h, finiteCauchyDenominator_succ,
      finiteVandermondeProduct_succ x, finiteVandermondeProduct_succ y]
    simp only [Finset.prod_div_distrib]
    have ht := ih (x ∘ Fin.succ) (y ∘ Fin.succ) (fun i j => h i.succ j.succ)
    calc
      _ = ((∏ i : Fin n, (x i.succ - x 0)) * (∏ j : Fin n, (y j.succ - y 0))) *
          ((finiteCauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ)).det *
            finiteCauchyDenominator (x ∘ Fin.succ) (y ∘ Fin.succ)) := by
        exact firstPivot_product_cancel _ _ _ _ _ _ _ (h 0 0) hi hj
      _ = _ := by rw [ht]; ring

end
end ModifiedCartan

#print axioms ModifiedCartan.finiteCauchyMatrix_det_mul_denominator
