import FewInflection.PolynomialJets
import FewInflection.PluckerBounds
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Polynomial derivative coefficients and translated roots

These lemmas isolate the part of the polynomial-minor argument that is
available directly from Mathlib: translation by a center sends every root to
its displacement from that center, and Vieta's formula computes every Taylor
coefficient from the corresponding elementary symmetric function.
-/

open scoped BigOperators

namespace FewInflection

noncomputable section

theorem polynomial_taylor_roots_eq_map_sub
    (p : Polynomial ℂ) (a : ℂ) :
    (p.taylor a).roots = p.roots.map (fun x => x - a) := by
  rw [Polynomial.taylor_apply]
  have h := Polynomial.roots_comp_C_mul_X_add_C p 1 a (isUnit_one)
  simpa [sub_eq_add_neg] using h

theorem polynomial_taylor_coeff_eq_roots_esymm
    (p : Polynomial ℂ) (hp : p.Splits) (a : ℂ) {k : ℕ}
    (hk : k ≤ p.natDegree) :
    (p.taylor a).coeff k = p.leadingCoeff *
      (-1) ^ (p.natDegree - k) *
        (p.taylor a).roots.esymm (p.natDegree - k) := by
  have hq := Polynomial.coeff_eq_esymm_roots_of_splits
    (hp.taylor a) (k := k)
    (by simpa [Polynomial.natDegree_taylor] using hk)
  simpa [Polynomial.leadingCoeff_taylor, Polynomial.natDegree_taylor] using hq

theorem polynomial_iteratedDeriv_eval_eq_factorial_mul_roots_esymm
    (p : Polynomial ℂ) (hp : p.Splits) (a : ℂ) {k : ℕ}
    (hk : k ≤ p.natDegree) :
    iteratedDeriv k (fun z : ℂ => p.eval z) a =
      (Nat.factorial k : ℂ) * p.leadingCoeff *
        (-1) ^ (p.natDegree - k) *
          (p.taylor a).roots.esymm (p.natDegree - k) := by
  calc
    iteratedDeriv k (fun z : ℂ => p.eval z) a =
        (Nat.factorial k : ℂ) * (p.taylor a).coeff k := by
      exact (factorial_mul_polynomial_taylor_coeff_eq_jet p a k).symm
    _ = (Nat.factorial k : ℂ) * p.leadingCoeff *
        (-1) ^ (p.natDegree - k) *
          (p.taylor a).roots.esymm (p.natDegree - k) := by
      rw [polynomial_taylor_coeff_eq_roots_esymm p hp a hk]
      ring

theorem polynomial_taylor_coeff_linear_product_eq_elementarySymmetric
    {M s : ℕ} (a : Fin M → ℂ) (z : ℂ) (hs : s ≤ M) :
    (Polynomial.taylor z (∏ i : Fin M,
      (Polynomial.X - Polynomial.C (a i)))).coeff (M - s) =
      elementarySymmetric (fun i => z - a i) s := by
  rw [show Polynomial.taylor z (∏ i : Fin M,
      (Polynomial.X - Polynomial.C (a i))) =
      ∏ i : Fin M, Polynomial.taylor z
        (Polynomial.X - Polynomial.C (a i)) by
    change Polynomial.taylorAlgHom z (∏ i : Fin M,
      (Polynomial.X - Polynomial.C (a i))) = _
    rw [map_prod]
    rfl]
  simp only [show ∀ i : Fin M,
      Polynomial.taylor z (Polynomial.X - Polynomial.C (a i)) =
        Polynomial.X + Polynomial.C (z - a i) by
    intro i
    rw [Polynomial.taylor_apply]
    simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]]
  rw [Finset.prod_X_add_C_coeff (s := (Finset.univ : Finset (Fin M)))
    (fun i => z - a i)]
  · simp [elementarySymmetric]
    rw [Nat.sub_sub_self hs]
  · simpa using Nat.sub_le _ _

theorem polynomial_taylor_coeff_linear_product_div_prod_eq_reciprocal_elementarySymmetric
    {M s : ℕ} (a : Fin M → ℂ) (z : ℂ) (hs : s ≤ M)
    (hroot : ∀ i, z - a i ≠ 0) :
    (Polynomial.taylor z (∏ i : Fin M,
      (Polynomial.X - Polynomial.C (a i)))).coeff s /
        (∏ i : Fin M, (z - a i)) =
      elementarySymmetric (fun i => (z - a i)⁻¹) s := by
  have hsub : M - s ≤ M := Nat.sub_le _ _
  have hcoeff := polynomial_taylor_coeff_linear_product_eq_elementarySymmetric
    a z hsub
  have hcoeff' :
      (Polynomial.taylor z (∏ i : Fin M,
        (Polynomial.X - Polynomial.C (a i)))).coeff s =
        elementarySymmetric (fun i => z - a i) (M - s) := by
    simpa only [Nat.sub_sub_self hs] using hcoeff
  rw [hcoeff']
  exact elementarySymmetric_complement_div_prod (fun i => z - a i) hroot hs

end

end FewInflection
