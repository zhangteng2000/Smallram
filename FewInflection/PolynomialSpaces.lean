import FewInflection.Results
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open scoped BigOperators Topology

namespace FewInflection

noncomputable section

/-! ### Algebraic consequences of the polynomial normal form

The normal form in the order-less-than-one alternative has a nowhere-zero
scalar factor and an invertible constant matrix.  The two elementary facts
below make those hypotheses usable: the representation is polynomial in the
literal sense of `Curve.HasPolynomialRepresentation`, and its coordinates are
linearly independent.  No growth estimate is used here.
-/

theorem RationalNormalForm.hasPolynomialRepresentation
    {n : ℕ} {f : Curve n} (h : RationalNormalForm n f) :
    f.HasPolynomialRepresentation := by
  rcases h.factor with ⟨g, hg, hgdiff, hcoord⟩
  refine ⟨fun j => ∑ k : Index n,
      Polynomial.C (h.A k j) * Polynomial.X ^ (k : ℕ), g, hg, hgdiff, ?_⟩
  intro j z
  rw [hcoord]
  congr 1
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem RationalNormalForm.linearlyNonDegenerate
    {n : ℕ} {f : Curve n} (h : RationalNormalForm n f) :
    f.linearlyNonDegenerate := by
  classical
  rcases h.factor with ⟨g, hg, hgdiff, hcoord⟩
  unfold Curve.linearlyNonDegenerate
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  let d : Index n → ℂ := fun k =>
    ∑ i : Index n, h.A k i * c i
  have hpoly : ∀ z : ℂ,
      ∑ i : Index n, c i * (∑ k : Index n,
        z ^ (k : ℕ) * h.A k i) = 0 := by
    intro z
    have hz := congrFun hc z
    have hz' : g z *
        (∑ i : Index n, c i * (∑ k : Index n,
          z ^ (k : ℕ) * h.A k i)) = 0 := by
      simpa [hcoord, smul_eq_mul, Finset.mul_sum, Finset.sum_mul,
        mul_assoc, mul_left_comm, mul_comm] using hz
    exact (mul_eq_zero.mp hz').resolve_left (hg z)
  have hmon : ∑ k : Index n, d k • monomialFamily n k = 0 := by
    funext z
    simp only [Pi.zero_apply, Finset.sum_apply, smul_eq_mul]
    change ∑ k : Index n, d k * z ^ (k : ℕ) = 0
    have hp := hpoly z
    simp only [d] at hp ⊢
    simp_rw [Finset.sum_mul]
    rw [← Finset.sum_comm]
    simpa [Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm,
      mul_comm] using hp
  have hd : d = 0 := by
    have hli := monomialCurve_linearlyNonDegenerate n
    change LinearIndependent ℂ (monomialFamily n) at hli
    have hdz : ∀ k, d k = 0 := (Fintype.linearIndependent_iff.mp hli) d hmon
    funext k
    exact hdz k
  have hAc : Matrix.mulVec h.A c = Matrix.mulVec h.A (0 : Index n → ℂ) := by
    funext k
    simp only [Matrix.mulVec, dotProduct, d] at hd ⊢
    simpa [Finset.sum_mul, mul_comm] using congrFun hd k
  have hunitA : IsUnit h.A := (Matrix.isUnit_iff_isUnit_det h.A).2 h.A_invertible
  have hAinj : Function.Injective
      (fun x : Index n → ℂ => Matrix.mulVec h.A x) :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunitA
  have hc0 : c = 0 := hAinj hAc
  exact congrFun hc0 j

theorem RationalNormalForm.not_transcendental
    {n : ℕ} {f : Curve n} (h : RationalNormalForm n f) :
    ¬ f.Transcendental := by
  intro htrans
  exact htrans h.hasPolynomialRepresentation

end

end FewInflection
