import FewInflection.Gauge
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open scoped BigOperators Topology

namespace FewInflection

noncomputable section

private theorem curve_eq_of_coord_eq
    {n : ℕ} {f g : Curve n} (hcoord : f.coord = g.coord) : f = g := by
  cases f with
  | mk fc fh fr =>
    cases g with
    | mk gc gh gr =>
      simp_all

def transformedPolynomial {n : ℕ}
    (p : Index n → Polynomial ℂ) (A : Matrix (Index n) (Index n) ℂ) :
    Index n → Polynomial ℂ :=
  fun j => ∑ k : Index n, p k * Polynomial.C (A k j)

lemma eval_transformedPolynomial {n : ℕ}
    (p : Index n → Polynomial ℂ) (A : Matrix (Index n) (Index n) ℂ)
    (j : Index n) (z : ℂ) :
    (transformedPolynomial p A j).eval z =
      ∑ k : Index n, (p k).eval z * A k j := by
  simp [transformedPolynomial, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_C]

theorem Curve.matrixGauge_hasPolynomialRepresentation
    {n : ℕ} (f : Curve n) (A : Matrix (Index n) (Index n) ℂ)
    (hA : IsUnit A.det) (hrep : f.HasPolynomialRepresentation) :
    (f.matrixGauge A hA).HasPolynomialRepresentation := by
  rcases hrep with ⟨p, g, hg, hgd, hcoord⟩
  refine ⟨transformedPolynomial p A, g, hg, hgd, ?_⟩
  intro j z
  change (∑ k : Index n, f.coord k z * A k j) =
    g z * (transformedPolynomial p A j).eval z
  rw [eval_transformedPolynomial]
  rw [show (∑ k : Index n, f.coord k z * A k j) =
      ∑ k : Index n, (g z * (p k).eval z) * A k j by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hcoord k z]]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma matrixGauge_coord_mul_inverse
    {n : ℕ} (f : Curve n) (A : Matrix (Index n) (Index n) ℂ)
    (hA : IsUnit A.det) (j : Index n) (z : ℂ) :
    f.coord j z =
      ∑ k : Index n, (f.matrixGauge A hA).coord k z * A⁻¹ k j := by
  change f.coord j z =
    ∑ k : Index n, (∑ l : Index n, f.coord l z * A l k) * A⁻¹ k j
  have hmat : ∀ l : Index n, ∑ k : Index n, A l k * A⁻¹ k j =
      (1 : Matrix (Index n) (Index n) ℂ) l j := by
    intro l
    exact congrFun (congrFun (Matrix.mul_nonsing_inv A hA) l) j
  calc
    f.coord j z =
        ∑ l : Index n, f.coord l z *
          (1 : Matrix (Index n) (Index n) ℂ) l j := by
            simp [Matrix.one_apply]
    _ = ∑ l : Index n, f.coord l z *
          (∑ k : Index n, A l k * A⁻¹ k j) := by
            apply Finset.sum_congr rfl
            intro l hl
            rw [hmat]
    _ = ∑ l : Index n, ∑ k : Index n,
          (f.coord l z * A l k) * A⁻¹ k j := by
            apply Finset.sum_congr rfl
            intro l hl
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            ring
    _ = ∑ k : Index n, ∑ l : Index n,
          (f.coord l z * A l k) * A⁻¹ k j := by
            rw [Finset.sum_comm]
    _ = ∑ k : Index n, (∑ l : Index n,
          f.coord l z * A l k) * A⁻¹ k j := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [Finset.sum_mul]

theorem Curve.matrixGauge_transcendental_iff
    {n : ℕ} (f : Curve n) (A : Matrix (Index n) (Index n) ℂ)
    (hA : IsUnit A.det) :
    f.Transcendental ↔ (f.matrixGauge A hA).Transcendental := by
  constructor
  · intro htrans hrep
    apply htrans
    rcases hrep with ⟨p, g, hg, hgd, hcoord⟩
    refine ⟨transformedPolynomial p A⁻¹, g, hg, hgd, ?_⟩
    intro j z
    rw [matrixGauge_coord_mul_inverse f A hA j z]
    rw [show (∑ k : Index n, (f.matrixGauge A hA).coord k z * A⁻¹ k j) =
        ∑ k : Index n, (g z * (p k).eval z) * A⁻¹ k j by
          apply Finset.sum_congr rfl
          intro k hk
          rw [hcoord k z]]
    rw [eval_transformedPolynomial]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  · intro htrans hrep
    apply htrans
    exact Curve.matrixGauge_hasPolynomialRepresentation f A hA hrep

/-- An invertible constant matrix preserves linear nondegeneracy in both
directions. -/
theorem Curve.matrixGauge_linearlyNonDegenerate_iff
    {n : ℕ} (f : Curve n) (A : Matrix (Index n) (Index n) ℂ)
    (hA : IsUnit A.det) :
    f.linearlyNonDegenerate ↔
      (f.matrixGauge A hA).linearlyNonDegenerate := by
  constructor
  · exact Curve.matrixGauge_linearlyNonDegenerate f A hA
  · intro hlin
    have hAi : IsUnit A⁻¹.det := Matrix.isUnit_nonsing_inv_det A hA
    have hback := Curve.matrixGauge_linearlyNonDegenerate
      (f.matrixGauge A hA) A⁻¹ hAi hlin
    have hcomp : (f.matrixGauge A hA).matrixGauge A⁻¹ hAi = f := by
      apply curve_eq_of_coord_eq
      funext j z
      change ∑ k : Index n,
        (f.matrixGauge A hA).coord k z * A⁻¹ k j = f.coord j z
      exact (matrixGauge_coord_mul_inverse f A hA j z).symm
    simpa only [hcomp] using hback

end

end FewInflection
