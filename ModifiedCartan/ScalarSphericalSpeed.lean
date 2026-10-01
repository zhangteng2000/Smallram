import ModifiedCartan.ScalarSphereProjection
import ModifiedCartan.RescaledGauge
import ModifiedCartan.UnitaryNorm
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem scalar_wronskian_formula_function (g : Index 1 → ℂ → ℂ) (z : ℂ) :
    FewInflection.wronskian 1 g z = g 0 z * deriv (g 1) z - g 1 z * deriv (g 0) z := by
  let A : Matrix (Fin 2) (Fin 2) ℂ := fun i j => iteratedDeriv (i : ℕ) (g j) z
  simpa only [FewInflection.wronskian, A, Fin.val_zero, Fin.val_one,
    iteratedDeriv_zero, iteratedDeriv_one] using! Matrix.det_fin_two A

theorem scalarPairEnergy_eq_euclideanNorm_sq (v : Index 1 → ℂ) :
    scalarPairEnergy (v 0) (v 1) = euclideanNorm v ^ 2 := by
  rw [euclideanNorm_sq]
  exact (Fin.sum_univ_two (fun j : Fin 2 => ‖v j‖ ^ 2)).symm

theorem scalar_curve_reduced_pair (f : Curve 1) (z : ℂ) :
    f.coord 0 z ≠ 0 ∨ f.coord 1 z ≠ 0 := by
  obtain ⟨j, hj⟩ := f.reduced z
  fin_cases j
  · exact Or.inl hj
  · exact Or.inr hj

/-- The exact spherical speed of a pair, used in the proof of LaTeX `thm:A` (b).
For a reduced pair its denominator is strictly positive, including at poles. -/
def scalarSphericalSpeed (g : Index 1 → ℂ → ℂ) (z : ℂ) : ℝ :=
  ‖FewInflection.wronskian 1 g z‖ / euclideanNorm (fun j => g j z) ^ 2

theorem scalarSphericalSpeed_nonneg (g : Index 1 → ℂ → ℂ) (z : ℂ) :
    0 ≤ scalarSphericalSpeed g z := div_nonneg (norm_nonneg _) (sq_nonneg _)

theorem scalarSphericalSpeed_rescaled (f : Curve 1) (t : ℝ)
    {H : ℂ → ℂ} {z : ℂ} (hH : AnalyticAt ℂ H z) :
    scalarSphericalSpeed (rescaledRepresentation f t H) z =
      |t| * scalarSphericalSpeed f.coord ((t : ℂ) * z) := by
  have hsum : (∑ i : Index 1, (i : ℕ)) = 1 := by
    simpa only [Fin.val_zero, Fin.val_one, zero_add] using
      Fin.sum_univ_two (fun i : Fin 2 => (i : ℕ))
  unfold scalarSphericalSpeed
  rw [rescaledRepresentation_wronskian f t hH, FewInflection.wronskian_dilate, hsum]
  simp only [Nat.reduceAdd, pow_one, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  change ‖Complex.exp (-H z)‖ ^ 2 * (|t| * ‖FewInflection.wronskian 1 f.coord ((t : ℂ) * z)‖) /
      euclideanNorm (fun j => Complex.exp (-H z) * f.coord j ((t : ℂ) * z)) ^ 2 = _
  rw [euclideanNorm_mul_scalar, mul_pow]
  have hne : ‖Complex.exp (-H z)‖ ≠ 0 := norm_ne_zero_iff.mpr (Complex.exp_ne_zero _)
  field_simp

/-- Composition of a complex derivative with an actual real-parameter path. -/
theorem complex_hasDerivAt_comp_real_path {g : ℂ → ℂ} {γ : ℝ → ℂ}
    {g' γ' : ℂ} {t : ℝ} (hg : HasDerivAt g g' (γ t))
    (hγ : HasDerivAt γ γ' t) :
    HasDerivAt (fun x => g (γ x)) (γ' * g') t := by
  exact (hg.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hγ

/-- Gauge-independent path control of an actual holomorphic curve.
Auxiliary to LaTeX `thm:A` (b), without excluding poles of either chart. -/
theorem scalar_curve_spherical_path_bound (f : Curve 1) {γ γ' : ℝ → ℂ}
    {a b C : ℝ} (hab : a ≤ b)
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (γ' t) t)
    (hbound : ∀ t ∈ Ico a b, ‖γ' t‖ * scalarSphericalSpeed f.coord (γ t) ≤ C) :
    ‖scalarSphereProjection (f.coord 0 (γ b)) (f.coord 1 (γ b)) -
      scalarSphereProjection (f.coord 0 (γ a)) (f.coord 1 (γ a))‖ ≤ C * (b - a) := by
  apply scalarSphereProjection_path_bound hab
    (fun t ht => complex_hasDerivAt_comp_real_path (f.holomorphic 0 (γ t)).hasDerivAt (hγ t ht))
    (fun t ht => complex_hasDerivAt_comp_real_path (f.holomorphic 1 (γ t)).hasDerivAt (hγ t ht))
    (fun t _ => scalar_curve_reduced_pair f (γ t))
  intro t ht
  have he : f.coord 0 (γ t) * (γ' t * deriv (f.coord 1) (γ t)) -
      f.coord 1 (γ t) * (γ' t * deriv (f.coord 0) (γ t)) =
        γ' t * FewInflection.wronskian 1 f.coord (γ t) := by
    rw [scalar_wronskian_formula]
    ring
  change ‖f.coord 0 (γ t) * (γ' t * deriv (f.coord 1) (γ t)) -
      f.coord 1 (γ t) * (γ' t * deriv (f.coord 0) (γ t))‖ / _ ≤ C
  rw [he, norm_mul, scalarPairEnergy_eq_euclideanNorm_sq (fun j => f.coord j (γ t)), mul_div_assoc]
  exact hbound t ht

end
end ModifiedCartan
#print axioms ModifiedCartan.scalarSphericalSpeed_rescaled
#print axioms ModifiedCartan.scalar_curve_spherical_path_bound
