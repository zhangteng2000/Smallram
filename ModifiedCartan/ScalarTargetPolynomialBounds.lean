import ModifiedCartan.ScalarTargetUnitary
import ModifiedCartan.ReplacementNormProperties

open scoped Topology Matrix
open Filter Set Metric Matrix
set_option autoImplicit false
namespace ModifiedCartan

/-- The actual target component of a Taylor polynomial retains the sharp
exponent when the constructed Taylor accuracy dominates the negative bound. -/
theorem scalarTargetPolynomial_exp_bound (f : Curve 1) (β : WithTop ℂ)
    {r s M κ C A : ℝ} {H : ℂ → ℂ} {z : ℂ} {p : Index 1 → Polynomial ℂ}
    (hs : 0 ≤ s) (hA : κ - M ≤ A)
    (herr : ∀ j, ‖(p j).eval z - rescaledRepresentation f r H j z‖ ≤ Real.exp (-A * s))
    (hN : euclideanNorm (fun j => rescaledRepresentation f r H j z) ≤ Real.exp (M * s))
    (hD : ‖scalarCurveSphere f ((r : ℂ) * z) - scalarSphereValue β‖ ≤ C * Real.exp (-κ * s)) :
    ‖(polynomialMatrixGauge p (scalarTargetUnitary β : Matrix (Index 1) (Index 1) ℂ) 0).eval z‖ ≤
      (2 * scalarTargetLinearSize β * C + scalarTargetLinearSize β) * Real.exp ((M - κ) * s) := by
  let v : Index 1 → ℂ := fun j => (p j).eval z
  let w : Index 1 → ℂ := fun j => rescaledRepresentation f r H j z
  let V := (scalarTargetUnitary β : Matrix (Index 1) (Index 1) ℂ)
  have he : (polynomialMatrixGauge p V 0).eval z = (v ᵥ* V) 0 :=
    congrFun (polynomialMatrixGauge_eval_vecMul p V z) 0
  have hdiff : ‖(v ᵥ* V) 0 - (w ᵥ* V) 0‖ ≤ scalarTargetLinearSize β * Real.exp (-A * s) :=
    scalarTargetUnitary_first_difference_bound β (Real.exp_pos _).le herr
  have hw : ‖(w ᵥ* V) 0‖ ≤ (2 * scalarTargetLinearSize β * C) * Real.exp ((M - κ) * s) :=
    (scalarTargetUnitary_first_norm_le β w).trans (scalarRescaled_target_exp_bound f β hN hD)
  have hexp : Real.exp (-A * s) ≤ Real.exp ((M - κ) * s) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith : -A ≤ M - κ) hs)
  change ‖(polynomialMatrixGauge p V 0).eval z‖ ≤ _
  rw [he]
  calc
    _ = ‖(w ᵥ* V) 0 + ((v ᵥ* V) 0 - (w ᵥ* V) 0)‖ := by congr 1; abel
    _ ≤ ‖(w ᵥ* V) 0‖ + ‖(v ᵥ* V) 0 - (w ᵥ* V) 0‖ := norm_add_le _ _
    _ ≤ (2 * scalarTargetLinearSize β * C) * Real.exp ((M - κ) * s) +
        scalarTargetLinearSize β * Real.exp (-A * s) := add_le_add hw hdiff
    _ ≤ (2 * scalarTargetLinearSize β * C) * Real.exp ((M - κ) * s) +
        scalarTargetLinearSize β * Real.exp ((M - κ) * s) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hexp (scalarTargetLinearSize_pos β).le)
    _ = _ := by ring

/-- Uniform polynomial target log caps on actual selected points. The Taylor
accuracy is supplied by `exists_arbitrary_radius_limits_normalized_with_accuracy`.
Auxiliary to LaTeX `thm:A` (b). -/
theorem PolynomialReplacementData.scalar_target_log_cap
    {f : Curve 1} {r s : ℕ → ℝ} {C₀ A L : ℝ} {H : ℕ → ℂ → ℂ}
    {p : ℕ → Index 1 → Polynomial ℂ}
    {a : (ν : ℕ) → Fin (FewInflection.polynomialWronskian (p ν)).natDegree → ℂ}
    {η : ℕ → ℝ} (h : PolynomialReplacementData f r s C₀ A L H p a η)
    (β : WithTop ℂ) {D : ℕ → Set ℂ} {M κ C ε : ℝ}
    (hs : Tendsto s atTop atTop) (hC : 0 ≤ C) (hε : 0 < ε) (hA : κ - M ≤ A)
    (hDΩ : ∀ ν, D ν ⊆ ball (0 : ℂ) 4)
    (hN : ∀ᶠ ν in atTop, ∀ z ∈ D ν,
      euclideanNorm (fun j => rescaledRepresentation f (r ν) (H ν) j z) ≤ Real.exp (M * s ν))
    (hD : ∀ᶠ ν in atTop, ∀ z ∈ D ν,
      ‖scalarCurveSphere f ((r ν : ℂ) * z) - scalarSphereValue β‖ ≤ C * Real.exp (-κ * s ν)) :
    ∀ᶠ ν in atTop, ∀ z ∈ D ν,
      normalizedExtendedLog (s ν)
        (fun w => (polynomialMatrixGauge (p ν)
          (scalarTargetUnitary β : Matrix (Index 1) (Index 1) ℂ) 0).eval w) z ≤
            ((M - κ + ε : ℝ) : EReal) := by
  have hβ := scalarTargetLinearSize_pos β
  have habs := constant_mul_exp_neg_le_eventually hs
    (show -(M - κ + ε) < -(M - κ) by linarith)
    (show 0 ≤ 2 * scalarTargetLinearSize β * C + scalarTargetLinearSize β by positivity)
  filter_upwards [h.jet_error, hN, hD, habs, hs.eventually_gt_atTop 0] with ν he hNν hDν haν hsν
  intro z hz
  apply (normalizedExtendedLog_le_iff_norm_le_exp hsν _ z (M - κ + ε)).2
  have herr : ∀ j, ‖(p ν j).eval z - rescaledRepresentation f (r ν) (H ν) j z‖ ≤
      Real.exp (-A * s ν) := by
    intro j
    simpa only [iteratedDeriv_zero] using he j 0 (by omega) z
      ((closedBall_subset_closedBall (by norm_num : (4 : ℝ) ≤ 16)) (ball_subset_closedBall (hDΩ ν hz)))
  exact (scalarTargetPolynomial_exp_bound f β hsν.le hA herr (hNν z hz) (hDν z hz)).trans
    (by simpa only [neg_neg] using haν)

end ModifiedCartan
#print axioms ModifiedCartan.scalarTargetPolynomial_exp_bound
#print axioms ModifiedCartan.PolynomialReplacementData.scalar_target_log_cap
