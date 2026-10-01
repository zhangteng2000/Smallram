import ModifiedCartan.ScalarSphericalLine
import ModifiedCartan.ScalarSphereValues
import ModifiedCartan.RescaledGauge
import ModifiedCartan.ScalarSharpScaleBounds
import ModifiedCartan.JetLogCompactness

open scoped Topology ComplexConjugate
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- The actual homogeneous linear form vanishing at a scalar target. -/
def scalarTargetLinearForm (β : WithTop ℂ) (q p : ℂ) : ℂ :=
  β.recTopCoe q (fun b => p - b * q)

def scalarTargetLinearSize (β : WithTop ℂ) : ℝ :=
  β.recTopCoe 1 (fun b => 1 + ‖b‖)

theorem scalarTargetLinearSize_pos (β : WithTop ℂ) : 0 < scalarTargetLinearSize β := by
  induction β using WithTop.recTopCoe with
  | top => exact zero_lt_one
  | coe b => exact add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg b)

/-- Projective distance controls the target's homogeneous linear form
linearly, including the target at infinity. There is no square-root loss. -/
theorem scalarTargetLinearForm_le_sphere_distance (β : WithTop ℂ) {q p : ℂ}
    (hne : q ≠ 0 ∨ p ≠ 0) :
    ‖scalarTargetLinearForm β q p‖ ≤ scalarTargetLinearSize β *
      ‖scalarSphereProjection q p - scalarSphereValue β‖ * (‖q‖ + ‖p‖) := by
  have hE := scalarPairEnergy_complex_ne_zero hne
  induction β using WithTop.recTopCoe with
  | top =>
    let e := scalarSphereProjection q p
    have hid : q = e.1 * p + e.2 * q := by
      change q = (q * conj p / (q * conj q + p * conj p)) * p +
        (q * conj q / (q * conj q + p * conj p)) * q
      rw [div_mul_eq_mul_div₀, div_mul_eq_mul_div₀, ← add_div]
      apply (eq_div_iff hE).2
      ring
    have h₁ := norm_fst_le e
    have h₂ := norm_snd_le e
    change ‖q‖ ≤ 1 * ‖e - (0 : ℂ × ℂ)‖ * (‖q‖ + ‖p‖)
    simp only [sub_zero, one_mul]
    calc
      _ = ‖e.1 * p + e.2 * q‖ := congrArg norm hid
      _ ≤ ‖e.1‖ * ‖p‖ + ‖e.2‖ * ‖q‖ := by simpa only [norm_mul] using norm_add_le (e.1 * p) (e.2 * q)
      _ ≤ ‖e‖ * ‖p‖ + ‖e‖ * ‖q‖ := add_le_add
        (mul_le_mul_of_nonneg_right h₁ (norm_nonneg p)) (mul_le_mul_of_nonneg_right h₂ (norm_nonneg q))
      _ = _ := by ring
  | coe b =>
    let e := scalarSphereProjection q p - scalarSphereValue (b : WithTop ℂ)
    have hD : (1 : ℂ) + b * conj b ≠ 0 := by
      simpa only [map_one, one_mul] using
        (scalarPairEnergy_complex_ne_zero (q := (1 : ℂ)) (p := b) (Or.inl one_ne_zero))
    have hEc : conj (q * conj q + p * conj p) = q * conj q + p * conj p := by
      simp only [map_add, map_mul, Complex.conj_conj]
      ring
    have hDc : conj ((1 : ℂ) + b * conj b) = 1 + b * conj b := by
      simp only [map_add, map_mul, map_one, Complex.conj_conj]
      ring
    have hval : scalarSphereValue (b : WithTop ℂ) =
        (conj b / (1 + b * conj b), 1 / (1 + b * conj b)) := by
      change scalarSphereProjection 1 b = _
      simp only [scalarSphereProjection, map_one, one_mul]
    have he : e = (q * conj p / (q * conj q + p * conj p) - conj b / (1 + b * conj b),
        q * conj q / (q * conj q + p * conj p) - 1 / (1 + b * conj b)) := by
      dsimp only [e]
      rw [hval]
      rfl
    have hidp : (p - b * q) * conj p / (q * conj q + p * conj p) = -e.2 - b * e.1 := by
      rw [he]
      dsimp only [Prod.fst, Prod.snd]
      field_simp [hE, hD]
      <;> ring
    have hidq : (p - b * q) * conj q / (q * conj q + p * conj p) = conj e.1 - b * e.2 := by
      rw [he]
      dsimp only [Prod.fst, Prod.snd]
      rw [map_sub, map_div₀, map_div₀, map_mul, Complex.conj_conj, Complex.conj_conj, hEc, hDc]
      field_simp [hE, hD]
      <;> ring
    have h₁ := norm_fst_le e
    have h₂ := norm_snd_le e
    have hp : ‖(p - b * q) * conj p / (q * conj q + p * conj p)‖ ≤ (1 + ‖b‖) * ‖e‖ := by
      rw [hidp]
      calc
        _ ≤ ‖e.2‖ + ‖b‖ * ‖e.1‖ := by simpa only [norm_neg, norm_mul] using norm_sub_le (-e.2) (b * e.1)
        _ ≤ ‖e‖ + ‖b‖ * ‖e‖ := add_le_add h₂ (mul_le_mul_of_nonneg_left h₁ (norm_nonneg b))
        _ = _ := by ring
    have hq : ‖(p - b * q) * conj q / (q * conj q + p * conj p)‖ ≤ (1 + ‖b‖) * ‖e‖ := by
      rw [hidq]
      calc
        _ ≤ ‖e.1‖ + ‖b‖ * ‖e.2‖ := by simpa only [Complex.norm_conj, norm_mul] using norm_sub_le (conj e.1) (b * e.2)
        _ ≤ ‖e‖ + ‖b‖ * ‖e‖ := add_le_add h₁ (mul_le_mul_of_nonneg_left h₂ (norm_nonneg b))
        _ = _ := by ring
    have hid : p - b * q = ((p - b * q) * conj p / (q * conj q + p * conj p)) * p +
        ((p - b * q) * conj q / (q * conj q + p * conj p)) * q := by
      field_simp [hE]
      <;> ring
    change ‖p - b * q‖ ≤ (1 + ‖b‖) * ‖e‖ * (‖q‖ + ‖p‖)
    calc
      _ = ‖((p - b * q) * conj p / (q * conj q + p * conj p)) * p +
          ((p - b * q) * conj q / (q * conj q + p * conj p)) * q‖ := congrArg norm hid
      _ ≤ ‖(p - b * q) * conj p / (q * conj q + p * conj p)‖ * ‖p‖ +
          ‖(p - b * q) * conj q / (q * conj q + p * conj p)‖ * ‖q‖ := by
        simpa only [norm_mul] using norm_add_le
          (((p - b * q) * conj p / (q * conj q + p * conj p)) * p)
          (((p - b * q) * conj q / (q * conj q + p * conj p)) * q)
      _ ≤ ((1 + ‖b‖) * ‖e‖) * ‖p‖ + ((1 + ‖b‖) * ‖e‖) * ‖q‖ := add_le_add
        (mul_le_mul_of_nonneg_right hp (norm_nonneg p)) (mul_le_mul_of_nonneg_right hq (norm_nonneg q))
      _ = _ := by ring

theorem scalarVector_target_linear_bound (v : Index 1 → ℂ) (β : WithTop ℂ)
    (hne : v 0 ≠ 0 ∨ v 1 ≠ 0) :
    ‖scalarTargetLinearForm β (v 0) (v 1)‖ ≤
      (2 * scalarTargetLinearSize β) * euclideanNorm v *
        ‖scalarSphereProjection (v 0) (v 1) - scalarSphereValue β‖ := by
  have hq := (norm_le_pi_norm v 0).trans (norm_le_euclideanNorm _)
  have hp := (norm_le_pi_norm v 1).trans (norm_le_euclideanNorm _)
  have hh := scalarTargetLinearForm_le_sphere_distance β hne
  calc
    _ ≤ scalarTargetLinearSize β * ‖scalarSphereProjection (v 0) (v 1) - scalarSphereValue β‖ *
        (‖v 0‖ + ‖v 1‖) := hh
    _ ≤ scalarTargetLinearSize β * ‖scalarSphereProjection (v 0) (v 1) - scalarSphereValue β‖ *
        (2 * euclideanNorm v) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (scalarTargetLinearSize_pos β).le (norm_nonneg _))
    _ = _ := by ring

theorem scalarCurve_target_linear_bound (f : Curve 1) (β : WithTop ℂ) (z : ℂ) :
    ‖scalarTargetLinearForm β (f.coord 0 z) (f.coord 1 z)‖ ≤
      (2 * scalarTargetLinearSize β) * euclideanNorm (fun j => f.coord j z) *
        ‖scalarCurveSphere f z - scalarSphereValue β‖ :=
  scalarVector_target_linear_bound (fun j => f.coord j z) β (scalar_curve_reduced_pair f z)

theorem scalarRescaled_target_linear_bound (f : Curve 1) (β : WithTop ℂ)
    (r : ℝ) (H : ℂ → ℂ) (z : ℂ) :
    ‖scalarTargetLinearForm β (rescaledRepresentation f r H 0 z)
      (rescaledRepresentation f r H 1 z)‖ ≤
      (2 * scalarTargetLinearSize β) *
        euclideanNorm (fun j => rescaledRepresentation f r H j z) *
          ‖scalarCurveSphere f ((r : ℂ) * z) - scalarSphereValue β‖ := by
  have hne : rescaledRepresentation f r H 0 z ≠ 0 ∨
      rescaledRepresentation f r H 1 z ≠ 0 := by
    rcases scalar_curve_reduced_pair f ((r : ℂ) * z) with h | h
    · exact Or.inl (mul_ne_zero (Complex.exp_ne_zero _) h)
    · exact Or.inr (mul_ne_zero (Complex.exp_ne_zero _) h)
  have hh := scalarVector_target_linear_bound (fun j => rescaledRepresentation f r H j z) β hne
  simpa only [rescaledRepresentation, scalarSphereProjection_mul (Complex.exp_ne_zero _),
    scalarCurveSphere] using hh

/-- Exact exponential coefficient for the target form, before the harmless
fixed multiplicative factor is absorbed; auxiliary to LaTeX `thm:A` (b). -/
theorem scalarRescaled_target_exp_bound (f : Curve 1) (β : WithTop ℂ)
    {r s M κ C : ℝ} {H : ℂ → ℂ} {z : ℂ}
    (hN : euclideanNorm (fun j => rescaledRepresentation f r H j z) ≤ Real.exp (M * s))
    (hD : ‖scalarCurveSphere f ((r : ℂ) * z) - scalarSphereValue β‖ ≤ C * Real.exp (-κ * s)) :
    ‖scalarTargetLinearForm β (rescaledRepresentation f r H 0 z)
      (rescaledRepresentation f r H 1 z)‖ ≤
      (2 * scalarTargetLinearSize β * C) * Real.exp ((M - κ) * s) := by
  have hβ := scalarTargetLinearSize_pos β
  calc
    _ ≤ (2 * scalarTargetLinearSize β) *
        euclideanNorm (fun j => rescaledRepresentation f r H j z) *
          ‖scalarCurveSphere f ((r : ℂ) * z) - scalarSphereValue β‖ :=
      scalarRescaled_target_linear_bound f β r H z
    _ ≤ (2 * scalarTargetLinearSize β) * Real.exp (M * s) *
          (C * Real.exp (-κ * s)) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hN (by positivity)) hD (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [show (M - κ) * s = M * s + (-κ * s) by ring, Real.exp_add]
      ring

/-- Uniform target log bounds on any actual sets of points, including zeros
of the target form. The loss in exponent can be arbitrarily small. -/
theorem scalarRescaled_target_log_bound_eventually (f : Curve 1) (β : WithTop ℂ)
    {r s : ℕ → ℝ} {H : ℕ → ℂ → ℂ} {D : ℕ → Set ℂ} {M κ C ε : ℝ}
    (hs : Tendsto s atTop atTop) (hC : 0 ≤ C) (hε : 0 < ε)
    (hN : ∀ᶠ ν in atTop, ∀ z ∈ D ν,
      euclideanNorm (fun j => rescaledRepresentation f (r ν) (H ν) j z) ≤ Real.exp (M * s ν))
    (hD : ∀ᶠ ν in atTop, ∀ z ∈ D ν,
      ‖scalarCurveSphere f ((r ν : ℂ) * z) - scalarSphereValue β‖ ≤ C * Real.exp (-κ * s ν)) :
    ∀ᶠ ν in atTop, ∀ z ∈ D ν,
      normalizedExtendedLog (s ν) (fun w => scalarTargetLinearForm β
        (rescaledRepresentation f (r ν) (H ν) 0 w)
        (rescaledRepresentation f (r ν) (H ν) 1 w)) z ≤ ((M - κ + ε : ℝ) : EReal) := by
  have hβ := scalarTargetLinearSize_pos β
  have habs := constant_mul_exp_neg_le_eventually hs
    (show -(M - κ + ε) < -(M - κ) by linarith)
    (show 0 ≤ 2 * scalarTargetLinearSize β * C by positivity)
  filter_upwards [hN, hD, habs, hs.eventually_gt_atTop 0] with ν hNν hDν habsν hsν
  intro z hz
  apply (normalizedExtendedLog_le_iff_norm_le_exp hsν _ z (M - κ + ε)).2
  have hh := scalarRescaled_target_exp_bound f β (hNν z hz) (hDν z hz)
  exact hh.trans (by simpa only [neg_neg] using habsν)

end
end ModifiedCartan
#print axioms ModifiedCartan.scalarTargetLinearForm_le_sphere_distance
#print axioms ModifiedCartan.scalarCurve_target_linear_bound
#print axioms ModifiedCartan.scalarRescaled_target_exp_bound
#print axioms ModifiedCartan.scalarRescaled_target_log_bound_eventually
