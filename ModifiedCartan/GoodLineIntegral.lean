import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

open scoped Topology
open Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Integral control of all increments on an interval, used for the good-path
construction in LaTeX `thm:A` (b). -/
theorem norm_sub_le_integral_derivative_bound_on_interval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {B : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (g t) t)
    (hg : IntervalIntegrable B volume a b)
    (hbound : ∀ t ∈ Icc a b, ‖g t‖ ≤ B t)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖f x - f y‖ ≤ ∫ t in a..b, B t := by
  have hab : a ≤ b := hx.1.trans hx.2
  have haux (u v : ℝ) (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (huv : u ≤ v) :
      ‖f v - f u‖ ≤ ∫ t in a..b, B t := by
    have hsub : Icc u v ⊆ Icc a b := Icc_subset_Icc hu.1 hv.2
    have hgi : IntervalIntegrable B volume u v :=
      hg.mono_set (by simpa only [uIcc_of_le hab, uIcc_of_le huv] using hsub)
    calc
      ‖f v - f u‖ ≤ ∫ t in u..v, B t := by
        apply norm_sub_le_integral_of_norm_deriv_le_of_le huv
          (fun t ht => (hf t (hsub ht)).continuousAt.continuousWithinAt)
          (fun t ht => (hf t (hsub (Ioo_subset_Icc_self ht))).differentiableAt.differentiableWithinAt)
          _ hgi
        exact Filter.Eventually.of_forall (fun t ht => by
          rw [(hf t (hsub (Ioo_subset_Icc_self ht))).deriv]
          exact hbound t (hsub (Ioo_subset_Icc_self ht)))
      _ ≤ ∫ t in a..b, B t := intervalIntegral.integral_mono_interval hu.1 huv hv.2
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact (norm_nonneg (g t)).trans (hbound t (Ioc_subset_Icc_self ht))) hg
  rcases le_total y x with h | h
  · exact haux y x hy hx h
  · rw [norm_sub_rev]
    exact haux x y hx hy h

/-- A one-dimensional integral estimate gives uniform control on a line.
This is the precise good-line estimate required by LaTeX `thm:A` (b). -/
theorem norm_le_integral_norm_add_derivative_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {B : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (g t) t)
    (hg : IntervalIntegrable B volume a b)
    (hbound : ∀ t ∈ Icc a b, ‖g t‖ ≤ B t)
    {x : ℝ} (hx : x ∈ Icc a b) :
    ‖f x‖ ≤ (∫ t in a..b, ‖f t‖) / (b - a) + ∫ t in a..b, B t := by
  have hfc : ContinuousOn f (Icc a b) :=
    fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hfi : IntervalIntegrable (fun t => ‖f t‖) volume a b :=
    (show ContinuousOn (fun t => ‖f t‖) (uIcc a b) by
      rw [uIcc_of_le hab.le]
      exact hfc.norm).intervalIntegrable
  have hb (y : ℝ) (hy : y ∈ Icc a b) :
      ‖f x‖ ≤ ‖f y‖ + ∫ t in a..b, B t := by
    have hd := norm_sub_le_integral_derivative_bound_on_interval hf hg hbound hx hy
    calc
      ‖f x‖ = ‖(f x - f y) + f y‖ := by rw [sub_add_cancel]
      _ ≤ ‖f x - f y‖ + ‖f y‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hi := intervalIntegral.integral_mono_on hab.le
    (intervalIntegrable_const (c := ‖f x‖))
    (hfi.add (intervalIntegrable_const (c := ∫ t in a..b, B t))) hb
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_add hfi intervalIntegrable_const,
    intervalIntegral.integral_const] at hi
  simp only [smul_eq_mul] at hi
  have hmul := div_mul_cancel₀ (∫ t in a..b, ‖f t‖) (sub_pos.mpr hab).ne'
  nlinarith

theorem norm_sub_le_integral_norm_derivative_on_interval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (g t) t)
    (hg : IntervalIntegrable (fun t => ‖g t‖) volume a b)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖f x - f y‖ ≤ ∫ t in a..b, ‖g t‖ :=
  norm_sub_le_integral_derivative_bound_on_interval hf hg (fun _ _ => le_rfl) hx hy

theorem norm_le_integral_norm_add_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {a b : ℝ} (hab : a < b)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (g t) t)
    (hg : IntervalIntegrable (fun t => ‖g t‖) volume a b)
    {x : ℝ} (hx : x ∈ Icc a b) :
    ‖f x‖ ≤ (∫ t in a..b, ‖f t‖) / (b - a) + ∫ t in a..b, ‖g t‖ :=
  norm_le_integral_norm_add_derivative_bound hab hf hg (fun _ _ => le_rfl) hx
end ModifiedCartan
#print axioms ModifiedCartan.norm_sub_le_integral_derivative_bound_on_interval
#print axioms ModifiedCartan.norm_le_integral_norm_add_derivative_bound

