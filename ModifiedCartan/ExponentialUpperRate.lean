import ModifiedCartan.PowerExpPrimitive

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- Every exponential with strictly larger real rate dominates the function. -/
def HasExponentialUpperRate (H : ℝ) (f : ℝ → ℂ) : Prop :=
  ∀ a : ℝ, H < a → Tendsto (fun t => Real.exp (-a * t) * ‖f t‖) atTop (𝓝 0)

theorem HasExponentialUpperRate.congr {H : ℝ} {f g : ℝ → ℂ}
    (hf : HasExponentialUpperRate H f) (hfg : f =ᶠ[atTop] g) :
    HasExponentialUpperRate H g := by
  intro a ha
  apply (hf a ha).congr'
  filter_upwards [hfg] with t ht
  rw [ht]

theorem exp_weight_norm_profile_ratio {t : ℝ} (ht : 0 < t) (lam z : ℂ) (a b : ℝ) :
    Real.exp (-a * t) * ‖z‖ =
      (t ^ b * Real.exp (-(a - lam.re) * t)) * ‖z / powerExpProfile lam b t‖ := by
  rw [norm_div, powerExpProfile_norm ht, powerExpWeight]
  rw [show -(a - lam.re) * t = -a * t + lam.re * t by ring, Real.exp_add]
  have hp : t ^ b ≠ 0 := (Real.rpow_pos_of_pos ht b).ne'
  field_simp

/-- The actual normalized asymptotic controls every strictly larger exponential,
including when the normalized limit is zero. -/
theorem HasExponentialUpperRate.of_profile_limit {H b : ℝ} {lam c : ℂ} {f : ℝ → ℂ}
    (hlam : lam.re ≤ H)
    (hf : Tendsto (fun t => f t / powerExpProfile lam b t) atTop (𝓝 c)) :
    HasExponentialUpperRate H f := by
  intro a ha
  have hgap : 0 < a - lam.re := by linarith
  have hdec := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero b (a - lam.re) hgap
  have hh := hdec.mul hf.norm
  simp only [zero_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (exp_weight_norm_profile_ratio ht lam (f t) a b).symm

theorem HasExponentialUpperRate.const_mul {H : ℝ} {f : ℝ → ℂ}
    (hf : HasExponentialUpperRate H f) (c : ℂ) :
    HasExponentialUpperRate H (fun t => c * f t) := by
  intro a ha
  have hh := (hf a ha).const_mul ‖c‖
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [] with t
  rw [norm_mul]
  ring

theorem HasExponentialUpperRate.sum {ι : Type*} {H : ℝ} (s : Finset ι)
    {f : ι → ℝ → ℂ} (hf : ∀ i ∈ s, HasExponentialUpperRate H (f i)) :
    HasExponentialUpperRate H (fun t => ∑ i ∈ s, f i t) := by
  intro a ha
  have hlim : Tendsto (fun t => ∑ i ∈ s, Real.exp (-a * t) * ‖f i t‖) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum s (fun i hi => hf i hi a ha)
  apply squeeze_zero' (Eventually.of_forall (fun t => by positivity)) _ hlim
  exact Eventually.of_forall (fun t => by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (norm_sum_le s (fun i => f i t)) (Real.exp_pos _).le)

theorem HasExponentialUpperRate.real_power_mul {H : ℝ} {f : ℝ → ℂ}
    (hf : HasExponentialUpperRate H f) (b : ℝ) :
    HasExponentialUpperRate H (fun t => ((t ^ b : ℝ) : ℂ) * f t) := by
  intro a ha
  let A := (H + a) / 2
  have hHA : H < A := by dsimp [A]; linarith
  have hgap : 0 < a - A := by dsimp [A]; linarith
  have hdec := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero b (a - A) hgap
  have hh := hdec.mul (hf A hHA)
  simp only [zero_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]
  have he : Real.exp (-(a - A) * t) * Real.exp (-A * t) = Real.exp (-a * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    (t ^ b * Real.exp (-(a - A) * t)) * (Real.exp (-A * t) * ‖f t‖) =
        (Real.exp (-(a - A) * t) * Real.exp (-A * t)) * (t ^ b * ‖f t‖) := by ring
    _ = _ := by rw [he]

/-- Taking an actual primitive preserves every nonnegative exponential upper rate. -/
theorem HasExponentialUpperRate.primitive {H : ℝ} (hH : 0 ≤ H) {f f' : ℝ → ℂ}
    (hdf : ∀ᶠ t in atTop, HasDerivAt f (f' t) t)
    (hf : HasExponentialUpperRate H f') : HasExponentialUpperRate H f := by
  intro a ha
  have hap : 0 < a := lt_of_le_of_lt hH ha
  have hnorm (g : ℝ → ℂ) :
      (fun t : ℝ => ‖g t / powerExpProfile (a : ℂ) 0 t‖) =ᶠ[atTop]
        (fun t => Real.exp (-a * t) * ‖g t‖) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [norm_div, powerExpProfile_norm ht]
    simp only [powerExpWeight, Real.rpow_zero, one_mul, Complex.ofReal_re]
    rw [show -a * t = -(a * t) by ring, Real.exp_neg]
    ring
  have hrat : Tendsto (fun t => f' t / powerExpProfile (a : ℂ) 0 t) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr ((hf a ha).congr' (hnorm f').symm)
  have hl := powerExp_primitive_ratio_limit (show 0 < (a : ℂ).re from hap) hdf hrat
  simp only [zero_div] at hl
  have hh := hl.norm
  simp only [norm_zero] at hh
  exact hh.congr' (hnorm f)

/-- The normalization supplied by the constructed ray fundamental system. -/
theorem HasExponentialUpperRate.of_normalized_limit {H b : ℝ} {lam c : ℂ} {f : ℝ → ℂ}
    (hlam : lam.re ≤ H)
    (hf : Tendsto (fun t : ℝ => t ^ (-b) • (Complex.exp (-lam * (t : ℂ)) • f t))
      atTop (𝓝 c)) : HasExponentialUpperRate H f := by
  apply HasExponentialUpperRate.of_profile_limit hlam
  apply hf.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact powerExpProfile_normalization ht lam (f t) b
end ModifiedCartan
#print axioms ModifiedCartan.HasExponentialUpperRate.of_profile_limit
#print axioms ModifiedCartan.HasExponentialUpperRate.primitive

