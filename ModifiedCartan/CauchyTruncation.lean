import ModifiedCartan.CauchyKernel

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric

namespace ModifiedCartan

/-! Explicit planar singular integrals and the finite-atomic part of
`eq:kernel-truncation-bound` in the proof of `lem:logderivlimit`.
General Riesz measures and the convergence theorem require further proofs. -/

theorem radial_integral_ball (f : ℝ → ℝ) (R : ℝ) :
    (∫ z : ℂ in ball 0 R, f ‖z‖) =
      2 * Real.pi * ∫ r in Ioo 0 R, r * f r := by
  have h := integral_fun_norm_addHaar (volume : Measure ℂ) ((Iio R).indicator f)
  have hl : (fun z : ℂ => (Iio R).indicator f ‖z‖) =
      (ball 0 R).indicator (fun z : ℂ => f ‖z‖) := by
    funext z
    simp only [indicator, mem_Iio, mem_ball, dist_zero_right]
  have hr : (fun r : ℝ => r ^ (Module.finrank ℝ ℂ - 1) • (Iio R).indicator f r) =
      (Iio R).indicator (fun r : ℝ => r * f r) := by
    funext r
    simp only [Complex.finrank_real_complex, Nat.reduceSub, pow_one, smul_eq_mul,
      indicator, mul_ite, mul_zero]
  rw [hl, integral_indicator measurableSet_ball, hr, integral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio] at h
  have hset : Iio R ∩ Ioi (0 : ℝ) = Ioo 0 R := by ext r; simp only [mem_inter_iff,
    mem_Iio, mem_Ioi, mem_Ioo, and_comm]
  have hvol : volume.real (ball (0 : ℂ) 1) = Real.pi := by
    simp [Measure.real, Complex.volume_ball]
  simpa only [hset, Complex.finrank_real_complex, hvol, smul_eq_mul, nsmul_eq_mul,
    Nat.cast_ofNat, mul_assoc] using h

theorem integral_norm_neg_rpow {p R : ℝ} (hp : p < 2) (hR : 0 ≤ R) :
    (∫ z : ℂ in ball 0 R, ‖z‖ ^ (-p)) =
      (2 * Real.pi / (2 - p)) * R ^ (2 - p) := by
  rw [radial_integral_ball (fun r : ℝ => r ^ (-p)) R]
  have heq : (∫ r in Ioo 0 R, r * r ^ (-p)) = ∫ r in Ioo 0 R, r ^ (1 - p) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    calc
      r * r ^ (-p) = r ^ (1 : ℝ) * r ^ (-p) := by rw [Real.rpow_one]
      _ = r ^ (1 - p) := by rw [← Real.rpow_add hr.1]; rfl
  rw [heq, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR,
    integral_rpow (Or.inl (by linarith : -1 < 1 - p)),
    show 1 - p + 1 = 2 - p by ring,
    Real.zero_rpow (by linarith : 2 - p ≠ 0), sub_zero]
  ring

theorem integral_shifted_norm_neg_rpow_exact {p R : ℝ} (hp : p < 2) (hR : 0 ≤ R)
    (a : ℂ) :
    (∫ z in ball a R, ‖z - a‖ ^ (-p)) =
      (2 * Real.pi / (2 - p)) * R ^ (2 - p) := by
  rw [integral_shifted_norm_neg_rpow, integral_norm_neg_rpow hp hR]

noncomputable def nearCauchyKernel (R : ℝ) (a : ℂ) : ℂ → ℂ :=
  (ball a R).indicator (fun z => (z - a)⁻¹)

theorem memLp_nearCauchyKernel {p : ℝ} (hp0 : 0 < p) (hp2 : p < 2) (R : ℝ) (a : ℂ) :
    MemLp (nearCauchyKernel R a) (ENNReal.ofReal p) volume := by
  exact (memLp_indicator_iff_restrict measurableSet_ball).mpr (memLp_cauchyKernel hp0 hp2 a R)

theorem eLpNorm_nearCauchyKernel {p R : ℝ} (hp0 : 0 < p) (hp2 : p < 2)
    (hR : 0 ≤ R) (a : ℂ) :
    eLpNorm (nearCauchyKernel R a) (ENNReal.ofReal p) volume =
      ENNReal.ofReal (((2 * Real.pi / (2 - p)) * R ^ (2 - p)) ^ p⁻¹) := by
  rw [nearCauchyKernel, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball,
    MemLp.eLpNorm_eq_integral_rpow_norm (by simpa using hp0) ENNReal.ofReal_ne_top
      (memLp_cauchyKernel hp0 hp2 a R)]
  simp only [ENNReal.toReal_ofReal hp0.le, norm_inv, Real.inv_rpow (norm_nonneg _),
    ← Real.rpow_neg (norm_nonneg _), integral_shifted_norm_neg_rpow_exact hp2 hR]

theorem eLpNorm_sum_nearCauchyKernel_le {ι : Type*} (s : Finset ι) (a c : ι → ℂ)
    {p R : ℝ} (hp1 : 1 ≤ p) (hp2 : p < 2) (hR : 0 ≤ R) (K : Set ℂ) :
    eLpNorm (fun z => ∑ i ∈ s, c i * nearCauchyKernel R (a i) z)
        (ENNReal.ofReal p) (volume.restrict K) ≤
      (∑ i ∈ s, ‖c i‖ₑ) *
        ENNReal.ofReal (((2 * Real.pi / (2 - p)) * R ^ (2 - p)) ^ p⁻¹) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  have hmeas : ∀ i ∈ s, AEStronglyMeasurable (c i • nearCauchyKernel R (a i))
      (volume.restrict K) := by
    intro i _
    have hint := ((memLp_nearCauchyKernel hp0 hp2 R (a i)).const_smul (c i)).mono_measure
      (Measure.restrict_le_self (s := K))
    exact hint.aestronglyMeasurable
  have hsum : (fun z => ∑ i ∈ s, c i * nearCauchyKernel R (a i) z) =
      ∑ i ∈ s, c i • nearCauchyKernel R (a i) := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    _ ≤ ∑ i ∈ s, eLpNorm (c i • nearCauchyKernel R (a i))
        (ENNReal.ofReal p) (volume.restrict K) := by
      rw [hsum]
      exact eLpNorm_sum_le hmeas (ENNReal.one_le_ofReal.mpr hp1)
    _ ≤ _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      rw [eLpNorm_const_smul]
      have hle := (eLpNorm_mono_measure (nearCauchyKernel R (a i))
        (p := ENNReal.ofReal p) (μ := volume) (ν := volume.restrict K)
        Measure.restrict_le_self).trans_eq
        (eLpNorm_nearCauchyKernel hp0 hp2 hR (a i))
      gcongr

theorem cauchy_truncation_bound_tendsto_zero {p : ℝ} (hp0 : 0 < p) (hp2 : p < 2) :
    Tendsto (fun R : ℝ =>
      ENNReal.ofReal (((2 * Real.pi / (2 - p)) * R ^ (2 - p)) ^ p⁻¹))
      (𝓝 0) (𝓝 0) := by
  have hpow : Tendsto (fun R : ℝ => R ^ (2 - p)) (𝓝 0) (𝓝 0) :=
    tendsto_id.rpow_const_nhds_zero (by linarith)
  have hmul : Tendsto (fun R : ℝ => (2 * Real.pi / (2 - p)) * R ^ (2 - p))
      (𝓝 0) (𝓝 0) := by
    simpa only [mul_zero] using hpow.const_mul (2 * Real.pi / (2 - p))
  simpa only [ENNReal.ofReal_zero] using
    ENNReal.tendsto_ofReal (hmul.rpow_const_nhds_zero (inv_pos.mpr hp0))

theorem uniform_cauchy_truncation {ι : Type*} (s : ℕ → Finset ι) (a c : ℕ → ι → ℂ)
    {p M : ℝ} (hp1 : 1 ≤ p) (hp2 : p < 2)
    (hM : ∀ ν, ∑ i ∈ s ν, ‖c ν i‖ₑ ≤ ENNReal.ofReal M) (K : Set ℂ) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ R : ℝ, 0 ≤ R → R < δ → ∀ ν,
      eLpNorm (fun z => ∑ i ∈ s ν, c ν i * nearCauchyKernel R (a ν i) z)
        (ENNReal.ofReal p) (volume.restrict K) < ε := by
  intro ε hε
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  have hlim : Tendsto (fun R : ℝ => ENNReal.ofReal M *
      ENNReal.ofReal (((2 * Real.pi / (2 - p)) * R ^ (2 - p)) ^ p⁻¹))
      (𝓝 0) (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul
      (cauchy_truncation_bound_tendsto_zero hp0 hp2)
      (Or.inr ENNReal.ofReal_ne_top : (0 : ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal M ≠ ⊤)
  obtain ⟨δ, hδ, hsmall⟩ := Metric.eventually_nhds_iff_ball.mp (hlim.eventually_lt_const hε)
  refine ⟨δ, hδ, ?_⟩
  intro R hR hRδ ν
  have hnear : R ∈ ball (0 : ℝ) δ := by
    simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hR] using hRδ
  apply lt_of_le_of_lt (eLpNorm_sum_nearCauchyKernel_le (s ν) (a ν) (c ν) hp1 hp2 hR K)
  apply lt_of_le_of_lt _ (hsmall R hnear)
  gcongr
  exact hM ν

end ModifiedCartan


