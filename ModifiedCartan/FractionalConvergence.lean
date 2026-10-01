import ModifiedCartan.SingularPowerEstimate
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

/-! Fractional integral convergence and vanishing of normalized finite pole sums,
the singular part of `eq:higher-logderiv-measure`. -/

theorem integrableOn_weighted_poles_rpow {ι : Type*} (S : Finset ι) (a w : ι → ℂ)
    {K : Set ℂ} {R α : ℝ} {q : ℕ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hpow : (q : ℝ) * α < 2) (hKR : ∀ i ∈ S, K ⊆ ball (a i) R) :
    IntegrableOn (fun z => ‖∑ i ∈ S, w i / (z - a i) ^ q‖ ^ α) K := by
  have hterm (i : ι) (hi : i ∈ S) :
      IntegrableOn (fun z => ‖w i / (z - a i) ^ q‖ ^ α) K := by
    simp_rw [norm_div_pow_rpow, neg_mul]
    exact ((integrableOn_shifted_norm_neg_rpow hpow (a i) R).mono_set (hKR i hi)).const_mul _
  have hmeas : Measurable (fun z => ∑ i ∈ S, w i / (z - a i) ^ q) := by
    apply Finset.measurable_fun_sum
    intro i _
    fun_prop
  apply (integrable_finsetSum S hterm).mono' (hmeas.norm.pow_const α).aestronglyMeasurable
  filter_upwards [] with z
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using
    norm_finsetSum_rpow_le S (fun i => w i / (z - a i) ^ q) hα hα1

theorem tendstoInMeasure_zero_of_integral_norm_rpow
    {A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E]
    {μ : Measure A} [IsFiniteMeasure μ] {f : ℕ → A → E} {α : ℝ} (hα : 0 < α)
    (hf : ∀ n, Integrable (fun x => ‖f n x‖ ^ α) μ)
    (hlim : Tendsto (fun n => ∫ x, ‖f n x‖ ^ α ∂μ) atTop (𝓝 0)) :
    TendstoInMeasure μ f atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  simp only [sub_zero]
  have hb (n : ℕ) : μ.real {x | ε ≤ ‖f n x‖} ≤ (∫ x, ‖f n x‖ ^ α ∂μ) / ε ^ α := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hε α)).mpr
    have heq : {x | ε ^ α ≤ ‖f n x‖ ^ α} = {x | ε ≤ ‖f n x‖} := by
      ext x
      exact Real.rpow_le_rpow_iff hε.le (norm_nonneg _) hα
    simpa only [heq, mul_comm] using mul_meas_ge_le_integral_of_nonneg
      (Eventually.of_forall (fun x => Real.rpow_nonneg (norm_nonneg (f n x)) α)) (hf n) (ε ^ α)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_div] using hlim.div_const (ε ^ α)) (fun _ => measureReal_nonneg) hb

theorem integral_normalized_weighted_poles_rpow_le {ι : Type*} (S : Finset ι)
    (a w : ι → ℂ) {K : Set ℂ} (hK : MeasurableSet K)
    {R α t M : ℝ} {q : ℕ} (hR : 0 ≤ R) (hα : 0 < α) (hα1 : α ≤ 1)
    (ht : 0 < t) (hpow : (q : ℝ) * α < 2) (hKR : ∀ i ∈ S, K ⊆ ball (a i) R)
    (hmass : ∑ i ∈ S, ‖w i‖ ^ α ≤ t * M) :
    (∫ z in K, ‖(∑ i ∈ S, w i / (z - a i) ^ q) / (t : ℂ) ^ q‖ ^ α) ≤
      ((2 * Real.pi / (2 - (q : ℝ) * α)) * R ^ (2 - (q : ℝ) * α)) *
        M * t ^ (1 - (q : ℝ) * α) := by
  have hC : 0 ≤ ((2 * Real.pi / (2 - (q : ℝ) * α)) * R ^ (2 - (q : ℝ) * α)) := by positivity
  simp_rw [norm_div_pow_rpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, neg_mul]
  rw [integral_mul_const]
  calc
    _ ≤ (((2 * Real.pi / (2 - (q : ℝ) * α)) * R ^ (2 - (q : ℝ) * α)) *
        ∑ i ∈ S, ‖w i‖ ^ α) * t ^ (-((q : ℝ) * α)) :=
      mul_le_mul_of_nonneg_right
        (integral_norm_weighted_poles_rpow_le S a w hK hR hα hα1 hpow hKR)
        (Real.rpow_nonneg ht.le _)
    _ ≤ (((2 * Real.pi / (2 - (q : ℝ) * α)) * R ^ (2 - (q : ℝ) * α)) *
        (t * M)) * t ^ (-((q : ℝ) * α)) := by gcongr
    _ = _ := by
      rw [show 1 - (q : ℝ) * α = 1 + (-((q : ℝ) * α)) by ring, Real.rpow_add ht, Real.rpow_one]
      ring

theorem normalized_weighted_poles_tendstoInMeasure {ι : Type*}
    (S : ℕ → Finset ι) (a w : ℕ → ι → ℂ) {K : Set ℂ} (hK : IsCompact K)
    {R α M : ℝ} {q : ℕ} {s : ℕ → ℝ} (hR : 0 ≤ R)
    (hα : 0 < α) (hα1 : α ≤ 1) (hqα : 1 < (q : ℝ) * α) (hpow : (q : ℝ) * α < 2)
    (hs0 : ∀ n, 0 < s n) (hs : Tendsto s atTop atTop)
    (hKR : ∀ n i, i ∈ S n → K ⊆ ball (a n i) R)
    (hmass : ∀ n, ∑ i ∈ S n, ‖w n i‖ ^ α ≤ s n * M) :
    TendstoInMeasure (volume.restrict K)
      (fun n z => (∑ i ∈ S n, w n i / (z - a n i) ^ q) / (s n : ℂ) ^ q)
      atTop (fun _ => 0) := by
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  apply tendstoInMeasure_zero_of_integral_norm_rpow hα
  · intro n
    simp_rw [norm_div_pow_rpow]
    exact (integrableOn_weighted_poles_rpow (S n) (a n) (w n) hα hα1 hpow (hKR n)).mul_const _
  · have hlim : Tendsto (fun n => s n ^ (1 - (q : ℝ) * α)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, neg_sub] using
        (tendsto_rpow_neg_atTop (sub_pos.mpr hqα)).comp hs
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [mul_zero] using
        (hlim.const_mul (((2 * Real.pi / (2 - (q : ℝ) * α)) * R ^ (2 - (q : ℝ) * α)) * M)))
    · intro n
      exact integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    · intro n
      exact integral_normalized_weighted_poles_rpow_le (S n) (a n) (w n) hK.measurableSet
        hR hα hα1 (hs0 n) hpow (hKR n) (hmass n)


end ModifiedCartan

