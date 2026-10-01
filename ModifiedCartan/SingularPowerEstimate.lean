import ModifiedCartan.CauchyTruncation
import Mathlib.Analysis.MeanInequalitiesPow

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

/-! Fractional integral estimates for the finite singular sums in
`eq:singular-logderivative` and `eq:higher-logderiv-measure`. -/

theorem norm_finsetSum_rpow_le {ι : Type*} (S : Finset ι) (v : ι → ℂ)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ‖∑ i ∈ S, v i‖ ^ α ≤ ∑ i ∈ S, ‖v i‖ ^ α := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Real.zero_rpow hα.ne']
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (Real.rpow_le_rpow (norm_nonneg _) (norm_add_le _ _) hα.le).trans
      ((Real.rpow_add_le_add_rpow (norm_nonneg _) (norm_nonneg _) hα.le hα1).trans
        (add_le_add le_rfl ih))

theorem norm_div_pow_rpow (w z : ℂ) (q : ℕ) (α : ℝ) :
    ‖w / z ^ q‖ ^ α = ‖w‖ ^ α * ‖z‖ ^ (-(q : ℝ) * α) := by
  rw [norm_div, norm_pow, Real.div_rpow (norm_nonneg _) (by positivity),
    ← Real.rpow_natCast_mul (norm_nonneg _) q α, div_eq_mul_inv,
    ← Real.rpow_neg (norm_nonneg _)]
  congr 2
  ring

theorem weighted_integer_rpow_le {α χ : ℝ} {m : ℤ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1) (hm : 0 ≤ m) :
    (χ * (m : ℝ)) ^ α ≤ (m : ℝ) := by
  by_cases hm0 : m = 0
  · simp [hm0, Real.zero_rpow hα.ne']
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ m by omega)
  exact (Real.rpow_le_rpow (by positivity) (mul_le_of_le_one_left (by positivity) hχ1)
    hα.le).trans (Real.rpow_le_self_of_one_le hm1 hα1)

theorem integral_norm_pole_rpow_le {K : Set ℂ} {a : ℂ} {R α : ℝ} {q : ℕ}
    (_hK : MeasurableSet K) (hKR : K ⊆ ball a R) (hR : 0 ≤ R)
    (hpow : (q : ℝ) * α < 2) :
    (∫ z in K, ‖(z - a)⁻¹ ^ q‖ ^ α) ≤
      (2 * Real.pi / (2 - (q : ℝ) * α)) * R ^ (2 - (q : ℝ) * α) := by
  have heq (z : ℂ) : ‖(z - a)⁻¹ ^ q‖ ^ α = ‖z - a‖ ^ (-((q : ℝ) * α)) := by
    rw [norm_pow, norm_inv, ← Real.rpow_natCast_mul (by positivity) q α,
      Real.inv_rpow (norm_nonneg _), ← Real.rpow_neg (norm_nonneg _)]
  simp_rw [heq]
  rw [← integral_shifted_norm_neg_rpow_exact hpow hR a]
  exact setIntegral_mono_set (integrableOn_shifted_norm_neg_rpow hpow a R)
    (Eventually.of_forall (fun _ => Real.rpow_nonneg (norm_nonneg _) _)) (Eventually.of_forall hKR)

theorem integral_norm_weighted_poles_rpow_le {ι : Type*} (S : Finset ι)
    (a w : ι → ℂ) {K : Set ℂ} (_hK : MeasurableSet K)
    {R α : ℝ} {q : ℕ} (hR : 0 ≤ R) (hα : 0 < α) (hα1 : α ≤ 1)
    (hpow : (q : ℝ) * α < 2) (hKR : ∀ i ∈ S, K ⊆ ball (a i) R) :
    (∫ z in K, ‖∑ i ∈ S, w i / (z - a i) ^ q‖ ^ α) ≤
      ((2 * Real.pi / (2 - (q : ℝ) * α)) * R ^ (2 - (q : ℝ) * α)) *
        ∑ i ∈ S, ‖w i‖ ^ α := by
  have hterm (i : ι) (hi : i ∈ S) :
      IntegrableOn (fun z => ‖w i / (z - a i) ^ q‖ ^ α) K := by
    simp_rw [norm_div_pow_rpow, neg_mul]
    exact ((integrableOn_shifted_norm_neg_rpow hpow (a i) R).mono_set (hKR i hi)).const_mul _
  have hsum : IntegrableOn (fun z => ∑ i ∈ S, ‖w i / (z - a i) ^ q‖ ^ α) K :=
    integrable_finsetSum S hterm
  have hbound (z : ℂ) := norm_finsetSum_rpow_le S (fun i => w i / (z - a i) ^ q) hα hα1
  have hmeas : Measurable (fun z => ∑ i ∈ S, w i / (z - a i) ^ q) := by
    apply Finset.measurable_fun_sum
    intro i _
    fun_prop
  have hint : IntegrableOn (fun z => ‖∑ i ∈ S, w i / (z - a i) ^ q‖ ^ α) K := by
    apply hsum.mono' (hmeas.norm.pow_const α).aestronglyMeasurable
    filter_upwards [] with z
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using hbound z
  calc
    _ ≤ ∫ z in K, ∑ i ∈ S, ‖w i / (z - a i) ^ q‖ ^ α := integral_mono hint hsum hbound
    _ = ∑ i ∈ S, ∫ z in K, ‖w i / (z - a i) ^ q‖ ^ α := integral_finsetSum S hterm
    _ ≤ ∑ i ∈ S, ‖w i‖ ^ α *
        ((2 * Real.pi / (2 - (q : ℝ) * α)) * R ^ (2 - (q : ℝ) * α)) := by
      apply Finset.sum_le_sum
      intro i hi
      simp_rw [norm_div_pow_rpow, neg_mul]
      rw [integral_const_mul]
      gcongr
      rw [← integral_shifted_norm_neg_rpow_exact hpow hR (a i)]
      exact setIntegral_mono_set (integrableOn_shifted_norm_neg_rpow hpow (a i) R)
        (Eventually.of_forall (fun _ => Real.rpow_nonneg (norm_nonneg _) _)) (Eventually.of_forall (hKR i hi))
    _ = _ := by rw [← Finset.sum_mul, mul_comm]


end ModifiedCartan

