import ModifiedCartan.SharpnessRayAE
import ModifiedCartan.RootIndicatorIntegral
import ModifiedCartan.SharpnessDomination
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open scoped Topology
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Dominated convergence for the actual prescribed entire coordinates,
with the exact root-indicator integral. LaTeX `eq:sharpness-asymptotic`. -/
theorem IsSharpnessSystem.characteristic_power_limit {n k q : ℕ}
    {g : Index n → ℂ → ℂ} (h : IsSharpnessSystem n k q g)
    (hq : 2 ≤ q) (hqn : q ≤ n + 1) :
    Tendsto (fun r : ℝ => characteristic (h.curve hq hqn) r / r ^ (1 + (k : ℝ) / q))
      atTop (𝓝 ((q : ℝ) * Real.sin (Real.pi / q) /
        (Real.pi * (1 + (k : ℝ) / q)))) := by
  let f := h.curve hq hqn
  let ρ : ℝ := 1 + (k : ℝ) / q
  let H : ℝ → ℝ := fun θ => sharpnessRootIndicator q (by omega) (ρ * θ) / ρ
  let L : ℝ → ℝ → ℝ := fun r θ => Real.log (euclideanNorm (f.vector (circleMap 0 r θ))) / r ^ ρ
  have hρ : 0 < ρ := sharpness_rho_pos q k
  obtain ⟨C, _hC, hdom⟩ := h.abs_log_vector_norm_le hq hqn
  have hmeas : ∀ᶠ r in atTop, AEStronglyMeasurable (L r) (volume.restrict (uIoc 0 (2 * Real.pi))) := by
    apply Eventually.of_forall
    intro r
    exact (((curve_log_euclideanNorm_continuous f).comp (continuous_circleMap 0 r)).div_const (r ^ ρ)).aestronglyMeasurable
  have hbound : ∀ᶠ r in atTop, ∀ᵐ θ : ℝ, θ ∈ uIoc 0 (2 * Real.pi) → ‖L r θ‖ ≤ C := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    apply Eventually.of_forall
    intro θ _
    have hrp : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hz : ‖circleMap 0 r θ‖ ≤ r := by rw [norm_circleMap_zero, abs_of_pos hrp]
    have hb := hdom r hr (circleMap 0 r θ) hz
    have hp : 0 < r ^ ρ := Real.rpow_pos_of_pos hrp ρ
    change ‖Real.log (euclideanNorm (fun j => g j (circleMap 0 r θ))) / r ^ ρ‖ ≤ C
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hp]
    exact (div_le_iff₀ hp).mpr hb
  have hl : ∀ᵐ θ : ℝ, θ ∈ uIoc 0 (2 * Real.pi) → Tendsto (fun r => L r θ) atTop (𝓝 (H θ)) := by
    filter_upwards [h.ae_ray_log_limit hq hqn] with θ hθ _
    change Tendsto (fun r : ℝ => Real.log (euclideanNorm (fun j => g j (circleMap 0 r θ))) / r ^ ρ)
      atTop (𝓝 (H θ))
    simpa only [circleMap_zero, rayPhase] using hθ
  have hint := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => C) hmeas hbound intervalIntegrable_const hl
  have hmean := hint.const_mul ((2 * Real.pi)⁻¹)
  have hval : (2 * Real.pi)⁻¹ * (∫ θ in 0..2 * Real.pi, H θ) =
      (q : ℝ) * Real.sin (Real.pi / q) / (Real.pi * ρ) := sharpness_indicator_average (by omega) k
  rw [hval] at hmean
  have hconst : Tendsto (fun r : ℝ => Real.log (euclideanNorm (f.vector 0)) / r ^ ρ) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rpow_atTop hρ)
  have hh := hmean.sub hconst
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [] with r
  change (2 * Real.pi)⁻¹ * (∫ θ in 0..2 * Real.pi,
    Real.log (euclideanNorm (f.vector (circleMap 0 r θ))) / r ^ ρ) -
      Real.log (euclideanNorm (f.vector 0)) / r ^ ρ = characteristic f r / r ^ ρ
  rw [intervalIntegral.integral_div, characteristic, Real.circleAverage_def, smul_eq_mul]
  ring

theorem sharpness_asymptotic_constant_pos {q : ℕ} (hq : 2 ≤ q) (k : ℕ) :
    0 < (q : ℝ) * Real.sin (Real.pi / q) / (Real.pi * (1 + (k : ℝ) / q)) := by
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hqone : (1 : ℝ) < q := by exact_mod_cast hq
  have hs : 0 < Real.sin (Real.pi / q) := Real.sin_pos_of_pos_of_lt_pi
    (div_pos Real.pi_pos hqpos) ((div_lt_iff₀ hqpos).mpr (by nlinarith [Real.pi_pos]))
  exact div_pos (mul_pos hqpos hs) (mul_pos Real.pi_pos (sharpness_rho_pos q k))

end ModifiedCartan
#print axioms ModifiedCartan.IsSharpnessSystem.characteristic_power_limit
