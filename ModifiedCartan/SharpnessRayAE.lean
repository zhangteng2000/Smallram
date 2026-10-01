import ModifiedCartan.SharpnessRootIndicator
import ModifiedCartan.SharpnessRayLimit

open scoped Topology
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- LaTeX `eq:sharpness-ray-limit`: the exact ray limit for the prescribed
system holds almost everywhere, with every spectral condition discharged. -/
theorem IsSharpnessSystem.ae_ray_log_limit {n k q : ℕ} {g : Index n → ℂ → ℂ}
    (h : IsSharpnessSystem n k q g) (hq : 2 ≤ q) (hqn : q ≤ n + 1) :
    ∀ᵐ θ : ℝ, Tendsto (fun r : ℝ =>
      Real.log (euclideanNorm (fun j => g j ((r : ℂ) * rayPhase θ))) / r ^ (1 + (k : ℝ) / q))
      atTop (𝓝 (sharpnessRootIndicator q (by omega) ((1 + (k : ℝ) / q) * θ) /
        (1 + (k : ℝ) / q))) := by
  let ρ : ℝ := 1 + (k : ℝ) / q
  let β : ℝ := (k : ℝ) / q
  have hρ : 0 < ρ := sharpness_rho_pos q k
  have hq1 : 1 ≤ q := by omega
  have hb : β * (q : ℝ) = k := sharpness_beta_balance hq1 k
  filter_upwards [sharpnessRootIndicator_ae_pos hq hρ.ne'] with θ hθ
  obtain ⟨j, hj⟩ := sharpnessRootIndicator_attained hq1 (ρ * θ)
  let δ := rayPhase (β * θ)
  let η := rayPhase θ
  have hs (i : Fin q) : raySpectralValues q δ η i = rayPhase (ρ * θ) * sharpnessRoot q i := by
    unfold raySpectralValues
    change (rayPhase θ * rayPhase (β * θ)) * sharpnessRoot q i = _
    rw [rayPhases_product (show ρ = 1 + β from rfl)]
  have hp : 0 < (raySpectralValues q δ η j).re := by rw [hs, ← hj]; exact hθ
  have hm (i : Fin q) : (raySpectralValues q δ η i).re ≤ (raySpectralValues q δ η j).re := by
    rw [hs, hs, ← hj]
    exact sharpnessRootIndicator_le hq1 (ρ * θ) i
  have hl := h.ray_radius_log_limit_of_maximal_positive_mode hq hqn hρ rfl hb
    (rayPhase_ne_zero (β * θ)) (rayPhase_ne_zero θ) (rayPhases_power_balance hb θ) j hp hm
  rw [hs, ← hj] at hl
  exact hl

end ModifiedCartan
#print axioms ModifiedCartan.IsSharpnessSystem.ae_ray_log_limit
