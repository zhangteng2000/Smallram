import ModifiedCartan.DiskMeanLimits
import ModifiedCartan.SubharmonicOrigin

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan.Paper

/-- LaTeX `eq:origin-bound`, for the actual normalized Euclidean norm
limit and its nonnegative subharmonic representative. -/
theorem eq_origin_bound {n : ℕ} (f : Curve n) (htrans : f.Transcendental)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) {H : ℕ → ℂ → ℂ} {e : ℕ → ℝ}
    (hH : ∀ᶠ ν in atTop, AnalyticOnNhd ℂ (H ν) (ball 0 64))
    (he : Tendsto e atTop (𝓝 0))
    (hmean : ∀ᶠ ν in atTop, ∀ R : ℝ, 0 < R → R < 64 →
      Real.circleAverage (fun z => (characteristic f (r ν))⁻¹ * Real.log (euclideanNorm
        (fun j => rescaledRepresentation f (r ν) (H ν) j z))) 0 R =
          characteristic f (R * r ν) / characteristic f (r ν) + e ν)
    {U : ℂ → EReal} {v : ℂ → ℝ}
    (hU : IsSubharmonicOn (ball (0 : ℂ) 4) U)
    (hrep : U =ᵐ[volume.restrict (ball (0 : ℂ) 4)] (fun z => (v z : EReal)))
    (hpos : ∀ z ∈ ball (0 : ℂ) 4, 0 ≤ U z)
    (hlim : LocalLpConvergence 1 (ball (0 : ℂ) 4)
      (fun ν z => (characteristic f (r ν))⁻¹ * Real.log (euclideanNorm
        (fun j => rescaledRepresentation f (r ν) (H ν) j z))) v) :
    U 0 = 0 ∧ ∀ ε : ℝ, 0 < ε → ε < ρ → ∃ C : ℝ, 0 < C ∧
      ∀ z ∈ ball (0 : ℂ) (1 / 4), 0 ≤ U z ∧ U z ≤ ((C * ‖z‖ ^ (ρ - ε) : ℝ) : EReal) := by
  have hh (ε : ℝ) (hε : 0 < ε) (hερ : ε < ρ) :
      U 0 = 0 ∧ ∃ C : ℝ, 0 < C ∧ ∀ z ∈ ball (0 : ℂ) (1 / 4),
        0 ≤ U z ∧ U z ≤ ((C * ‖z‖ ^ (ρ - ε) : ℝ) : EReal) := by
    obtain ⟨C, hC, hbound⟩ := arbitrary_norm_limit_disk_average_bound f htrans hρ hε hερ
      hl hu hr hH he hmean hlim
    have hb := subharmonic_origin_bound_of_disk_means hU hrep hpos
      (fun K hK hKU => memLp_one_iff_integrable.mp (hlim.limit_mem K hK hKU)) hC
      (sub_pos.mpr hερ) hbound
    exact ⟨hb.1, 4 * C * (2 : ℝ) ^ (ρ - ε), by positivity, hb.2⟩
  exact ⟨(hh (ρ / 2) (by positivity) (by linarith)).1, fun ε hε hερ => (hh ε hε hερ).2⟩

end ModifiedCartan.Paper
#print axioms ModifiedCartan.Paper.eq_origin_bound
