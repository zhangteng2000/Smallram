import ModifiedCartan.EnvelopeConstantLimit
import ModifiedCartan.EnvelopeIntegration

open scoped Topology
open Filter Set MeasureTheory Asymptotics
set_option autoImplicit false
namespace ModifiedCartan.Paper

/-- LaTeX `lem:envelope`, including finiteness of the literal integral
constant, its limit at zero, and integrability at the constructed radii.
All hypotheses are exactly those of the submitted lemma. -/
theorem lem_envelope {H : ℝ → ℝ} {α : ℝ}
    (hH : ContinuousOn H (Ioi 0)) (hn : ∀ t, 0 < t → 0 ≤ H t)
    (hm : MonotoneOn H (Ioi 0)) (hp : ∀ᶠ t in atTop, 0 < H t)
    (hα : 0 < α) (hα1 : α < 1)
    (ho : H =o[atTop] (fun t => t ^ α)) :
    IntegrableOn (envelopeIntegrand α) (Ioi 0) ∧
      Tendsto envelopeConstant (𝓝[>] 0) (𝓝 1) ∧
      ∃ r : ℕ → ℝ, (∀ ν, 0 < r ν) ∧ Tendsto r atTop atTop ∧
        (∀ ν, 0 < H (r ν)) ∧ ∀ ν,
          IntegrableOn (fun t => H (3 * t) / (r ν + t) ^ 2) (Ioi 0) ∧
          r ν * (∫ t in Ioi 0, H (3 * t) / (r ν + t) ^ 2) ≤
            envelopeConstant α * H (r ν) := by
  obtain ⟨r, hr, ht, hpos, hb⟩ := exists_power_envelope_sequence hH hm hp ho
  exact ⟨envelope_integrand_integrable hα.le hα1, envelopeConstant_tendsto_one,
    r, hr, ht, hpos, fun ν => integral_envelope_at_radius (hr ν) hα.le hα1 hH hn (hb ν)⟩

end ModifiedCartan.Paper
#print axioms ModifiedCartan.Paper.lem_envelope
