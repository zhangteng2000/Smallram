import ModifiedCartan.CharacteristicPeaks
import ModifiedCartan.CurveCoordinateNormalization
import ModifiedCartan.RescaledRepresentation

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- The compactness assertion actually needed at each positive peak scale
in Step 1 of `prop:indices`. The bound is independent of R and the original
curve need not have nonzero coordinates at the origin. -/
theorem peak_coefficient_relative_compactness {n : ℕ} (f : Curve n)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {r ε : ℕ → ℝ} {μ : ℝ} (hμ : 0 < μ)
    (hrpos : ∀ ν, 0 < r ν) (hr : Tendsto r atTop atTop)
    (hεpos : ∀ ν, 0 < ε ν) (hε : Tendsto ε atTop (𝓝 0))
    (hpeak : ∀ ν t, ε ν ≤ t → t ≤ (ε ν)⁻¹ →
      characteristic f (t * r ν) ≤ (1 + ε ν) * t ^ μ * characteristic f (r ν)) :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 0 < R →
      ∀ ρ : ℕ → ℕ, StrictMono ρ →
        ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ b : Fin n → ℂ → ℂ,
          ∀ i, AnalyticOnNhd ℂ (b i) (ball 0 4) ∧
            LocalMeasureConvergence (ball (0 : ℂ) 4)
              (fun ν z => (((R * r (ρ (σ ν)) /
                (R ^ μ * characteristic f (r (ρ (σ ν))))) : ℝ) : ℂ) ^ (n + 1 - i.val) *
                canonicalCoefficient n f.coord i.castSucc (((R * r (ρ (σ ν))) : ℂ) * z))
              (b i) ∧ ∀ z ∈ ball (0 : ℂ) 1, ‖b i z‖ ≤ K := by
  obtain ⟨g, hg0, hgT, hgN, hgQ, hglin, _, _, _⟩ := exists_normalized_curve f
  obtain ⟨K, hK, hrep⟩ := Paper.prop_representation n (2 * (256 : ℝ) ^ μ) (by positivity)
  refine ⟨K, hK, ?_⟩
  intro R hR ρ hρ
  obtain ⟨ht, hs, hlog, hT, hN⟩ := characteristic_peak_scale_hypotheses f htrans hsmall
    hμ hrpos hr hεpos hε hpeak hR
  have hTg : ∀ᶠ ν in atTop, characteristic g (256 * (R * r ν)) ≤
      (2 * (256 : ℝ) ^ μ) * (R ^ μ * characteristic f (r ν)) := by
    simpa only [hgT] using hT
  have hNg : Tendsto (fun ν => ValueDistribution.logCounting (FewInflection.wronskian n g.coord)
      (0 : WithTop ℂ) (256 * (R * r ν)) / (R ^ μ * characteristic f (r ν)))
      atTop (𝓝 0) := by
    change Tendsto (fun ν => ramification g (256 * (R * r ν)) /
      (R ^ μ * characteristic f (r ν))) atTop (𝓝 0)
    rw [hgN]
    exact hN
  obtain ⟨_, _, _, _, _, _, _, hc⟩ := hrep g (hglin.mpr hlin) hg0
    (fun ν => R * r ν) (fun ν => R ^ μ * characteristic f (r ν)) ht hs hlog hTg hNg
  obtain ⟨σ, hσ, b, hb⟩ := hc ρ hρ
  refine ⟨σ, hσ, b, ?_⟩
  intro i
  simpa only [hgQ, Complex.ofReal_mul] using hb i

end
end ModifiedCartan
#print axioms ModifiedCartan.peak_coefficient_relative_compactness
