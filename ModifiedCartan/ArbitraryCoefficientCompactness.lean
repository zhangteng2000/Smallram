import ModifiedCartan.ArbitraryScaleHypotheses
import ModifiedCartan.CurveCoordinateNormalization
import ModifiedCartan.RescaledRepresentation

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Relative compactness at every fixed scale in `eq:arbitrary-coefficients`,
with one bound independent of the scale and of every extracted subsequence. -/
theorem arbitrary_coefficient_relative_compactness {n : ℕ} (f : Curve n)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (hερ : ε < ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 0 < R →
      ∀ ι : ℕ → ℕ, StrictMono ι →
        ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ b : Fin n → ℂ → ℂ,
          ∀ i, AnalyticOnNhd ℂ (b i) (ball 0 4) ∧
            LocalMeasureConvergence (ball (0 : ℂ) 4)
              (fun ν z => (((R * r (ι (σ ν)) /
                (arbitraryScaleWeight ρ ε R * characteristic f (r (ι (σ ν))))) : ℝ) : ℂ) ^
                  (n + 1 - i.val) * canonicalCoefficient n f.coord i.castSucc
                    (((R * r (ι (σ ν))) : ℂ) * z)) (b i) ∧
              ∀ z ∈ ball (0 : ℂ) 1, ‖b i z‖ ≤ K := by
  obtain ⟨C, hC, hscale⟩ := characteristic_arbitrary_scale_hypotheses f htrans hsmall
    hρ hε hερ hl hu hr
  obtain ⟨g, hg0, hgT, hgN, hgQ, hglin, _, _, _⟩ := exists_normalized_curve f
  obtain ⟨K, hK, hrep⟩ := Paper.prop_representation n C hC
  refine ⟨K, hK, ?_⟩
  intro R hR ι hι
  obtain ⟨ht, hs, hlog, hT, hN⟩ := hscale R hR
  have hTg : ∀ᶠ ν in atTop, characteristic g (256 * (R * r ν)) ≤
      C * (arbitraryScaleWeight ρ ε R * characteristic f (r ν)) := by
    simpa only [hgT] using hT
  have hNg : Tendsto (fun ν => ValueDistribution.logCounting (FewInflection.wronskian n g.coord)
      (0 : WithTop ℂ) (256 * (R * r ν)) /
        (arbitraryScaleWeight ρ ε R * characteristic f (r ν))) atTop (𝓝 0) := by
    change Tendsto (fun ν => ramification g (256 * (R * r ν)) /
      (arbitraryScaleWeight ρ ε R * characteristic f (r ν))) atTop (𝓝 0)
    rw [hgN]
    exact hN
  obtain ⟨_, _, _, _, _, _, _, hc⟩ := hrep g (hglin.mpr hlin) hg0
    (fun ν => R * r ν) (fun ν => arbitraryScaleWeight ρ ε R * characteristic f (r ν))
      ht hs hlog hTg hNg
  obtain ⟨σ, hσ, b, hb⟩ := hc ι hι
  refine ⟨σ, hσ, b, ?_⟩
  intro i
  simpa only [hgQ, Complex.ofReal_mul] using hb i

end ModifiedCartan
#print axioms ModifiedCartan.arbitrary_coefficient_relative_compactness
