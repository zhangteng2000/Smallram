import ModifiedCartan.InversePullbackConvergence
import ModifiedCartan.InversePullbackAE
import ModifiedCartan.LogLimitRepresentatives
import ModifiedCartan.FirstLogDerivLimit
import ModifiedCartan.LocalMeasureUniqueness
import ModifiedCartan.SubharmonicLocalConvexity

open scoped Topology ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem analytic_comp_nontrivial_of_inverse {U G : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hG : IsOpen G) (hGn : G.Nonempty)
    {f ψ φ : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (hn : ∃ z ∈ U, f z ≠ 0)
    (hψU : MapsTo ψ G U) (hinv : ∀ z ∈ G, φ (ψ z) = z)
    (hφ : DifferentiableOn ℝ φ (ψ '' G)) : ∃ z ∈ G, (f ∘ ψ) z ≠ 0 := by
  exact Measure.exists_mem_of_measure_ne_zero_of_ae (hG.measure_ne_zero volume hGn)
    (ae_comp_of_differentiable_inverse hU.measurableSet hG.measurableSet hψU hinv hφ
      (analytic_ae_ne_zero hU hUc hf hn))

/-- Subharmonicity of the actual continuous pullback is obtained from the
actual composed holomorphic logarithms and the proved local L1 compactness theorem. -/
theorem normalizedLog_inverse_pullback_subharmonic {U G : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hG : IsOpen G)
    (hGc : IsPreconnected G) (hGn : G.Nonempty)
    {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {v : ℂ → ℝ}
    (hf : ∀ ν, AnalyticOnNhd ℂ (f ν) U) (hn : ∀ ν, ∃ z ∈ U, f ν z ≠ 0)
    (hs : ∀ ν, 0 < s ν)
    (hlim : LocalLpConvergence 1 U (fun ν z => (s ν)⁻¹ * Real.log ‖f ν z‖) v)
    (hv : ContinuousOn v U) {ψ φ : ℂ → ℂ} (hψ : AnalyticOnNhd ℂ ψ G)
    (hψU : MapsTo ψ G U) (hinv : ∀ z ∈ G, φ (ψ z) = z)
    {D : ℂ → ℂ →L[ℝ] ℂ}
    (hD : ∀ z ∈ ψ '' G, HasFDerivWithinAt φ (D z) (ψ '' G) z)
    (hDc : ContinuousOn (fun z => |(D z).det|) (ψ '' G)) :
    IsSubharmonicOn G (fun z => (v (ψ z) : EReal)) := by
  have hc := hlim.comp_inverse hψ.continuousOn hψU hinv hD hDc
  have hnc (ν : ℕ) : ∃ z ∈ G, (f ν ∘ ψ) z ≠ 0 :=
    analytic_comp_nontrivial_of_inverse hU hUc hG hGn (hf ν) (hn ν)
      hψU hinv (fun z hz => (hD z hz).differentiableWithinAt)
  obtain ⟨u, hu, _, hrep, _⟩ := normalizedLog_limit_subharmonic_representative
    hG hGc hGn (fun ν => (hf ν).comp hψ hψU) hnc hs hc
  exact hu.congr_on (hu.eqOn_of_ae_eq_continuous hG (hv.comp hψ.continuousOn hψU) hrep)

/-- The weak chain rule needed for `prop:homogeneity` is proved by uniqueness
of the actual first logarithmic derivative limits after change of variables. -/
theorem normalizedLog_inverse_pullback_gradient {U G : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hG : IsOpen G)
    (hGc : IsPreconnected G) (hGn : G.Nonempty)
    {f : ℕ → ℂ → ℂ} {s : ℕ → ℝ} {v : ℂ → ℝ} {g : ℂ → ℂ}
    (hf : ∀ ν, AnalyticOnNhd ℂ (f ν) U) (hn : ∀ ν, ∃ z ∈ U, f ν z ≠ 0)
    (hs : Tendsto s atTop atTop)
    (hlim : LocalLpConvergence 1 U (fun ν z => (s ν)⁻¹ * Real.log ‖f ν z‖) v)
    (hg : HasWeakComplexGradient U v g)
    {ψ φ : ℂ → ℂ} (hψ : AnalyticOnNhd ℂ ψ G)
    (hψU : MapsTo ψ G U) (hinv : ∀ z ∈ G, φ (ψ z) = z)
    {D : ℂ → ℂ →L[ℝ] ℂ}
    (hD : ∀ z ∈ ψ '' G, HasFDerivWithinAt φ (D z) (ψ '' G) z)
    (hDc : ContinuousOn (fun z => |(D z).det|) (ψ '' G)) :
    ∃ H : ℂ → ℂ, HasWeakComplexGradient G (fun z => v (ψ z)) H ∧
      H =ᵐ[volume.restrict G] (fun z => deriv ψ z * g (ψ z)) := by
  have hc := hlim.comp_inverse hψ.continuousOn hψU hinv hD hDc
  have hfc (ν : ℕ) : AnalyticOnNhd ℂ (f ν ∘ ψ) G := (hf ν).comp hψ hψU
  have hnc (ν : ℕ) : ∃ z ∈ G, (f ν ∘ ψ) z ≠ 0 :=
    analytic_comp_nontrivial_of_inverse hU hUc hG hGn (hf ν) (hn ν)
      hψU hinv (fun z hz => (hD z hz).differentiableWithinAt)
  obtain ⟨H, hH, _⟩ := hc.log_limit_weak_gradient hG hGc hfc hnc hs
  have hgl : LocalLpConvergence 1 U (fun ν z => (s ν)⁻¹ • logDeriv (f ν) z) g := by
    simpa only [ENNReal.ofReal_one] using!
      hlim.logDeriv_localLpConvergence hU hUc hf hn hs hg (p := 1) le_rfl (by norm_num)
  have hglc := (hgl.comp_inverse hψ.continuousOn hψU hinv hD hDc).continuousOn_mul hψ.deriv.continuousOn
  have hHl : LocalLpConvergence 1 G (fun ν z => (s ν)⁻¹ • logDeriv (f ν ∘ ψ) z) H := by
    simpa only [ENNReal.ofReal_one] using!
      hc.logDeriv_localLpConvergence hG hGc hfc hnc hs hH (p := 1) le_rfl (by norm_num)
  have hsource (ν : ℕ) :
      (fun z => (s ν)⁻¹ • logDeriv (f ν ∘ ψ) z) =ᵐ[volume.restrict G]
        (fun z => deriv ψ z * ((s ν)⁻¹ • logDeriv (f ν) (ψ z))) := by
    filter_upwards [ae_restrict_mem hG.measurableSet] with z hz
    rw [logDeriv_comp (hf ν (ψ z) (hψU hz)).differentiableAt (hψ z hz).differentiableAt]
    simp only [Complex.real_smul]
    ring
  exact ⟨H, hH, ((hHl.congr_ae hsource EventuallyEq.rfl).inMeasure (by norm_num)).ae_unique hG
    (hglc.inMeasure (by norm_num))⟩

end ModifiedCartan
#print axioms ModifiedCartan.normalizedLog_inverse_pullback_subharmonic
#print axioms ModifiedCartan.normalizedLog_inverse_pullback_gradient

