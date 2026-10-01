import ModifiedCartan.UnitaryPowerConvexity

open scoped Topology BigOperators ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Retain the actual pulled-back subharmonic function, weak gradient, and
constant equation used in the finite-gradient convexity proof. This is proved
from the same actual logarithmic limits, not an added equation hypothesis. -/
theorem ArbitraryRadiusLimitData.unitary_component_powerChart_gradient_equation
    {n : ℕ} {f : Curve n} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) {a : ℂ} (ha : a ≠ 0) (ha4 : ‖a‖ < 4)
    {ns : ℕ → ℕ} (hns : StrictMono ns) (V : ℕ → Matrix.unitaryGroup (Index n) ℂ)
    (j : Index n) {u : ℂ → EReal} {v : ℂ → ℝ}
    (hu : IsSubharmonicOn (ball (0 : ℂ) 4) u)
    (hrep : u =ᵐ[volume.restrict (ball (0 : ℂ) 4)] (fun z => (v z : EReal)))
    (hlim : LocalERealLpConvergence 1 (ball (0 : ℂ) 4)
      (fun ν => normalizedExtendedLog (characteristic f (r (d.subseq (ns ν))))
        (fun z => (polynomialMatrixGauge (d.polynomial (ns ν))
          (V ν : Matrix (Index n) (Index n) ℂ) j).eval z)) v) :
    ∃ H : ℂ → ℂ,
      IsSubharmonicOn (powerChartDomain a ρ)
        (fun w => ((u (powerChart a ρ w)).toReal : EReal)) ∧
      HasWeakComplexGradient (powerChartDomain a ρ) (fun w => (u (powerChart a ρ w)).toReal) H ∧
      ∀ᵐ w ∂volume.restrict (powerChartDomain a ρ),
        H w ^ (n + 1) + ∑ i : Index n,
          (d.fullCoefficient i a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ (n + 1 - i.val)) * H w ^ i.val = 0 := by
  have hr : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  let G := powerChartDomain a ρ
  let ψ := powerChart a ρ
  let φ := powerChartInverse a ρ
  let F : ℕ → ℂ → ℂ := fun ν z =>
    (polynomialMatrixGauge (d.polynomial (ns ν)) (V ν : Matrix (Index n) (Index n) ℂ) j).eval z
  let s : ℕ → ℝ := fun ν => characteristic f (r (d.subseq (ns ν)))
  have hG : IsOpen G := powerChartDomain_isOpen a ρ
  have hGc : Convex ℝ G := powerChartDomain_convex a ρ
  have hGn : G.Nonempty := ⟨1, powerChartDomain_one_mem ha ha4 hr⟩
  have hψ : AnalyticOnNhd ℂ ψ G := powerChart_analytic a ρ
  have hψU : MapsTo ψ G (ball (0 : ℂ) 4) := powerChart_mapsTo ha hr
  have hinv : ∀ z ∈ G, φ (ψ z) = z := fun _ hz => powerChart_inverse ha hρ hz
  obtain ⟨D, hD, hDc⟩ := powerChart_inverse_jacobian ha hρ
  have hf (ν : ℕ) : AnalyticOnNhd ℂ (F ν) (ball (0 : ℂ) 4) :=
    (AnalyticOnNhd.eval_polynomial _).mono (subset_univ _)
  have hn (ν : ℕ) : ∃ z ∈ ball (0 : ℂ) 4, F ν z ≠ 0 :=
    hlim.normalizedLog_nontrivial isOpen_ball ⟨0, mem_ball_self (by norm_num)⟩ (d.scale_pos (ns ν))
  have hrealrep : v =ᵐ[volume.restrict (ball (0 : ℂ) 4)] (fun z => (u z).toReal) := by
    filter_upwards [hrep] with z hz
    rw [hz, EReal.toReal_coe]
  have hreal : LocalLpConvergence 1 (ball (0 : ℂ) 4)
      (fun ν z => (s ν)⁻¹ * Real.log ‖F ν z‖) (fun z => (u z).toReal) :=
    hlim.normalizedLog_real.congr_ae (fun _ => EventuallyEq.rfl) hrealrep
  have hreg := d.unitary_component_regular hns V j hu hrep hlim
  have hsub : IsSubharmonicOn G (fun w => ((u (ψ w)).toReal : EReal)) :=
    normalizedLog_inverse_pullback_subharmonic isOpen_ball (convex_ball (0 : ℂ) 4).isPreconnected
      hG hGc.isPreconnected hGn hf hn (fun ν => d.scale_pos (ns ν)) hreal
      hreg.2.continuousOn hψ hψU hinv hD hDc
  obtain ⟨g, hg, he⟩ := d.unitary_component_real_gradient hns V j hrep hlim
  obtain ⟨H, hH, hchain⟩ := normalizedLog_inverse_pullback_gradient isOpen_ball
    (convex_ball (0 : ℂ) 4).isPreconnected hG hGc.isPreconnected hGn hf hn
    (d.scale_tendsto.comp hns.tendsto_atTop) hreal hg hψ hψU hinv hD hDc
  have hpull := ae_comp_of_differentiable_inverse measurableSet_ball hG.measurableSet hψU hinv
    (fun z hz => (hD z hz).differentiableWithinAt) he
  let c : Index n → ℂ := fun i => d.fullCoefficient i a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ (n + 1 - i.val)
  have hpoly : ∀ᵐ w ∂volume.restrict G, H w ^ (n + 1) + ∑ i, c i * H w ^ i.val = 0 := by
    filter_upwards [hpull, hchain, ae_restrict_mem hG.measurableSet] with w hw heq hwG
    rw [heq]
    have hh := monic_equation_mul (fun i => d.fullCoefficient i (ψ w)) (m := deriv ψ w) hw
    simpa only [ψ, d.fullCoefficient_powerChart hr.ne' a hwG] using hh
  exact ⟨H, hsub, hH, hpoly⟩

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.unitary_component_powerChart_gradient_equation
