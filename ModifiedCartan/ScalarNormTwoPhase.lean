import ModifiedCartan.ScalarPowerGradient
import ModifiedCartan.TwoPhaseForms

open scoped Topology BigOperators ENNReal
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Retain one fixed root of the actual quadratic while comparing coordinates. -/
theorem ArbitraryRadiusLimitData.unitary_component_locallyTwoPhase_of_root
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) {a : ℂ} (ha : a ≠ 0) (ha4 : ‖a‖ < 4)
    {ns : ℕ → ℕ} (hns : StrictMono ns) (V : ℕ → Matrix.unitaryGroup (Index 1) ℂ)
    (j : Index 1) {u : ℂ → EReal} {v : ℂ → ℝ}
    (hu : IsSubharmonicOn (ball (0 : ℂ) 4) u)
    (hrep : u =ᵐ[volume.restrict (ball (0 : ℂ) 4)] (fun z => (v z : EReal)))
    (hlim : LocalERealLpConvergence 1 (ball (0 : ℂ) 4)
      (fun ν => normalizedExtendedLog (characteristic f (r (d.subseq (ns ν))))
        (fun z => (polynomialMatrixGauge (d.polynomial (ns ν))
          (V ν : Matrix (Index 1) (Index 1) ℂ) j).eval z)) v)
    (b : ℂ) (hb : b ^ 2 = -(d.coefficient 0 a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2)) :
    LocallyTwoPhaseOn (powerChartDomain a ρ) (fun w => (u (powerChart a ρ w)).toReal) b := by
  obtain ⟨q, H, hq, hsub, hH, he⟩ := d.unitary_component_powerChart_quadratic hρ ha ha4 hns V j hu hrep hlim
  have hroots : ∀ᵐ w ∂volume.restrict (powerChartDomain a ρ), H w = b ∨ H w = -b := by
    filter_upwards [he] with w hw
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
    rcases hw with hw | hw
    · rw [hw]; exact hq.trans hb.symm
    · rw [hw, neg_sq]; exact hq.trans hb.symm
  intro c hc
  simpa only [EReal.toReal_coe, HasTwoPhaseFormOn] using
    hsub.locally_two_phase_form (powerChartDomain_isOpen a ρ) EventuallyEq.rfl hH b hroots hc

/-- A two-coordinate EReal maximum of finite values is the real maximum. -/
theorem ereal_fin_two_sup_coe (u : Fin 2 → ℝ) :
    Finset.univ.sup (fun j => (u j : EReal)) = ((max (u 0) (u 1) : ℝ) : EReal) := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j _
    fin_cases j
    · exact EReal.coe_le_coe_iff.mpr (le_max_left _ _)
    · exact EReal.coe_le_coe_iff.mpr (le_max_right _ _)
  · rcases le_total (u 0) (u 1) with h | h
    · rw [max_eq_right h]; exact Finset.le_sup (f := fun j => (u j : EReal)) (Finset.mem_univ (1 : Fin 2))
    · rw [max_eq_left h]; exact Finset.le_sup (f := fun j => (u j : EReal)) (Finset.mem_univ (0 : Fin 2))

/-- The actual scalar norm limit has locally exactly the same two phases.
The basis and both logarithmic component limits are constructed from d. -/
theorem ArbitraryRadiusLimitData.scalar_norm_powerChart_locallyTwoPhase
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hρ : 1 ≤ ρ) {a : ℂ} (ha : a ≠ 0) (ha4 : ‖a‖ < 4) :
    ∃ b : ℂ, b ^ 2 = -(d.coefficient 0 a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2) ∧
      LocallyTwoPhaseOn (powerChartDomain a ρ) (fun w => (d.U (powerChart a ρ w)).toReal) b := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq
    (-(d.coefficient 0 a * (a * ((ρ⁻¹ : ℝ) : ℂ)) ^ 2)) (n := 2) (by norm_num)
  obtain ⟨c₀, _, hc₀⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (isOpen_ball.measure_ne_zero volume (nonempty_ball.mpr (by norm_num : (0 : ℝ) < 2))) d.good_centers.full_measure
  obtain ⟨ns, hns, V, u, v, hu, hmax, _, _⟩ := Paper.lem_basis_at_point d c₀ hc₀
  let ψ := powerChart a ρ
  let G := powerChartDomain a ρ
  have hr : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hreg (j : Index 1) := d.unitary_component_regular hns V j
    (hu j).1 (hu j).2.2.1 (hu j).2.2.2
  have hphase (j : Index 1) : LocallyTwoPhaseOn G (fun w => (u j (ψ w)).toReal) b :=
    d.unitary_component_locallyTwoPhase_of_root hρ ha ha4 hns V j
      (hu j).1 (hu j).2.2.1 (hu j).2.2.2 b hb
  have hc (j : Index 1) : ContinuousOn (fun w => (u j (ψ w)).toReal) G :=
    (hreg j).2.continuousOn.comp (powerChart_analytic a ρ).continuousOn (powerChart_mapsTo ha hr)
  have hm := (hphase 0).max (powerChartDomain_isOpen a ρ) (hphase 1) (hc 0) (hc 1)
  have heq : EqOn (fun w => (d.U (ψ w)).toReal)
      (fun w => max (u 0 (ψ w)).toReal (u 1 (ψ w)).toReal) G := by
    intro w hw
    have hz := powerChart_mapsTo ha hr hw
    have he : d.U (ψ w) = ((max (u 0 (ψ w)).toReal (u 1 (ψ w)).toReal : ℝ) : EReal) := by
      rw [hmax hz]
      have hf : (fun j => u j (ψ w)) = (fun j => ((u j (ψ w)).toReal : EReal)) :=
        funext (fun j => (hreg j).1 _ hz)
      change Finset.univ.sup (fun j => u j (ψ w)) = _
      rw [hf]
      simpa only using! ereal_fin_two_sup_coe (fun j => (u j (ψ w)).toReal)
    change (d.U (ψ w)).toReal = _
    rw [he, EReal.toReal_coe]
  refine ⟨b, hb, fun c hc => ?_⟩
  obtain ⟨s, hs, hsG, hform⟩ := hm c hc
  exact ⟨s, hs, hsG, hform.congr (heq.symm.mono hsG) (mem_ball_self hs)⟩

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_norm_powerChart_locallyTwoPhase

