import ModifiedCartan.SubharmonicMean

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem IsSubharmonicOn.le_of_ae_bound_on_ball {U : Set ℂ} {u : ℂ → EReal}
    (hu : IsSubharmonicOn U u) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hball : closedBall c r ⊆ U) {M : ℝ}
    (hbound : ∀ᵐ z ∂volume.restrict (ball c r), u z ≤ (M : EReal)) : u c ≤ (M : EReal) := by
  by_cases hc : u c = ⊥
  · rw [hc]
    exact bot_le
  have hc' := hu.ne_top c (hball (mem_closedBall_self hr.le))
  have hvol : volume (ball c r) < ⊤ :=
    (measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall c r).measure_lt_top
  have : IsFiniteMeasure (volume.restrict (ball c r)) := ⟨by simpa using hvol⟩
  have hreal : ∀ᵐ z ∂volume.restrict (ball c r), (u z).toReal ≤ M := by
    filter_upwards [hu.ae_finite_on_ball hr hball hc, hbound] with z hz hMz
    rw [← EReal.coe_toReal hz.2 hz.1, EReal.coe_le_coe_iff] at hMz
    exact hMz
  have hint := integral_mono_ae (hu.integrableOn_toReal_ball hr hball hc) (integrable_const M) hreal
  rw [setIntegral_const, smul_eq_mul] at hint
  change _ ≤ (volume (ball c r)).toReal * M at hint
  rw [complex_ball_real_volume c hr.le] at hint
  have hpoint := hu.mul_area_le_integral hr hball hc
  have harea : 0 < Real.pi * r ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hr)
  have hle : (u c).toReal ≤ M := (mul_le_mul_iff_right₀ harea).mp (hpoint.trans hint)
  rw [← EReal.coe_toReal hc' hc, EReal.coe_le_coe_iff]
  exact hle

theorem IsSubharmonicOn.le_of_ae_le_upperSemicontinuous {U : Set ℂ} {u v : ℂ → EReal}
    (hu : IsSubharmonicOn U u) (hv : UpperSemicontinuousOn v U) (hU : IsOpen U)
    (hle : ∀ᵐ z ∂volume.restrict U, u z ≤ v z) : ∀ x ∈ U, u x ≤ v x := by
  intro x hx
  by_contra hnot
  obtain ⟨M, hvM, hMu⟩ := EReal.exists_between_coe_real (lt_of_not_ge hnot)
  have hevent : ∀ᶠ z in 𝓝 x, v z < (M : EReal) := by
    simpa only [hU.nhdsWithin_eq hx] using hv x hx (M : EReal) hvM
  obtain ⟨ε, hε, hεboth⟩ := Metric.mem_nhds_iff.mp (inter_mem hevent (hU.mem_nhds hx))
  have hclosed : closedBall x (ε / 2) ⊆ U :=
    ((closedBall_subset_ball (half_lt_self hε)).trans hεboth).trans inter_subset_right
  have hballU : ball x (ε / 2) ⊆ U := ball_subset_closedBall.trans hclosed
  have hbound : ∀ᵐ z ∂volume.restrict (ball x (ε / 2)), u z ≤ (M : EReal) := by
    filter_upwards [hle.filter_mono (ae_mono (Measure.restrict_mono_set _ hballU)),
      ae_restrict_mem isOpen_ball.measurableSet] with z hz hzball
    exact hz.trans (le_of_lt (hεboth ((ball_subset_ball (half_le_self hε.le)) hzball)).1)
  exact (not_lt_of_ge (hu.le_of_ae_bound_on_ball (half_pos hε) hclosed hbound)) hMu

theorem IsSubharmonicOn.eqOn_of_ae_eq {U : Set ℂ} {u v : ℂ → EReal}
    (hu : IsSubharmonicOn U u) (hv : IsSubharmonicOn U v) (hU : IsOpen U)
    (heq : u =ᵐ[volume.restrict U] v) : EqOn u v U := by
  have h₁ := hu.le_of_ae_le_upperSemicontinuous hv.upperSemicontinuousOn hU
    (heq.mono (fun _ hz => hz.le))
  have h₂ := hv.le_of_ae_le_upperSemicontinuous hu.upperSemicontinuousOn hU
    (heq.mono (fun _ hz => hz.ge))
  exact fun x hx => le_antisymm (h₁ x hx) (h₂ x hx)


end ModifiedCartan

