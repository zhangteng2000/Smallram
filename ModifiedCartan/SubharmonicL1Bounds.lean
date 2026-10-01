import ModifiedCartan.SubharmonicMean

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem abs_le_twice_upper_sub {x M : ℝ} (hM : 0 ≤ M) (hx : x ≤ M) : |x| ≤ 2 * M - x := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]
    linarith
  · rw [abs_of_nonpos h]
    linarith

/-- Quantitative disk L1 control from an upper bound and one finite lower
anchor. This is a lowest-level estimate for the compactness dichotomy. -/
theorem IsSubharmonicOn.integral_norm_le_of_lower_anchor {U : Set ℂ} {u : ℂ → EReal}
    (hu : IsSubharmonicOn U u) {c : ℂ} {r M L : ℝ} (hr : 0 < r)
    (hball : closedBall c r ⊆ U) (hM : 0 ≤ M)
    (hupper : ∀ z ∈ closedBall c r, u z ≤ (M : EReal))
    (hlower : ((-L : ℝ) : EReal) ≤ u c) :
    (∫ z in ball c r, ‖(u z).toReal‖) ≤ (Real.pi * r ^ 2) * (2 * M + L) := by
  have hc : u c ≠ ⊥ := ne_of_gt ((EReal.bot_lt_coe (-L)).trans_le hlower)
  have hc' := hu.ne_top c (hball (mem_closedBall_self hr.le))
  have hvol : volume (ball c r) < ⊤ :=
    (measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall c r).measure_lt_top
  have : IsFiniteMeasure (volume.restrict (ball c r)) := ⟨by simpa using hvol⟩
  have hint := hu.integrableOn_toReal_ball hr hball hc
  have hle : (∫ z in ball c r, ‖(u z).toReal‖) ≤ ∫ z in ball c r, 2 * M - (u z).toReal := by
    apply integral_mono_ae hint.norm ((integrable_const (2 * M)).sub hint)
    filter_upwards [hu.ae_finite_on_ball hr hball hc, ae_restrict_mem isOpen_ball.measurableSet]
      with z hz hzball
    have hMz : (u z).toReal ≤ M := by
      have h := hupper z (ball_subset_closedBall hzball)
      rwa [← EReal.coe_toReal hz.2 hz.1, EReal.coe_le_coe_iff] at h
    change ‖(u z).toReal‖ ≤ 2 * M - (u z).toReal
    rw [Real.norm_eq_abs]
    exact abs_le_twice_upper_sub hM hMz
  rw [integral_sub (integrable_const (2 * M)) hint, setIntegral_const, smul_eq_mul] at hle
  change _ ≤ (volume (ball c r)).toReal * (2 * M) - _ at hle
  rw [complex_ball_real_volume c hr.le] at hle
  have havg := hu.mul_area_le_integral hr hball hc
  have hlow : -L ≤ (u c).toReal := by
    rwa [← EReal.coe_toReal hc' hc, EReal.coe_le_coe_iff] at hlower
  have harea : 0 ≤ Real.pi * r ^ 2 := mul_nonneg Real.pi_pos.le (sq_nonneg r)
  nlinarith

theorem IsSubharmonicOn.l1_bound_of_anchor_in_ball {U : Set ℂ} {u : ℂ → EReal}
    (hu : IsSubharmonicOn U u) {c a : ℂ} {r M L : ℝ} (hr : 0 < r)
    (hball : closedBall c (3 * r) ⊆ U) (hM : 0 ≤ M)
    (hupper : ∀ z ∈ closedBall c (3 * r), u z ≤ (M : EReal))
    (ha : a ∈ ball c r) (hlower : ((-L : ℝ) : EReal) ≤ u a) :
    IntegrableOn (fun z => (u z).toReal) (ball c r) ∧
      (∫ z in ball c r, ‖(u z).toReal‖) ≤ (Real.pi * (2 * r) ^ 2) * (2 * M + L) := by
  have hac : dist a c < r := ha
  have hbig : closedBall a (2 * r) ⊆ closedBall c (3 * r) :=
    closedBall_subset_closedBall' (by linarith)
  have hsmall : ball c r ⊆ ball a (2 * r) :=
    ball_subset_ball' (by rw [dist_comm]; linarith)
  have hapos : u a ≠ ⊥ := ne_of_gt ((EReal.bot_lt_coe (-L)).trans_le hlower)
  have hint := hu.integrableOn_toReal_ball (by linarith : 0 < 2 * r) (hbig.trans hball) hapos
  refine ⟨hint.mono_set hsmall, ?_⟩
  have hmono := setIntegral_mono_set (s := ball c r) (t := ball a (2 * r)) hint.norm
    (Eventually.of_forall (fun z => norm_nonneg ((u z).toReal))) (Eventually.of_forall hsmall)
  exact hmono.trans (hu.integral_norm_le_of_lower_anchor (by linarith : 0 < 2 * r)
    (hbig.trans hball) hM (fun z hz => hupper z (hbig hz)) hlower)


end ModifiedCartan

