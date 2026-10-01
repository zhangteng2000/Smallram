import ModifiedCartan.DiskAverageApproximation

open scoped Topology ENNReal NNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem diskAverage_congr {f g : ℂ → ℝ} {r : ℝ} {c : ℂ}
    (hfg : EqOn f g (ball c r)) : diskAverage r f c = diskAverage r g c := by
  unfold diskAverage
  rw [setAverage_eq, setAverage_eq]
  congr 1
  exact setIntegral_congr_fun isOpen_ball.measurableSet hfg

theorem IsSubharmonicOn.le_diskAverage_of_eqOn {U : Set ℂ} {u : ℂ → EReal}
    (hu : IsSubharmonicOn U u) {f : ℂ → ℝ} {r : ℝ} {c : ℂ}
    (hr : 0 < r) (hball : closedBall c r ⊆ U)
    (hrep : EqOn (fun z => (u z).toReal) f (ball c r)) :
    u c ≤ (diskAverage r f c : EReal) := by
  rw [← diskAverage_congr hrep]
  exact hu.le_diskAverage_value hr hball

/-- Averaging preserves the local submean order inside the truncation region. -/
theorem IsSubharmonicOn.diskAverage_le_twice {U T : Set ℂ} {u : ℂ → EReal}
    (hu : IsSubharmonicOn U u)
    (hfinite : ∀ᵐ z ∂volume.restrict U, u z ≠ ⊥ ∧ u z ≠ ⊤)
    {f : ℂ → ℝ} (hf : Integrable f) (hTU : T ⊆ U)
    (hrep : EqOn (fun z => (u z).toReal) f T)
    {r : ℝ} (hr : 0 < r) {c : ℂ} (hball : closedBall c (2 * r) ⊆ T) :
    diskAverage r f c ≤ diskAverage r (diskAverage r f) c := by
  have hsmall : closedBall c r ⊆ T :=
    (closedBall_subset_closedBall (by linarith)).trans hball
  apply diskAverage_mono hr.le hf.integrableOn (diskAverage_integrable hr.le hf).integrableOn
  filter_upwards [hfinite.filter_mono (ae_mono (Measure.restrict_mono_set _
    (ball_subset_closedBall.trans (hsmall.trans hTU)))), ae_restrict_mem isOpen_ball.measurableSet]
    with z hz hzball
  have hzT : z ∈ T := hsmall (ball_subset_closedBall hzball)
  have hzclosed : closedBall z r ⊆ T :=
    (closedBall_subset_closedBall' (by have := mem_ball.mp hzball; linarith)).trans hball
  have hle := hu.le_diskAverage_of_eqOn hr (hzclosed.trans hTU)
    (fun w hw => hrep (hzclosed (ball_subset_closedBall hw)))
  have heq : (u z).toReal = f z := hrep hzT
  rw [← EReal.coe_toReal hz.2 hz.1, EReal.coe_le_coe_iff, heq] at hle
  exact hle

theorem IsSubharmonicOn.toReal_le_diskAverage_twice {U T : Set ℂ} {u : ℂ → EReal}
    (hu : IsSubharmonicOn U u)
    (hfinite : ∀ᵐ z ∂volume.restrict U, u z ≠ ⊥ ∧ u z ≠ ⊤)
    {f : ℂ → ℝ} (hf : Integrable f) (hTU : T ⊆ U)
    (hrep : EqOn (fun z => (u z).toReal) f T)
    {r : ℝ} (hr : 0 < r) {c : ℂ} (hball : closedBall c (2 * r) ⊆ T)
    (hc : u c ≠ ⊥) : (u c).toReal ≤ diskAverage r (diskAverage r f) c := by
  have hsmall : closedBall c r ⊆ T :=
    (closedBall_subset_closedBall (by linarith)).trans hball
  have hle := hu.le_diskAverage_of_eqOn hr (hsmall.trans hTU)
    (fun z hz => hrep (hsmall (ball_subset_closedBall hz)))
  rw [← EReal.coe_toReal (hu.ne_top c (hTU (hsmall (mem_closedBall_self hr.le)))) hc,
    EReal.coe_le_coe_iff] at hle
  exact hle.trans (hu.diskAverage_le_twice hfinite hf hTU hrep hr hball)


end ModifiedCartan
