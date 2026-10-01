import ModifiedCartan.SubharmonicMean
import Mathlib.MeasureTheory.Integral.Average

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

/-- Disk averaging with mathlib's normalized-measure convention. -/
noncomputable def diskAverage (r : ℝ) (f : ℂ → ℝ) (c : ℂ) : ℝ :=
  ⨍ z in ball c r, f z

theorem diskAverage_eq {r : ℝ} (hr : 0 ≤ r) (f : ℂ → ℝ) (c : ℂ) :
    diskAverage r f c = (Real.pi * r ^ 2)⁻¹ * ∫ z in ball c r, f z := by
  rw [diskAverage, setAverage_eq, smul_eq_mul]
  change (volume (ball c r)).toReal⁻¹ * _ = _
  rw [complex_ball_real_volume c hr]

theorem diskAverage_const {r : ℝ} (hr : 0 < r) (b : ℝ) (c : ℂ) :
    diskAverage r (fun _ => b) c = b := by
  rw [diskAverage_eq hr.le, setIntegral_const, smul_eq_mul]
  change (Real.pi * r ^ 2)⁻¹ * ((volume (ball c r)).toReal * b) = b
  rw [complex_ball_real_volume c hr.le]
  have harea : Real.pi * r ^ 2 ≠ 0 := ne_of_gt (mul_pos Real.pi_pos (sq_pos_of_pos hr))
  field_simp

theorem diskAverage_sub {r : ℝ} {f g : ℂ → ℝ} {c : ℂ}
    (hf : IntegrableOn f (ball c r)) (hg : IntegrableOn g (ball c r)) :
    diskAverage r (fun z => f z - g z) c = diskAverage r f c - diskAverage r g c := by
  simp only [diskAverage, setAverage_eq, smul_eq_mul, integral_sub hf hg, mul_sub]

theorem norm_diskAverage_sub_le {T : Set ℂ} {r : ℝ} (hr : 0 < r) {c : ℂ}
    (hball : ball c r ⊆ T) {f g : ℂ → ℝ} (hf : IntegrableOn f T) (hg : IntegrableOn g T) :
    ‖diskAverage r f c - diskAverage r g c‖ ≤
      (Real.pi * r ^ 2)⁻¹ * ∫ z in T, ‖f z - g z‖ := by
  have harea : 0 < (Real.pi * r ^ 2)⁻¹ := inv_pos.mpr (mul_pos Real.pi_pos (sq_pos_of_pos hr))
  rw [← diskAverage_sub (hf.mono_set hball) (hg.mono_set hball), diskAverage_eq hr.le, norm_mul,
    show ‖(Real.pi * r ^ 2)⁻¹‖ = (Real.pi * r ^ 2)⁻¹ from by
      rw [Real.norm_eq_abs, abs_of_pos harea]]
  apply mul_le_mul_of_nonneg_left _ harea.le
  have hmono := setIntegral_mono_set (s := ball c r) (t := T) (hf.sub hg).norm
    (Eventually.of_forall (fun z => norm_nonneg (f z - g z))) (Eventually.of_forall hball)
  exact (norm_integral_le_integral_norm (fun z => f z - g z)).trans hmono

theorem LocalLpConvergence.diskAverage_tendstoUniformlyOn {U T K : Set ℂ}
    {f : ℕ → ℂ → ℝ} {g : ℂ → ℝ} (h : LocalLpConvergence 1 U f g)
    (hT : IsCompact T) (hTU : T ⊆ U) {r : ℝ} (hr : 0 < r)
    (hballs : ∀ c ∈ K, ball c r ⊆ T) :
    TendstoUniformlyOn (fun n => diskAverage r (f n)) (diskAverage r g) atTop K := by
  have ht : Tendsto (fun n => (Real.pi * r ^ 2)⁻¹ * ∫ z in T, ‖f n z - g z‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using (h.integral_norm_sub_tendsto_zero hT hTU).const_mul ((Real.pi * r ^ 2)⁻¹)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn c hc
  rw [dist_comm, dist_eq_norm]
  exact (norm_diskAverage_sub_le hr (hballs c hc)
    (memLp_one_iff_integrable.mp (h.source_mem T hT hTU n))
    (memLp_one_iff_integrable.mp (h.limit_mem T hT hTU))).trans_lt hn

theorem IsSubharmonicOn.le_diskAverage_value {U : Set ℂ} {u : ℂ → EReal}
    (hu : IsSubharmonicOn U u) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hball : closedBall c r ⊆ U) : u c ≤ (diskAverage r (fun z => (u z).toReal) c : EReal) := by
  rw [diskAverage_eq hr.le]
  exact hu.le_diskAverage hr hball


end ModifiedCartan

