import ModifiedCartan.SubharmonicMean
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.LiminfLimsup

open scoped Topology ENNReal
open Filter MeasureTheory Set Metric

set_option autoImplicit false

namespace ModifiedCartan

theorem integral_le_upper_add_l1_error {S T : Set ℂ} {f g : ℂ → ℝ} {M : ℝ}
    (hS : volume S < ⊤) (hST : S ⊆ T) (hf : IntegrableOn f T) (hg : IntegrableOn g T)
    (hbound : ∀ᵐ z ∂volume.restrict S, g z ≤ M) :
    (∫ z in S, f z) ≤ (volume S).toReal * M + ∫ z in T, ‖f z - g z‖ := by
  have : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hS⟩
  have hnorm : IntegrableOn (fun z => ‖f z - g z‖) T := (hf.sub hg).norm
  have hnormS := hnorm.mono_set hST
  have hle : (∫ z in S, f z) ≤ ∫ z in S, M + ‖f z - g z‖ := by
    apply integral_mono_ae (hf.mono_set hST) ((integrable_const M).add hnormS)
    filter_upwards [hbound] with z hz
    have h := le_abs_self (f z - g z)
    change f z ≤ M + ‖f z - g z‖
    rw [Real.norm_eq_abs]
    linarith
  rw [integral_add (integrable_const M) hnormS, setIntegral_const, smul_eq_mul] at hle
  have hmono := setIntegral_mono_set (s := S) (t := T) hnorm (Eventually.of_forall (fun z => norm_nonneg (f z - g z)))
    (Eventually.of_forall hST)
  exact hle.trans (add_le_add le_rfl hmono)

theorem subharmonic_eventually_upper_bound {U K V : Set ℂ}
    {u : ℕ → ℂ → EReal} {v : ℂ → ℝ}
    (hu : ∀ n, IsSubharmonicOn U (u n))
    (hconv : LocalLpConvergence 1 U (fun n z => (u n z).toReal) v)
    (hK : IsCompact K) (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hKV : K ⊆ V) (hVU : closure V ⊆ U)
    {M : ℝ} (hM : ∀ᵐ z ∂volume.restrict V, v z ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x ∈ K, u n x ≤ ((M + ε : ℝ) : EReal) := by
  obtain ⟨r, hr, hrV⟩ := hK.exists_cthickening_subset_open hV hKV
  have harea : 0 < Real.pi * r ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hr)
  have hevent := (hconv.integral_norm_sub_tendsto_zero hVc hVU).eventually
    (gt_mem_nhds (mul_pos harea hε))
  filter_upwards [hevent] with n hn x hx
  have hballV : closedBall x r ⊆ V := (closedBall_subset_cthickening hx r).trans hrV
  have hballT : ball x r ⊆ closure V := (ball_subset_closedBall.trans hballV).trans subset_closure
  have hfi := memLp_one_iff_integrable.mp (hconv.source_mem (closure V) hVc hVU n)
  have hgi := memLp_one_iff_integrable.mp (hconv.limit_mem (closure V) hVc hVU)
  have hvol : volume (ball x r) < ⊤ := (measure_mono hballT).trans_lt hVc.measure_lt_top
  have hnum := integral_le_upper_add_l1_error hvol hballT hfi hgi
    (hM.filter_mono (ae_mono (Measure.restrict_mono_set _ (ball_subset_closedBall.trans hballV))))
  rw [complex_ball_real_volume x hr.le] at hnum
  have hnum' : (∫ z in ball x r, (u n z).toReal) ≤ (M + ε) * (Real.pi * r ^ 2) := by
    nlinarith
  have havg : (Real.pi * r ^ 2)⁻¹ * (∫ z in ball x r, (u n z).toReal) ≤ M + ε := by
    simpa only [div_eq_mul_inv, mul_comm] using (div_le_iff₀ harea).mpr hnum'
  exact ((hu n).le_diskAverage hr (hballV.trans (subset_closure.trans hVU))).trans
    (EReal.coe_le_coe_iff.mpr havg)

namespace Paper

/-- Upper-bound conclusion of LaTeX label `lem:subharmonic-compactness`.
The proof only needs the limit's finite AE representative and its supremum
on V, so no extra regularity of the limit is assumed. -/
theorem lem_subharmonic_compactness_upper_bound {U K V : Set ℂ}
    {u : ℕ → ℂ → EReal} {v : ℂ → EReal} {vReal : ℂ → ℝ}
    (hu : ∀ n, IsSubharmonicOn U (u n))
    (hconv : LocalERealLpConvergence 1 U u vReal)
    (hrep : v =ᵐ[volume.restrict U] (fun z => (vReal z : EReal)))
    (hK : IsCompact K) (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hKV : K ⊆ V) (hVU : closure V ⊆ U) :
    limsup (fun n => sSup (u n '' K)) atTop ≤ sSup (v '' V) := by
  apply (limsup_le_iff').mpr
  intro y hy
  obtain ⟨M, hM, hMy⟩ := EReal.exists_between_coe_real hy
  obtain ⟨N, hMN, hNy⟩ := EReal.exists_between_coe_real hMy
  have hε : 0 < N - M := sub_pos.mpr (EReal.coe_lt_coe_iff.mp hMN)
  have hbound : ∀ᵐ z ∂volume.restrict V, vReal z ≤ M := by
    filter_upwards [hrep.filter_mono (ae_mono (Measure.restrict_mono_set _
      (subset_closure.trans hVU))), ae_restrict_mem hV.measurableSet] with z hz hzV
    apply EReal.coe_le_coe_iff.mp
    rw [← hz]
    exact (show v z ≤ sSup (v '' V) from le_sSup ⟨z, hzV, rfl⟩).trans hM.le
  have hevent := subharmonic_eventually_upper_bound hu hconv.real_convergence hK hV hVc hKV hVU hbound hε
  filter_upwards [hevent] with n hn
  apply sSup_le
  rintro _ ⟨z, hzK, rfl⟩
  have hzn : u n z ≤ (N : EReal) := by simpa only [add_sub_cancel] using hn z hzK
  exact hzn.trans hNy.le

end Paper


end ModifiedCartan

