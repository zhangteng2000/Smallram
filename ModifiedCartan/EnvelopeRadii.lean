import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open scoped Topology
open Filter Set Asymptotics
set_option autoImplicit false
namespace ModifiedCartan

/-- The maximizing-radius construction in LaTeX `lem:envelope`.
The tail maximum is obtained on an explicitly bounded compact interval. -/
theorem exists_power_envelope_radius {H : ℝ → ℝ} {α R : ℝ}
    (hH : ContinuousOn H (Ioi 0)) (hm : MonotoneOn H (Ioi 0))
    (hR : 0 < R) (hHR : 0 < H R)
    (hzero : Tendsto (fun t => H t / t ^ α) atTop (𝓝 0)) :
    ∃ r : ℝ, R ≤ r ∧ 0 < H r ∧
      ∀ t : ℝ, 0 < t → H t ≤ H r * max 1 ((t / r) ^ α) := by
  let F : ℝ → ℝ := fun t => H t / t ^ α
  have hFR : 0 < F R := div_pos hHR (Real.rpow_pos_of_pos hR α)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hzero.eventually_lt_const hFR)
  let B := max R N
  have hRB : R ≤ B := le_max_left _ _
  have hF : ContinuousOn F (Icc R B) := by
    apply (hH.mono (fun t ht => hR.trans_le ht.1)).div
    · intro t ht
      exact (Real.continuousAt_rpow_const t α (Or.inl (hR.trans_le ht.1).ne')).continuousWithinAt
    · intro t ht
      exact (Real.rpow_pos_of_pos (hR.trans_le ht.1) α).ne'
  obtain ⟨r, hr, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hRB) hF
  have hrpos : 0 < r := hR.trans_le hr.1
  have hmaxR : F R ≤ F r := hmax ⟨le_rfl, hRB⟩
  have hHr : 0 < H r := by
    by_contra hn
    have hnonpos : F r ≤ 0 := div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn)
      (Real.rpow_pos_of_pos hrpos α).le
    linarith
  have hmaxTail (t : ℝ) (ht : R ≤ t) : F t ≤ F r := by
    by_cases htb : t ≤ B
    · exact hmax ⟨ht, htb⟩
    · exact (hN t ((le_max_right R N).trans (le_of_not_ge htb))).le.trans hmaxR
  refine ⟨r, hr.1, hHr, ?_⟩
  intro t ht
  by_cases htr : t ≤ r
  · exact (hm ht hrpos htr).trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (le_max_left 1 ((t / r) ^ α)) hHr.le)
  · have hratio := hmaxTail t (hr.1.trans (le_of_not_ge htr))
    have hbound : H t ≤ H r * ((t / r) ^ α) := by
      rw [Real.div_rpow ht.le hrpos.le α, ← mul_div_assoc]
      apply (le_div_iff₀ (Real.rpow_pos_of_pos hrpos α)).mpr
      exact (div_le_div_iff₀ (Real.rpow_pos_of_pos ht α) (Real.rpow_pos_of_pos hrpos α)).mp hratio
    exact hbound.trans (mul_le_mul_of_nonneg_left (le_max_right 1 ((t / r) ^ α)) hHr.le)

/-- Actual envelope radii tending to infinity, before applying the integral
kernel in `lem:envelope`. -/
theorem exists_power_envelope_sequence {H : ℝ → ℝ} {α : ℝ}
    (hH : ContinuousOn H (Ioi 0)) (hm : MonotoneOn H (Ioi 0))
    (hp : ∀ᶠ t in atTop, 0 < H t)
    (ho : H =o[atTop] (fun t => t ^ α)) :
    ∃ r : ℕ → ℝ, (∀ ν, 0 < r ν) ∧ Tendsto r atTop atTop ∧
      (∀ ν, 0 < H (r ν)) ∧
      ∀ ν t, 0 < t → H t ≤ H (r ν) * max 1 ((t / r ν) ^ α) := by
  obtain ⟨R0, hR0⟩ := eventually_atTop.mp hp
  let R : ℕ → ℝ := fun ν => max ((ν : ℝ) + 1) (max 1 R0)
  have hRpos (ν : ℕ) : 0 < R ν := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hRlarge (ν : ℕ) : R0 ≤ R ν := (le_max_right 1 R0).trans (le_max_right _ _)
  have hex (ν : ℕ) := exists_power_envelope_radius hH hm (hRpos ν) (hR0 _ (hRlarge ν))
    ho.tendsto_div_nhds_zero
  choose r hr hHr hb using hex
  refine ⟨r, fun ν => (hRpos ν).trans_le (hr ν), ?_, hHr, hb⟩
  have hbase : Tendsto (fun ν : ℕ => (ν : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact tendsto_atTop_mono (fun ν => (le_max_left _ _).trans (hr ν)) hbase

end ModifiedCartan
#print axioms ModifiedCartan.exists_power_envelope_sequence
