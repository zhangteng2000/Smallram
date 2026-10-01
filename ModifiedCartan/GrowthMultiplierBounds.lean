import ModifiedCartan.NormComparison
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

theorem extend_growth_upper_to_one (T : ℝ → ℝ)
    (hT : ∀ r, 0 < r → 0 < T r) (hmono : MonotoneOn T (Ioi 0))
    {p C X r0 : ℝ} (hp : 0 ≤ p) (hC : 0 < C) (hX : 1 ≤ X) (hr0 : 0 < r0)
    (hb : ∀ x r, X ≤ x → r0 ≤ r → T (x * r) ≤ C * x ^ p * T r) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ x r, 1 ≤ x → r0 ≤ r → T (x * r) / T r ≤ D * x ^ p := by
  let D := max 1 (C * X ^ p + C)
  have hD : 1 ≤ D := le_max_left _ _
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  have hXp : 0 < X ^ p := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hX) p
  have hCD : C ≤ D := by
    have := le_max_right 1 (C * X ^ p + C)
    dsimp [D]
    nlinarith
  have hCXD : C * X ^ p ≤ D := by
    have := le_max_right 1 (C * X ^ p + C)
    dsimp [D]
    linarith
  refine ⟨D, hD, ?_⟩
  intro x r hx hr
  have hx0 := lt_of_lt_of_le zero_lt_one hx
  have hrpos := hr0.trans_le hr
  have hTr := hT r hrpos
  have hxpow := Real.one_le_rpow hx hp
  by_cases hXx : X ≤ x
  · have hq : T (x * r) / T r ≤ C * x ^ p := (div_le_iff₀ hTr).mpr (hb x r hXx hr)
    exact hq.trans (mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg hx0.le p))
  · have hxr : x * r ≤ X * r := mul_le_mul_of_nonneg_right (lt_of_not_ge hXx).le hrpos.le
    have hTx := hmono (mul_pos hx0 hrpos) (mul_pos (lt_of_lt_of_le zero_lt_one hX) hrpos) hxr
    have hq : T (x * r) / T r ≤ C * X ^ p :=
      (div_le_iff₀ hTr).mpr (hTx.trans (hb X r le_rfl hr))
    exact hq.trans (hCXD.trans (by nlinarith))

theorem extend_growth_lower_to_one (T : ℝ → ℝ)
    (hT : ∀ r, 0 < r → 0 < T r) (hmono : MonotoneOn T (Ioi 0))
    {p c X r0 : ℝ} (hp : 0 ≤ p) (hc : 0 < c) (hX : 1 ≤ X) (hr0 : 0 < r0)
    (hb : ∀ x r, X ≤ x → r0 ≤ r → c * x ^ p * T r ≤ T (x * r)) :
    ∃ a : ℝ, 0 < a ∧ ∀ x r, 1 ≤ x → r0 ≤ r → a * x ^ p ≤ T (x * r) / T r := by
  let a := min c (X ^ p)⁻¹
  have hXp : 0 < X ^ p := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hX) p
  have ha : 0 < a := lt_min hc (inv_pos.mpr hXp)
  refine ⟨a, ha, ?_⟩
  intro x r hx hr
  have hx0 := lt_of_lt_of_le zero_lt_one hx
  have hrpos := hr0.trans_le hr
  have hTr := hT r hrpos
  by_cases hXx : X ≤ x
  · have hq : c * x ^ p ≤ T (x * r) / T r := (le_div_iff₀ hTr).mpr (hb x r hXx hr)
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg hx0.le p)).trans hq
  · have hTx : T r ≤ T (x * r) := hmono hrpos (mul_pos hx0 hrpos) (by nlinarith)
    have hq : 1 ≤ T (x * r) / T r := (le_div_iff₀ hTr).mpr (by simpa only [one_mul] using hTx)
    apply le_trans _ hq
    calc
      a * x ^ p ≤ (X ^ p)⁻¹ * X ^ p := mul_le_mul (min_le_right _ _)
        (Real.rpow_le_rpow hx0.le (lt_of_not_ge hXx).le hp)
        (Real.rpow_nonneg hx0.le p) (inv_nonneg.mpr hXp.le)
      _ = 1 := inv_mul_cancel₀ hXp.ne'

end
end ModifiedCartan
#print axioms ModifiedCartan.extend_growth_upper_to_one
#print axioms ModifiedCartan.extend_growth_lower_to_one
