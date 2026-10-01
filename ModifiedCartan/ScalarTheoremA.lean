import ModifiedCartan.ScalarDeficiencyQuantization
import ModifiedCartan.ScalarTheoremGrowth
import Mathlib.Topology.Algebra.InfiniteSum.Ring

open scoped Topology
open Filter Set Asymptotics
set_option autoImplicit false
namespace ModifiedCartan

/-- LaTeX `thm:A`, in full, for the actual scalar meromorphic function and its
literal characteristic, lower order, critical-point count, and deficiencies.
Both the growth assertion (a) and deficiency quantization and total (b) follow
from kernel-checked proofs, including construction of the global reduced lift. -/
theorem Paper.thm_A (f : ℂ → ℂ) : ScalarTheoremATarget f := by
  intro hf htrans hfinite hsmall
  obtain ⟨ρ, m, ℓ, hm, hρm, ho, hlo, hslow, ht⟩ :=
    Paper.thm_A_growth f hf htrans hfinite hsmall
  obtain ⟨F, hFt, hFl, he, _, hD⟩ := exists_scalar_curve_lift hf htrans
  have hcomp := scalarCharacteristic_isEquivalent_lift hf F hFt hFl he hD
  have hgrowth := growthOrders_eq_of_isEquivalent hcomp
    (characteristic_tendsto_atTop_of_transcendental F hFt)
  have hFfinite : FiniteLowerOrder F := by
    change lowerGrowthOrder (characteristic F) < ⊤
    rw [← hgrowth.2]
    exact hfinite
  have hFsmall : SmallRamification F := by
    change ramification F =o[atTop] characteristic F
    rw [← scalarRamification_eq_curve hf F hFl he hD]
    exact hsmall.trans_isBigO hcomp.isBigO
  obtain ⟨ρ', hl', _, ho', hu', _⟩ :=
    exists_common_admissible_order F (by norm_num) hFt hFl hFfinite hFsmall
  have heρ : ρ' = ρ := EReal.coe_eq_coe_iff.mp (ho'.symm.trans (hgrowth.1.symm.trans ho))
  subst ρ'
  have hρ : 1 ≤ ρ := by
    have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    rw [hρm]
    linarith
  obtain ⟨p, hp, hdef⟩ := scalarDeficiency_quantization_of_lift hf F hFt hFl he hD hFsmall hρ hl' hu' hρm
  exact ⟨ρ, m, ℓ, p, hm, hρm, ho, hlo, hslow, ht, hdef, hp⟩

/-- LaTeX `sum`, the deficiency sum two asserted after `thm:A` (b).
The real conversions preserve the actual finite EReal deficiencies. -/
theorem Paper.thm_A_deficiency_sum (f : ℂ → ℂ) (hf : Meromorphic f)
    (htrans : ScalarTranscendental f)
    (hfinite : lowerGrowthOrder (scalarCharacteristic f) < ⊤)
    (hsmall : scalarRamification f =o[atTop] scalarCharacteristic f) :
    HasSum (fun a : WithTop ℂ => (scalarDeficiency f a).toReal) 2 := by
  obtain ⟨ρ, m, _, p, hm, hρm, _, _, _, _, hdef, hp⟩ :=
    Paper.thm_A f hf htrans hfinite hsmall
  have hρ : 0 < ρ := by
    rw [hρm]
    have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hs := hp.div_const ρ
  have hcancel : (2 * ρ) / ρ = 2 := mul_div_cancel_right₀ 2 hρ.ne'
  simpa only [hdef, EReal.toReal_coe, hcancel] using hs

end ModifiedCartan
#print axioms ModifiedCartan.Paper.thm_A
#print axioms ModifiedCartan.Paper.thm_A_deficiency_sum
