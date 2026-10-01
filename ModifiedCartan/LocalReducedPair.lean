import ModifiedCartan.DiskCharacteristic
import Mathlib.Analysis.Meromorphic.FactorizedRational

open scoped Topology
open Filter Set Metric Function MeromorphicOn Function.locallyFinsuppWithin
set_option autoImplicit false
namespace ModifiedCartan

theorem factorizedRational_split_parts {U : Set ℂ}
    (D : locallyFinsuppWithin U ℤ) (hD : D.support.Finite) {z : ℂ} (hz : D z = 0) :
    (∏ᶠ a, (· - a) ^ D a) z =
      (∏ᶠ a, (· - a) ^ D⁺ a) z / (∏ᶠ a, (· - a) ^ D⁻ a) z := by
  classical
  let S := hD.toFinset
  have hexp (d : ℂ → ℤ) (hd : Function.support d ⊆ (S : Set ℂ)) :
      (∏ᶠ a, (· - a) ^ d a) z = ∏ a ∈ S, (z - a) ^ d a := by
    rw [finprod_eq_prod_of_mulSupport_subset _ (by
      rw [Function.FactorizedRational.mulSupport]
      exact hd), Finset.prod_apply]
    rfl
  have hs : Function.support D ⊆ (S : Set ℂ) := fun a ha => hD.mem_toFinset.mpr ha
  have hp : Function.support (fun a => D⁺ a) ⊆ (S : Set ℂ) := by
    intro a ha
    apply hs
    intro he
    exact ha (by simp [he])
  have hn : Function.support (fun a => D⁻ a) ⊆ (S : Set ℂ) := by
    intro a ha
    apply hs
    intro he
    exact ha (by simp [he])
  rw [hexp D hs, hexp (fun a => D⁺ a) hp, hexp (fun a => D⁻ a) hn,
    ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro a ha
  have hza : z - a ≠ 0 := by
    intro he
    have hzero : D a = 0 := by simpa only [sub_eq_zero.mp he] using hz
    exact (hD.mem_toFinset.mp ha) hzero
  rw [← zpow_sub₀ hza]
  congr 1
  exact (congrArg (fun d : locallyFinsuppWithin U ℤ => d a) (posPart_sub_negPart D)).symm

/-- A finite local divisor gives an actual analytic numerator and polynomial
denominator without common zeros. The quotient agrees on the codiscrete filter. -/
theorem local_reduced_pair_of_finite_divisor {f : ℂ → ℂ} {U : Set ℂ}
    (hf : MeromorphicOn f U) (hfinite : ∀ u : U, meromorphicOrderAt f u ≠ ⊤)
    (hD : (divisor f U).support.Finite) :
    ∃ p q : ℂ → ℂ, AnalyticOnNhd ℂ p U ∧ Differentiable ℂ q ∧
      (∀ z ∈ U, p z ≠ 0 ∨ q z ≠ 0) ∧
      f =ᶠ[codiscreteWithin U] (fun z => p z / q z) ∧
      divisor q U = (divisor f U)⁻ ∧
      (∀ z, divisor f U z = 0 → q z ≠ 0) := by
  obtain ⟨g, hg, hg0, hfg⟩ := hf.extract_zeros_poles hfinite hD
  let D := divisor f U
  let P : ℂ → ℂ := ∏ᶠ a, (· - a) ^ D⁺ a
  let q : ℂ → ℂ := ∏ᶠ a, (· - a) ^ D⁻ a
  let p : ℂ → ℂ := fun z => P z * g z
  have hP (z : ℂ) : AnalyticAt ℂ P z :=
    Function.FactorizedRational.analyticAt (posPart_nonneg D z)
  have hq (z : ℂ) : AnalyticAt ℂ q z :=
    Function.FactorizedRational.analyticAt (negPart_nonneg D z)
  refine ⟨p, q, (fun z hz => (hP z).mul (hg z hz)),
    (fun z => (hq z).differentiableAt), ?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases le_total (D z) 0 with hle | hge
    · left
      exact mul_ne_zero (Function.FactorizedRational.ne_zero
        (show D⁺ z = 0 by simpa using posPart_eq_zero.mpr hle)) (hg0 ⟨z, hz⟩)
    · right
      exact Function.FactorizedRational.ne_zero
        (show D⁻ z = 0 by simpa using negPart_eq_zero.mpr hge)
  · filter_upwards [hfg, D.eq_zero_codiscreteWithin] with z hz hzD
    change f z = p z / q z
    change f z = (∏ᶠ a, (· - a) ^ D a) z * g z at hz
    rw [hz, factorizedRational_split_parts D hD hzD]
    dsimp only [p, P, q]
    ring
  · apply Function.FactorizedRational.divisor
    exact hD.subset (fun z hz => by intro he; exact hz (by simp [D, he]))
  · intro z hz
    exact Function.FactorizedRational.ne_zero (show D⁻ z = 0 by simp [D, hz])

end ModifiedCartan
#print axioms ModifiedCartan.local_reduced_pair_of_finite_divisor

