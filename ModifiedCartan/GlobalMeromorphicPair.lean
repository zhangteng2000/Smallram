import ModifiedCartan.DivisorEntireMultiplicity
import Mathlib.Analysis.Meromorphic.RCLike

open scoped Topology
open Filter Set Function MeromorphicOn
set_option autoImplicit false
namespace ModifiedCartan

theorem entire_ne_zero_of_divisor_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {z : ℂ} (hn : meromorphicOrderAt f z ≠ ⊤) (hD : divisor f univ z = 0) : f z ≠ 0 := by
  have hM : MeromorphicOn f univ := fun w _ => (hf.analyticAt w).meromorphicAt
  rw [hM.divisor_apply (mem_univ z)] at hD
  exact (hf.analyticAt z).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp
    ((WithTop.untop₀_eq_zero.mp hD).resolve_right hn)

/-- Cancel the actual complete pole divisor by the proved entire product,
then remove the singularities of its product with f. Dependency of `thm:A`. -/
theorem global_reduced_pair_of_finite_orders {f : ℂ → ℂ} (hf : Meromorphic f)
    (hfinite : ∀ z, meromorphicOrderAt f z ≠ ⊤) :
    ∃ p q : ℂ → ℂ, Differentiable ℂ p ∧ Differentiable ℂ q ∧
      (∀ z, p z ≠ 0 ∨ q z ≠ 0) ∧
      f =ᶠ[codiscreteWithin (univ : Set ℂ)] (fun z => p z / q z) ∧
      divisor p univ = (divisor f univ)⁺ ∧
      divisor q univ = (divisor f univ)⁻ ∧
      (∀ z, meromorphicOrderAt p z ≠ ⊤) ∧
      (∀ z, meromorphicOrderAt q z ≠ ⊤) := by
  let D := divisor f univ
  obtain ⟨q, hq, hqD, hqfinite⟩ := exists_entire_with_nonnegative_divisor D⁻ (negPart_nonneg D)
  have hfU : MeromorphicOn f univ := hf.meromorphicOn
  have hqU : MeromorphicOn q univ := fun z _ => (hq.analyticAt z).meromorphicAt
  have hprod : MeromorphicOn (f * q) univ := hfU.mul hqU
  let p := toMeromorphicNFOn (f * q) univ
  have hpNF : MeromorphicNFOn p univ := meromorphicNFOn_toMeromorphicNFOn _ _
  have hpD : divisor p univ = D⁺ := by
    rw [show p = toMeromorphicNFOn (f * q) univ from rfl,
      hprod.divisor_of_toMeromorphicNFOn,
      divisor_mul hfU hqU (fun z _ => hfinite z) (fun z _ => hqfinite z), hqD]
    exact (eq_add_of_sub_eq (posPart_sub_negPart D)).symm
  have hp : Differentiable ℂ p := by
    apply Complex.analyticOnNhd_univ_iff_differentiable.mp
    apply hpNF.divisor_nonneg_iff_analyticOnNhd.mp
    rw [hpD]
    exact posPart_nonneg D
  have hpfinite (z : ℂ) : meromorphicOrderAt p z ≠ ⊤ := by
    rw [show p = toMeromorphicNFOn (f * q) univ from rfl,
      meromorphicOrderAt_toMeromorphicNFOn hprod (mem_univ z),
      meromorphicOrderAt_mul (hf z) (hq.analyticAt z).meromorphicAt]
    exact WithTop.add_ne_top.mpr ⟨hfinite z, hqfinite z⟩
  refine ⟨p, q, hp, hq, ?_, ?_, hpD, hqD, hpfinite, hqfinite⟩
  · intro z
    rcases le_total (D z) 0 with hz | hz
    · left
      apply entire_ne_zero_of_divisor_zero hp (hpfinite z)
      rw [hpD]
      simpa using posPart_eq_zero.mpr hz
    · right
      apply entire_ne_zero_of_divisor_zero hq (hqfinite z)
      rw [hqD]
      simpa using negPart_eq_zero.mpr hz
  · filter_upwards [toMeromorphicNFOn_eqOn_codiscrete hprod,
      MeromorphicAt.MeromorphicOn.codiscreteWithin_setOfPred_ne_zero hqU (fun z _ => hqfinite z)]
        with z hzp hzq
    change f z * q z = p z at hzp
    exact (eq_div_iff hzq).mpr hzp

/-- Every globally meromorphic scalar function has a reduced entire pair.
The identically zero meromorphic germ is handled explicitly as (0,1). -/
theorem global_reduced_pair_of_meromorphic {f : ℂ → ℂ} (hf : Meromorphic f) :
    ∃ p q : ℂ → ℂ, Differentiable ℂ p ∧ Differentiable ℂ q ∧
      (∀ z, p z ≠ 0 ∨ q z ≠ 0) ∧
      f =ᶠ[codiscreteWithin (univ : Set ℂ)] (fun z => p z / q z) ∧
      divisor p univ = (divisor f univ)⁺ ∧
      divisor q univ = (divisor f univ)⁻ ∧
      ∀ z, meromorphicOrderAt q z ≠ ⊤ := by
  by_cases hn : ∃ z, meromorphicOrderAt f z ≠ ⊤
  · obtain ⟨p, q, hp, hq, hred, he, hpD, hqD, _, hqfin⟩ :=
      global_reduced_pair_of_finite_orders hf (hf.exists_meromorphicOrderAt_ne_top_iff_forall.mp hn)
    exact ⟨p, q, hp, hq, hred, he, hpD, hqD, hqfin⟩
  · have htop (z : ℂ) : meromorphicOrderAt f z = ⊤ := by
      by_contra h
      exact hn ⟨z, h⟩
    have hD : divisor f univ = 0 := by
      ext z
      rw [hf.meromorphicOn.divisor_apply (mem_univ z), htop]
      rfl
    refine ⟨0, 1, by fun_prop, by fun_prop, fun z => Or.inr one_ne_zero, ?_, ?_, ?_, ?_⟩
    · filter_upwards [hf.meromorphicOn.analyticAt_mem_codiscreteWithin] with z hz
      simp only [Pi.zero_apply, Pi.one_apply, zero_div]
      by_contra hne
      have ho : meromorphicOrderAt f z = 0 := by
        rw [hz.meromorphicOrderAt_eq, hz.analyticOrderAt_eq_zero.mpr hne]
        rfl
      rw [htop] at ho
      exact WithTop.top_ne_zero ho
    · simp [hD]
    · simp [hD]
    · intro z
      simp

end ModifiedCartan
#print axioms ModifiedCartan.global_reduced_pair_of_finite_orders
#print axioms ModifiedCartan.global_reduced_pair_of_meromorphic
