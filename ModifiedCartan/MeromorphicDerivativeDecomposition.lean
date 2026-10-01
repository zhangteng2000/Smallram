import ModifiedCartan.CircleSingularSums
import FewInflection.Nevanlinna.PoissonKernelBounds
import Mathlib.Analysis.Meromorphic.IsolatedZeros

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem meromorphic_iteratedDeriv_on {f : ℂ → ℂ} {U : Set ℂ}
    (hf : MeromorphicOn f U) (m : ℕ) : MeromorphicOn (iteratedDeriv m f) U := by
  simpa only [iteratedDeriv_eq_iterate] using hf.iterated_deriv (n := m)

theorem iteratedDeriv_congr_codiscreteWithin {f g : ℂ → ℂ} {U : Set ℂ}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
    (heq : f =ᶠ[codiscreteWithin U] g) (m : ℕ) :
    iteratedDeriv m f =ᶠ[codiscreteWithin U] iteratedDeriv m g := by
  induction m with
  | zero => simpa only [iteratedDeriv_zero] using heq
  | succ m ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    exact (meromorphic_iteratedDeriv_on hf m).deriv_eventuallyEq_codiscreteWithin
      (meromorphic_iteratedDeriv_on hg m) ih

/-- Differentiating an actual finite principal part plus an analytic remainder
preserves the codiscrete identity, with every singular derivative explicit. -/
theorem iteratedDeriv_singular_add_analytic_eventuallyEq {f A : ℂ → ℂ} {U : Set ℂ}
    (S : Finset ℂ) (c : ℂ → ℂ) (hf : MeromorphicOn f U) (hA : AnalyticOnNhd ℂ A U)
    (heq : f =ᶠ[codiscreteWithin U] (fun z => (∑ a ∈ S, c a * (z - a)⁻¹) + A z)) (m : ℕ) :
    iteratedDeriv m f =ᶠ[codiscreteWithin U] (fun z =>
      (∑ a ∈ S, (c a * (-1 : ℂ) ^ m * (m.factorial : ℂ)) / (z - a) ^ (m + 1)) +
        iteratedDeriv m A z) := by
  have hsum : MeromorphicOn (fun z : ℂ => ∑ a ∈ S, c a * (z - a)⁻¹) U := by
    simpa only [pow_one, div_eq_mul_inv, id_eq] using
      (meromorphic_weighted_poles S id c 1).meromorphicOn (s := U)
  have hder := iteratedDeriv_congr_codiscreteWithin hf (hsum.add hA.meromorphicOn) heq m
  have hout : ∀ᶠ z in codiscreteWithin U, z ∉ (S : Set ℂ) :=
    compl_finite_mem_codiscreteWithin S.finite_toSet
  filter_upwards [hder, hout, self_mem_codiscreteWithin U] with z hz hzS hzU
  have hza : ∀ a ∈ S, a ≠ z := by
    intro a ha he
    exact hzS (he ▸ ha)
  have hsumA : AnalyticAt ℂ (fun w : ℂ => ∑ a ∈ S, c a * (w - a)⁻¹) z := by
    apply Finset.analyticAt_fun_sum
    intro a ha
    have hn : z - a ≠ 0 := sub_ne_zero.mpr (hza a ha).symm
    fun_prop
  rw [hz, iteratedDeriv_add hsumA.contDiffAt (hA z hzU).contDiffAt]
  congr 1
  simpa only [id_eq, mul_div_assoc, mul_assoc] using
    FewInflection.iteratedDeriv_singular_sum S id c m hza

end ModifiedCartan
#print axioms ModifiedCartan.iteratedDeriv_singular_add_analytic_eventuallyEq


