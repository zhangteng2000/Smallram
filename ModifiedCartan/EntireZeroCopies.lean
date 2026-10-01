import ModifiedCartan.CountingIntegral
import ModifiedCartan.DivisorPolynomial
import Mathlib.Data.Set.Countable

open scoped Topology
open Filter Set Metric Function MeromorphicOn Function.locallyFinsuppWithin
set_option autoImplicit false
namespace ModifiedCartan

/-- Actual zeros repeated according to their analytic multiplicities, as
in LaTeX `lem:entire-majorant`. A regular point contributes an empty fiber. -/
abbrev entireZeroCopies (f : ℂ → ℂ) := (z : ℂ) × Fin (analyticOrderAt f z).toNat

theorem locallyFinsupp_support_countable (D : locallyFinsupp ℂ ℤ) : D.support.Countable := by
  have hc : (⋃ N : ℕ, (toClosedBall (N : ℝ) D).support).Countable :=
    countable_iUnion (fun N => ((toClosedBall (N : ℝ) D).finiteSupport (isCompact_closedBall ..)).countable)
  apply hc.mono
  intro z hz
  obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
  apply mem_iUnion.mpr ⟨N, ?_⟩
  change (toClosedBall (N : ℝ) D) z ≠ 0
  rw [toClosedBall_eval_within D (by
    simpa only [mem_closedBall, dist_zero_right, abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)] using hN)]
  exact hz

theorem entire_divisor_eq_analyticMultiplicity {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (z : ℂ) :
    divisor f univ z = ((analyticOrderAt f z).toNat : ℤ) := by
  rw [(Complex.analyticOnNhd_univ_iff_differentiable.mpr hf).divisor_apply (mem_univ z)]
  cases analyticOrderAt f z using ENat.recTopCoe <;> simp

theorem entireZeroCopies_is_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (a : entireZeroCopies f) : f a.1 = 0 := by
  by_contra hn
  have horder := (hf.analyticAt a.1).analyticOrderAt_eq_zero.mpr hn
  have hpos := a.2.isLt
  simp only [horder, ENat.toNat_zero] at hpos
  omega

theorem entireZeroCopies_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0) (a : entireZeroCopies f) : a.1 ≠ 0 := by
  intro ha
  exact h0 (ha ▸ entireZeroCopies_is_zero hf a)

theorem entireZeroCopies_mem_divisor_support {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (a : entireZeroCopies f) : a.1 ∈ (divisor f univ).support := by
  change divisor f univ a.1 ≠ 0
  rw [entire_divisor_eq_analyticMultiplicity hf]
  have hp : 0 < (analyticOrderAt f a.1).toNat := (Nat.zero_le a.2.val).trans_lt a.2.isLt
  exact_mod_cast hp.ne'

/-- Countability is proved from the actual locally finite divisor. Thus
counting measure on the root copies is sigma-finite for Tonelli. -/
theorem entireZeroCopies_countable {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Countable (entireZeroCopies f) := by
  letI : Countable (divisor f univ).support :=
    (locallyFinsupp_support_countable (divisor f univ)).to_subtype
  let e : entireZeroCopies f → (divisor f univ).support × ℕ :=
    fun a => (⟨a.1, entireZeroCopies_mem_divisor_support hf a⟩, a.2.val)
  apply Function.Injective.countable (f := e)
  rintro ⟨z, i⟩ ⟨w, j⟩ h
  have hzw : z = w := congrArg (fun p => p.1.val) h
  have hij : i.val = j.val := congrArg Prod.snd h
  subst w
  exact congrArg (Sigma.mk z) (Fin.ext hij)

end ModifiedCartan
#print axioms ModifiedCartan.entireZeroCopies_countable
