import ModifiedCartan.WeightedZeroCounting

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem analyticOrderAt_translate_sub (f : ℂ → ℂ) (b z : ℂ) :
    analyticOrderAt (fun w => f (w - b)) z = analyticOrderAt f (z - b) := by
  have hd : HasDerivAt (fun w : ℂ => w - b) 1 z := (hasDerivAt_id z).sub_const b
  simpa only [Function.comp_def] using analyticOrderAt_comp_of_deriv_ne_zero
    (f := f) (g := fun w : ℂ => w - b) (by fun_prop) (by rw [hd.deriv]; exact one_ne_zero)

/-- Translation of the actual repeated-zero index, preserving every
analytic multiplicity, including roots moved to the origin. -/
def zeroCopiesTranslateEquiv (f : ℂ → ℂ) (b : ℂ) :
    entireZeroCopies f ≃ entireZeroCopies (fun z => f (z - b)) where
  toFun a := ⟨a.1 + b, ⟨a.2.val, by
    simpa only [analyticOrderAt_translate_sub, add_sub_cancel_right] using a.2.isLt⟩⟩
  invFun a := ⟨a.1 - b, ⟨a.2.val, by
    simpa only [analyticOrderAt_translate_sub] using a.2.isLt⟩⟩
  left_inv := by
    rintro ⟨z, ⟨i, hi⟩⟩
    change (Sigma.mk (z + b - b) ⟨i, _⟩ : entireZeroCopies f) = Sigma.mk z ⟨i, hi⟩
    apply Sigma.ext (add_sub_cancel_right z b)
    exact (Fin.heq_ext_iff (congrArg (fun w => (analyticOrderAt f w).toNat)
      (add_sub_cancel_right z b))).mpr rfl
  right_inv := by
    rintro ⟨z, ⟨i, hi⟩⟩
    change (Sigma.mk (z - b + b) ⟨i, _⟩ : entireZeroCopies (fun w => f (w - b))) =
      Sigma.mk z ⟨i, hi⟩
    apply Sigma.ext (sub_add_cancel z b)
    exact (Fin.heq_ext_iff (congrArg (fun w => (analyticOrderAt (fun v => f (v - b)) w).toNat)
      (sub_add_cancel z b))).mpr rfl

theorem translated_zeroCopy_weights_summable {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (b : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    Summable (fun a : entireZeroCopies f => rootCountingWeight R (a.1 + b)) := by
  have hg : Differentiable ℂ (fun z => f (z - b)) := hf.comp (by fun_prop)
  have hs : Summable (fun a : entireZeroCopies (fun z => f (z - b)) => rootCountingWeight R a.1) :=
    summable_of_hasFiniteSupport (zeroCopy_weight_hasFiniteSupport hg hR)
  simpa only [zeroCopiesTranslateEquiv, Equiv.coe_fn_mk, Function.comp_apply] using!
    hs.comp_injective (zeroCopiesTranslateEquiv f b).injective

theorem translated_logCounting_eq_tsum {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (b : ℂ) {R : ℝ} (hR : 0 < R) :
    ValueDistribution.logCounting (fun z => f (z - b)) (0 : WithTop ℂ) R =
      ∑' a : entireZeroCopies f, rootCountingWeight R (a.1 + b) := by
  have hg : Differentiable ℂ (fun z => f (z - b)) := hf.comp (by fun_prop)
  rw [entire_logCounting_eq_tsum_weights hg hR]
  simpa only [zeroCopiesTranslateEquiv, Equiv.coe_fn_mk] using!
    ((zeroCopiesTranslateEquiv f b).tsum_eq
      (fun a : entireZeroCopies (fun z => f (z - b)) => rootCountingWeight R a.1)).symm

end ModifiedCartan
#print axioms ModifiedCartan.zeroCopiesTranslateEquiv
#print axioms ModifiedCartan.translated_logCounting_eq_tsum
