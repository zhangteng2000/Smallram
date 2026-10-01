import ModifiedCartan.GenusZeroProduct
import ModifiedCartan.ExceptionalRadii

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem entire_zero_has_copy {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0) {z : ℂ} (hz : f z = 0) : ∃ a : entireZeroCopies f, a.1 = z := by
  have ht : analyticOrderAt f z ≠ ⊤ := by
    intro ht
    have he : f = 0 :=
      (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z (fun w => hf.analyticAt w)).mp ht
    exact h0 (congrFun he 0)
  have hn : analyticOrderAt f z ≠ 0 := fun he =>
    ((hf.analyticAt z).analyticOrderAt_eq_zero.mp he) hz
  have hm : 0 < (analyticOrderAt f z).toNat := by
    cases ho : analyticOrderAt f z using ENat.recTopCoe with
    | top => exact (ht ho).elim
    | coe m =>
        have hm : m ≠ 0 := by intro hm; simp [ho, hm] at hn
        simpa only [ENat.toNat_natCast] using Nat.pos_of_ne_zero hm
  exact ⟨⟨z, ⟨0, hm⟩⟩, rfl⟩

theorem genusZeroProduct_ne_zero_of_nonroot {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹)) {z : ℂ} (hz : f z ≠ 0) :
    genusZeroProduct f z ≠ 0 := by
  have hsum : Summable (fun a : entireZeroCopies f => ‖-(z / a.1)‖) := by
    simpa only [norm_neg, norm_div, div_eq_mul_inv, norm_mul, norm_inv] using! hs.mul_left ‖z‖
  have hfactor (a : entireZeroCopies f) : 1 + -(z / a.1) ≠ 0 := by
    rw [← sub_eq_add_neg, sub_ne_zero]
    intro he
    have he' : z = a.1 := (div_eq_one_iff_eq (entireZeroCopies_ne_zero hf h0 a)).mp he.symm
    exact hz (he' ▸ entireZeroCopies_is_zero hf a)
  simpa only [sub_eq_add_neg, genusZeroProduct] using tprod_one_add_ne_zero_of_summable hfactor hsum

/-- The genus-zero product has precisely the original zero set. Equality
of multiplicities is a separate next step before constructing the gauge
in LaTeX `lem:small-order-coordinates`. -/
theorem genusZeroProduct_eq_zero_iff {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹)) (z : ℂ) :
    genusZeroProduct f z = 0 ↔ f z = 0 := by
  constructor
  · intro hz
    by_contra h
    exact genusZeroProduct_ne_zero_of_nonroot hf h0 hs h hz
  · intro hz
    obtain ⟨a, ha⟩ := entire_zero_has_copy hf h0 hz
    apply tprod_of_exists_eq_zero
    refine ⟨a, ?_⟩
    rw [← ha, div_self (entireZeroCopies_ne_zero hf h0 a), sub_self]

end ModifiedCartan
#print axioms ModifiedCartan.genusZeroProduct_eq_zero_iff
