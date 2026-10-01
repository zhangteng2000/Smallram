import ModifiedCartan.GenusZeroProduct

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- A subproduct of the fixed actual zero index, used to isolate a
finite root fiber in `lem:small-order-coordinates`. -/
noncomputable def genusZeroSubproduct (f : ℂ → ℂ) (S : Set (entireZeroCopies f)) (z : ℂ) : ℂ :=
  ∏' a : S, (1 - z / a.val.1)

theorem genusZeroSubproduct_multipliable {f : ℂ → ℂ}
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹))
    (S : Set (entireZeroCopies f)) (z : ℂ) :
    Multipliable (fun a : S => 1 - z / a.val.1) := by
  have hh : Summable (fun a : S => ‖-(z / a.val.1)‖) := by
    simpa only [norm_neg, norm_div, div_eq_mul_inv, norm_mul, norm_inv, Function.comp_apply] using!
      (hs.subtype S).mul_left ‖z‖
  simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable hh

theorem genusZeroSubproduct_differentiable {f : ℂ → ℂ}
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹))
    (S : Set (entireZeroCopies f)) : Differentiable ℂ (genusZeroSubproduct f S) := by
  have hlocal : HasProdLocallyUniformlyOn (fun a : S => fun z => 1 - z / a.val.1)
      (genusZeroSubproduct f S) univ := by
    apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
    intro K _ hK
    obtain ⟨R, _, hR⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
    have hb : ∀ᶠ a : S in cofinite, ∀ z ∈ K, ‖-(z / a.val.1)‖ ≤ R * ‖a.val.1‖⁻¹ := by
      apply Filter.Eventually.of_forall
      intro a z hz
      have hzR : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hR hz
      rw [norm_neg, norm_div, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hzR (inv_nonneg.mpr (norm_nonneg _))
    change HasProdUniformlyOn (fun a : S => fun z => 1 - z / a.val.1)
      (fun z => ∏' a : S, (1 - z / a.val.1)) K
    simpa only [sub_eq_add_neg, Function.comp_apply] using!
      ((hs.subtype S).mul_left R).hasProdUniformlyOn_one_add hK hb (fun a => by fun_prop)
  have ht : TendstoLocallyUniformlyOn
      (fun T : Finset S => fun z => ∏ a ∈ T, (1 - z / a.val.1))
      (genusZeroSubproduct f S) atTop univ := hlocal
  apply differentiableOn_univ.mp
  apply ht.differentiableOn _ isOpen_univ
  exact Filter.Eventually.of_forall (fun T =>
    DifferentiableOn.fun_finsetProd (fun a _ => by fun_prop))

theorem genusZeroSubproduct_mul_compl {f : ℂ → ℂ}
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹))
    (S : Set (entireZeroCopies f)) (z : ℂ) :
    genusZeroSubproduct f S z * genusZeroSubproduct f Sᶜ z = genusZeroProduct f z := by
  exact Multipliable.tprod_mul_tprod_compl
    (f := fun a : entireZeroCopies f => 1 - z / a.1) (s := S)
    (genusZeroSubproduct_multipliable hs S z)
    (genusZeroSubproduct_multipliable hs Sᶜ z)

theorem genusZeroSubproduct_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹))
    (S : Set (entireZeroCopies f)) {z : ℂ} (hz : ∀ a ∈ S, z ≠ a.1) :
    genusZeroSubproduct f S z ≠ 0 := by
  have hsum : Summable (fun a : S => ‖-(z / a.val.1)‖) := by
    simpa only [norm_neg, norm_div, div_eq_mul_inv, norm_mul, norm_inv, Function.comp_apply] using!
      (hs.subtype S).mul_left ‖z‖
  have hfactor (a : S) : 1 + -(z / a.val.1) ≠ 0 := by
    rw [← sub_eq_add_neg, sub_ne_zero]
    intro he
    exact hz a.val a.property
      ((div_eq_one_iff_eq (entireZeroCopies_ne_zero hf h0 a.val)).mp he.symm)
  simpa only [sub_eq_add_neg, genusZeroSubproduct] using tprod_one_add_ne_zero_of_summable hfactor hsum

end ModifiedCartan
#print axioms ModifiedCartan.genusZeroSubproduct_differentiable
#print axioms ModifiedCartan.genusZeroSubproduct_mul_compl
