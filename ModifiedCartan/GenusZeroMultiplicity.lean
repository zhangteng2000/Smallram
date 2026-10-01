import ModifiedCartan.GenusZeroSubproduct
import ModifiedCartan.GenusZeroZeros

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

/-- The actual zero-copy fiber has exactly the analytic multiplicity.
Dependency for LaTeX `lem:small-order-coordinates`. -/
def entireZeroFiberEquiv (f : ℂ → ℂ) (z : ℂ) :
    {a : entireZeroCopies f // a.1 = z} ≃ Fin (analyticOrderAt f z).toNat where
  toFun a := a.property ▸ a.val.2
  invFun i := ⟨⟨z, i⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨w, i⟩, h⟩
    dsimp only at h
    subst w
    rfl
  right_inv := by intro i; rfl

theorem genusZeroSubproduct_fiber (f : ℂ → ℂ) (z w : ℂ) :
    genusZeroSubproduct f {a | a.1 = z} w =
      (1 - w / z) ^ (analyticOrderAt f z).toNat := by
  unfold genusZeroSubproduct
  calc
    (∏' a : {a : entireZeroCopies f // a.1 = z}, (1 - w / a.val.1)) =
        ∏' _i : Fin (analyticOrderAt f z).toNat, (1 - w / z) := by
      simpa only [entireZeroFiberEquiv, Equiv.coe_fn_symm_mk] using
        ((entireZeroFiberEquiv f z).symm.tprod_eq
          (fun a : {a : entireZeroCopies f // a.1 = z} => 1 - w / a.val.1)).symm
    _ = _ := by simp [tprod_fintype]

theorem genusZeroProduct_factor_fiber {f : ℂ → ℂ}
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹)) (z w : ℂ) :
    genusZeroProduct f w = (1 - w / z) ^ (analyticOrderAt f z).toNat *
      genusZeroSubproduct f {a | a.1 = z}ᶜ w := by
  rw [← genusZeroSubproduct_mul_compl hs {a | a.1 = z} w,
    genusZeroSubproduct_fiber]

theorem genusZeroSubproduct_compl_fiber_ne_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹)) (z : ℂ) :
    genusZeroSubproduct f {a | a.1 = z}ᶜ z ≠ 0 := by
  apply genusZeroSubproduct_ne_zero hf h0 hs
  intro a ha he
  exact ha he.symm

theorem entire_analyticOrderAt_ne_top {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (z : ℂ) : analyticOrderAt f z ≠ ⊤ := by
  intro ht
  have he : f = 0 :=
    (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z (fun w => hf.analyticAt w)).mp ht
  exact h0 (congrFun he 0)

theorem analyticOrderAt_genusZeroFactor {z : ℂ} (hz : z ≠ 0) :
    analyticOrderAt (fun w : ℂ => 1 - w / z) z = 1 := by
  have ha : AnalyticAt ℂ (fun w : ℂ => 1 - w / z) z := by fun_prop
  have hd : HasDerivAt (fun w : ℂ => 1 - w / z) (-(1 / z)) z :=
    ((hasDerivAt_id z).div_const z).const_sub 1
  apply ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
  · simp [hz]
  · simp [hd.deriv, hz]

/-- The fixed actual genus-zero product preserves all zero multiplicities,
as required in LaTeX `lem:small-order-coordinates`. -/
theorem genusZeroProduct_analyticOrderAt {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹)) (z : ℂ) :
    analyticOrderAt (genusZeroProduct f) z = analyticOrderAt f z := by
  by_cases hz : z = 0
  · subst z
    rw [(hf.analyticAt 0).analyticOrderAt_eq_zero.mpr h0]
    exact ((genusZeroProduct_differentiable hs).analyticAt 0).analyticOrderAt_eq_zero.mpr
      (by rw [genusZeroProduct_zero]; exact one_ne_zero)
  have ha : AnalyticAt ℂ (fun w : ℂ => 1 - w / z) z := by fun_prop
  have hb := (genusZeroSubproduct_differentiable hs {a | a.1 = z}ᶜ).analyticAt z
  have he : genusZeroProduct f = (fun w => 1 - w / z) ^ (analyticOrderAt f z).toNat *
      genusZeroSubproduct f {a | a.1 = z}ᶜ :=
    funext (genusZeroProduct_factor_fiber hs z)
  rw [he, analyticOrderAt_mul (ha.pow _) hb, analyticOrderAt_pow ha,
    analyticOrderAt_genusZeroFactor hz,
    hb.analyticOrderAt_eq_zero.mpr (genusZeroSubproduct_compl_fiber_ne_zero hf h0 hs z)]
  simpa only [add_zero, nsmul_one] using!
    ENat.natCast_toNat (entire_analyticOrderAt_ne_top hf h0 z)

end ModifiedCartan
#print axioms ModifiedCartan.genusZeroProduct_factor_fiber
#print axioms ModifiedCartan.genusZeroProduct_analyticOrderAt
