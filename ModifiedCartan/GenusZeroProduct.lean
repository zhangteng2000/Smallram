import ModifiedCartan.RootMajorantProduct
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Complex.LocallyUniformLimit

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- The actual genus-zero product from `lem:small-order-coordinates`.
Its root index is fixed independently of any auxiliary growth exponent. -/
noncomputable def genusZeroProduct (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∏' a : entireZeroCopies f, (1 - z / a.1)

theorem genusZero_factors_multipliable {f : ℂ → ℂ}
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹)) (z : ℂ) :
    Multipliable (fun a : entireZeroCopies f => 1 - z / a.1) := by
  have hh : Summable (fun a : entireZeroCopies f => ‖-(z / a.1)‖) := by
    simpa only [norm_neg, norm_div, div_eq_mul_inv, norm_mul, norm_inv] using! hs.mul_left ‖z‖
  simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable hh

theorem genusZero_hasProdUniformlyOn {f : ℂ → ℂ}
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹)) {K : Set ℂ}
    (hK : IsCompact K) :
    HasProdUniformlyOn (fun a : entireZeroCopies f => fun z => 1 - z / a.1)
      (genusZeroProduct f) K := by
  obtain ⟨R, _, hR⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  have hb : ∀ᶠ a : entireZeroCopies f in cofinite, ∀ z ∈ K, ‖-(z / a.1)‖ ≤ R * ‖a.1‖⁻¹ := by
    apply Filter.Eventually.of_forall
    intro a z hz
    have hzR : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hR hz
    rw [norm_neg, norm_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hzR (inv_nonneg.mpr (norm_nonneg _))
  change HasProdUniformlyOn (fun a : entireZeroCopies f => fun z => 1 - z / a.1)
    (fun z => ∏' a : entireZeroCopies f, (1 - z / a.1)) K
  simpa only [sub_eq_add_neg] using!
    (hs.mul_left R).hasProdUniformlyOn_one_add hK hb (fun a => by fun_prop)

theorem genusZero_hasProdLocallyUniformlyOn {f : ℂ → ℂ}
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹)) :
    HasProdLocallyUniformlyOn (fun a : entireZeroCopies f => fun z => 1 - z / a.1)
      (genusZeroProduct f) univ :=
  hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
    (fun _ _ hK => genusZero_hasProdUniformlyOn hs hK)

theorem genusZeroProduct_differentiable {f : ℂ → ℂ}
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹)) :
    Differentiable ℂ (genusZeroProduct f) := by
  have ht : TendstoLocallyUniformlyOn
      (fun S : Finset (entireZeroCopies f) => fun z => ∏ a ∈ S, (1 - z / a.1))
      (genusZeroProduct f) atTop univ := genusZero_hasProdLocallyUniformlyOn hs
  apply differentiableOn_univ.mp
  apply ht.differentiableOn _ isOpen_univ
  exact Filter.Eventually.of_forall (fun S =>
    DifferentiableOn.fun_finsetProd (fun a _ => by fun_prop))

theorem genusZeroProduct_zero (f : ℂ → ℂ) : genusZeroProduct f 0 = 1 := by
  simp [genusZeroProduct]

theorem genusZeroProduct_norm_le_rootMajorant {f : ℂ → ℂ}
    (hs : Summable (fun a : entireZeroCopies f => ‖a.1‖⁻¹)) (z : ℂ) :
    ‖genusZeroProduct f z‖ ≤ rootMajorantProduct f ‖z‖ := by
  classical
  apply le_of_tendsto_of_tendsto (genusZero_factors_multipliable hs z).hasProd.norm
    (rootMajorant_multipliable hs ‖z‖).hasProd
  exact Filter.Eventually.of_forall (fun S => by
    dsimp only
    apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    intro a _
    simpa only [norm_one, norm_div] using norm_sub_le (1 : ℂ) (z / a.1))

end ModifiedCartan
#print axioms ModifiedCartan.genusZeroProduct_differentiable
#print axioms ModifiedCartan.genusZeroProduct_norm_le_rootMajorant
