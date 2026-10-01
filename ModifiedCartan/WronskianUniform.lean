import FewInflection.TaylorLimits
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem locallyUniform_complex_finset_sum {ι κ : Type*} {p : Filter ι}
    {U : Set ℂ} (S : Finset κ) {F : κ → ι → ℂ → ℂ} {g : κ → ℂ → ℂ}
    (h : ∀ k ∈ S, TendstoLocallyUniformlyOn (F k) (g k) p U) :
    TendstoLocallyUniformlyOn (fun ν z => ∑ k ∈ S, F k ν z) (fun z => ∑ k ∈ S, g k z) p U := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using
        (tendsto_const_nhds (x := (0 : ℂ)) (f := p)).tendstoUniformlyOn_const U |>.tendstoLocallyUniformlyOn
  | @insert k S hk ih =>
      simpa only [Finset.sum_insert hk, Pi.add_apply] using!
        (h k (Finset.mem_insert_self k S)).add
          (ih (fun l hl => h l (Finset.mem_insert_of_mem hl)))

theorem locallyUniform_complex_finset_prod {ι κ : Type*} {p : Filter ι}
    {U : Set ℂ} (S : Finset κ) {F : κ → ι → ℂ → ℂ} {g : κ → ℂ → ℂ}
    (h : ∀ k ∈ S, TendstoLocallyUniformlyOn (F k) (g k) p U)
    (hg : ∀ k ∈ S, ContinuousOn (g k) U) :
    TendstoLocallyUniformlyOn (fun ν z => ∏ k ∈ S, F k ν z) (fun z => ∏ k ∈ S, g k z) p U := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa only [Finset.prod_empty] using
        (tendsto_const_nhds (x := (1 : ℂ)) (f := p)).tendstoUniformlyOn_const U |>.tendstoLocallyUniformlyOn
  | @insert k S hk ih =>
      have hS : ∀ l ∈ S, ContinuousOn (g l) U := fun l hl => hg l (Finset.mem_insert_of_mem hl)
      simpa only [Finset.prod_insert hk, Pi.mul_apply] using!
        (h k (Finset.mem_insert_self k S)).mul₀
          (ih (fun l hl => h l (Finset.mem_insert_of_mem hl)) hS)
          (hg k (Finset.mem_insert_self k S)) (continuousOn_finsetProd _ hS)

set_option backward.isDefEq.respectTransparency false in
/-- Locally uniform, rather than merely pointwise, convergence of Taylor
Wronskians, used in Step 3 of LaTeX `lem:entire-majorant`. -/
theorem taylorWronskian_tendstoLocallyUniformlyOn {n : ℕ}
    {y : Fin (n + 1) → ℂ → ℂ} (hy : ∀ j, Differentiable ℂ (y j)) :
    TendstoLocallyUniformlyOn
      (fun N => FewInflection.wronskian n
        (fun j z => (FewInflection.taylorPolynomial (y j) 0 N).eval z))
      (FewInflection.wronskian n y) atTop univ := by
  classical
  have hder (i j : Fin (n + 1)) : TendstoLocallyUniformlyOn
      (fun N => iteratedDeriv i.val (fun z => (FewInflection.taylorPolynomial (y j) 0 N).eval z))
      (iteratedDeriv i.val (y j)) atTop univ :=
    FewInflection.tendstoLocallyUniformlyOn_iteratedDeriv_of_differentiableOn isOpen_univ
      (FewInflection.tendstoLocallyUniformlyOn_taylorPolynomial_eval_of_entire (hy j) 0)
      (Filter.Eventually.of_forall (fun N =>
        (FewInflection.taylorPolynomial (y j) 0 N).differentiableOn)) i.val
  have hc (i j : Fin (n + 1)) : ContinuousOn (iteratedDeriv i.val (y j)) univ := by
    simpa only [iteratedDeriv_eq_iterate] using
      ((Complex.analyticOnNhd_univ_iff_differentiable.mpr (hy j)).iterated_deriv i.val).continuousOn
  change TendstoLocallyUniformlyOn
    (fun N z => FewInflection.wronskian n
      (fun j w => (FewInflection.taylorPolynomial (y j) 0 N).eval w) z)
    (fun z => FewInflection.wronskian n y z) atTop univ
  simp_rw [FewInflection.wronskian, Matrix.det_apply']
  apply locallyUniform_complex_finset_sum
  intro σ _
  apply TendstoLocallyUniformlyOn.mul₀
    ((tendsto_const_nhds.tendstoUniformlyOn_const univ).tendstoLocallyUniformlyOn)
    (locallyUniform_complex_finset_prod Finset.univ (fun i _ => hder (σ i) i) (fun i _ => hc (σ i) i))
    continuousOn_const
    (continuousOn_finsetProd _ (fun i _ => hc (σ i) i))

end ModifiedCartan
#print axioms ModifiedCartan.taylorWronskian_tendstoLocallyUniformlyOn
