import ModifiedCartan.Targets
import ModifiedCartan.GenusZeroProduct
import Mathlib.Analysis.SpecialFunctions.Exp

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

theorem zeroSharp_coeff_summable :
    Summable (fun j : ℕ => ‖Complex.exp (-((j + 1 : ℕ) : ℂ))‖) := by
  have hs : Summable (fun j : ℕ => Real.exp (-((j + 1 : ℕ) : ℝ))) :=
    Real.summable_exp_neg_nat.of_nonneg_of_le
      (fun _ => (Real.exp_pos _).le) (fun j => Real.exp_monotone (by push_cast; linarith))
  simpa only [Complex.norm_exp, Complex.neg_re, Complex.natCast_re] using hs

/-- LaTeX `eq:zero-sharp-example`: convergence of the actual prescribed product. -/
theorem zeroSharp_factors_multipliable (z : ℂ) :
    Multipliable (fun j : ℕ => 1 + Complex.exp (-((j + 1 : ℕ) : ℂ)) * z) := by
  apply multipliable_one_add_of_summable
  simpa only [norm_mul] using! zeroSharp_coeff_summable.mul_right ‖z‖

theorem zeroSharp_hasProdUniformlyOn {K : Set ℂ} (hK : IsCompact K) :
    HasProdUniformlyOn (fun j : ℕ => fun z => 1 + Complex.exp (-((j + 1 : ℕ) : ℂ)) * z)
      zeroSharpFunction K := by
  obtain ⟨R, _, hR⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  apply (zeroSharp_coeff_summable.mul_right R).hasProdUniformlyOn_one_add hK
  · apply Eventually.of_forall
    intro j z hz
    have hzR : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hR hz
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hzR (norm_nonneg _)
  · intro j
    fun_prop

theorem zeroSharp_hasProdLocallyUniformlyOn :
    HasProdLocallyUniformlyOn (fun j : ℕ => fun z => 1 + Complex.exp (-((j + 1 : ℕ) : ℂ)) * z)
      zeroSharpFunction univ :=
  hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
    (fun _ _ hK => zeroSharp_hasProdUniformlyOn hK)

theorem zeroSharpFunction_differentiable : Differentiable ℂ zeroSharpFunction := by
  have ht : TendstoLocallyUniformlyOn
      (fun S : Finset ℕ => fun z => ∏ j ∈ S, (1 + Complex.exp (-((j + 1 : ℕ) : ℂ)) * z))
      zeroSharpFunction atTop univ := zeroSharp_hasProdLocallyUniformlyOn
  apply differentiableOn_univ.mp
  apply ht.differentiableOn _ isOpen_univ
  exact Eventually.of_forall (fun S => DifferentiableOn.fun_finsetProd (fun j _ => by fun_prop))

theorem zeroSharpFunction_zero : zeroSharpFunction 0 = 1 := by
  simp [zeroSharpFunction]

theorem zeroSharpFunction_root (j : ℕ) :
    zeroSharpFunction (-Complex.exp ((j + 1 : ℕ) : ℂ)) = 0 := by
  apply tprod_of_exists_eq_zero
  refine ⟨j, ?_⟩
  rw [mul_neg, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  ring

end ModifiedCartan
#print axioms ModifiedCartan.zeroSharp_hasProdLocallyUniformlyOn
#print axioms ModifiedCartan.zeroSharpFunction_differentiable
#print axioms ModifiedCartan.zeroSharpFunction_root
