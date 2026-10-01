import ModifiedCartan.ZeroSharpProduct
import ModifiedCartan.EntireDerivativeNontrivial
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

open scoped Topology BigOperators
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem zeroSharp_real_root (j : ℕ) :
    zeroSharpFunction ((-Real.exp ((j + 1 : ℕ) : ℝ) : ℝ) : ℂ) = 0 := by
  simpa only [Complex.ofReal_neg, Complex.ofReal_exp, Complex.ofReal_natCast]
    using zeroSharpFunction_root j

theorem zeroSharp_root_injective :
    Function.Injective (fun j : ℕ => ((-Real.exp ((j + 1 : ℕ) : ℝ) : ℝ) : ℂ)) := by
  intro i j hij
  have he : Real.exp ((i + 1 : ℕ) : ℝ) = Real.exp ((j + 1 : ℕ) : ℝ) := by
    have := congrArg Complex.re hij
    simpa only [Complex.ofReal_re, neg_inj] using this
  have h := Real.exp_injective he
  exact Nat.add_right_cancel (Nat.cast_injective h)

theorem zeroSharpFunction_not_polynomial :
    ¬ ∃ p : Polynomial ℂ, ∀ z, zeroSharpFunction z = p.eval z := by
  rintro ⟨p, hp⟩
  have hi : Set.Infinite {z : ℂ | p.IsRoot z} :=
    (Set.infinite_range_of_injective zeroSharp_root_injective).mono (by
      rintro z ⟨j, rfl⟩
      change p.eval _ = 0
      rw [← hp, zeroSharp_real_root])
  have hz := p.eq_zero_of_infinite_isRoot hi
  have h := hp 0
  rw [zeroSharpFunction_zero, hz, Polynomial.eval_zero] at h
  exact one_ne_zero h

theorem zeroSharpFunction_iteratedDeriv_nonzero (m : ℕ) :
    ∃ z, iteratedDeriv m zeroSharpFunction z ≠ 0 :=
  entire_iteratedDeriv_not_identically_zero zeroSharpFunction_differentiable
    zeroSharpFunction_not_polynomial m

theorem zeroSharpFunction_real (x : ℝ) : (zeroSharpFunction (x : ℂ)).im = 0 := by
  have ht := Complex.continuous_im.tendsto (zeroSharpFunction (x : ℂ)) |>.comp
    (zeroSharp_factors_multipliable (x : ℂ)).hasProd.tendsto_prod_nat
  have he (N : ℕ) :
      (∏ j ∈ Finset.range N, (1 + Complex.exp (-((j + 1 : ℕ) : ℂ)) * (x : ℂ))) =
      ((∏ j ∈ Finset.range N, (1 + Real.exp (-((j + 1 : ℕ) : ℝ)) * x) : ℝ) : ℂ) := by
    push_cast
    rfl
  have hz : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
      (𝓝 (zeroSharpFunction (x : ℂ)).im) := by
    change Tendsto (fun N : ℕ =>
      (∏ j ∈ Finset.range N, (1 + Complex.exp (-((j + 1 : ℕ) : ℂ)) * (x : ℂ))).im)
      atTop (𝓝 (zeroSharpFunction (x : ℂ)).im) at ht
    simpa only [Function.comp_apply, he, Complex.ofReal_im] using ht
  exact tendsto_nhds_unique hz tendsto_const_nhds

theorem entire_deriv_real {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) (x : ℝ) :
    (deriv f (x : ℂ)).im = 0 := by
  have h := (hf (x : ℂ)).hasDerivAt
  have hR := h.real_of_complex.ofReal_comp
  have hR' : HasDerivAt (fun y : ℝ => f (y : ℂ))
      ((deriv f (x : ℂ)).re : ℂ) x := hR.congr_of_eventuallyEq (by
    filter_upwards [] with y
    apply Complex.ext <;> simp [hreal y])
  have he := h.comp_ofReal.unique hR'
  simpa using congrArg Complex.im he

theorem zeroSharpFunction_iteratedDeriv_entire (m : ℕ) :
    Differentiable ℂ (iteratedDeriv m zeroSharpFunction) := by
  induction m with
  | zero => exact zeroSharpFunction_differentiable
  | succ m ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem zeroSharpFunction_iteratedDeriv_real (m : ℕ) (x : ℝ) :
    (iteratedDeriv m zeroSharpFunction (x : ℂ)).im = 0 := by
  induction m generalizing x with
  | zero => exact zeroSharpFunction_real x
  | succ m ih =>
    rw [iteratedDeriv_succ]
    exact entire_deriv_real (zeroSharpFunction_iteratedDeriv_entire m) ih x

end ModifiedCartan
#print axioms ModifiedCartan.zeroSharpFunction_not_polynomial
#print axioms ModifiedCartan.zeroSharpFunction_iteratedDeriv_nonzero
#print axioms ModifiedCartan.zeroSharpFunction_iteratedDeriv_real
