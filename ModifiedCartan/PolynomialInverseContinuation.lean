import ModifiedCartan.MatrixCyclicOpen
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Polynomial.Roots

open scoped Classical Topology
open Filter

namespace ModifiedCartan

theorem polynomial_eq_zero_of_eventually_nat_eval_zero (p : Polynomial ℂ)
    (h : ∀ᶠ n : ℕ in atTop, p.eval (n : ℂ) = 0) : p = 0 := by
  obtain ⟨k, hk⟩ := eventually_atTop.mp h
  let f : Fin (p.natDegree + 1) → ℂ := fun i => ((k + i.val : ℕ) : ℂ)
  have hf : Function.Injective f := by
    intro i j hij
    have he : k + i.val = k + j.val := Nat.cast_injective hij
    apply Fin.ext
    omega
  apply p.eq_zero_of_natDegree_lt_card_of_eval_eq_zero hf
  · intro i
    exact hk (k + i.val) (by omega)
  · simp

theorem polynomial_eq_zero_of_eventually_inverse_eval_zero (p : Polynomial ℂ)
    (h : ∀ᶠ t in 𝓝 (0 : ℂ), t ≠ 0 → p.eval t⁻¹ = 0) : p = 0 := by
  apply polynomial_eq_zero_of_eventually_nat_eval_zero
  have hn := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)).eventually h
  filter_upwards [hn, eventually_gt_atTop (0 : ℕ)] with n hn hpos
  have hc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hpos)
  simpa only [inv_inv] using hn (inv_ne_zero hc)

end ModifiedCartan


