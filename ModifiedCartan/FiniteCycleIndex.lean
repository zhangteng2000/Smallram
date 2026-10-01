import ModifiedCartan.WeightedColoringBurnside
import ModifiedCartan.FiniteCyclePolynomials
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem finiteCyclePolynomial_average {A B : Type*} [Fintype A] [Fintype B] :
    MvPolynomial.C ((Nat.card (Equiv.Perm A) : ℂ)⁻¹) *
      (∑ σ : Equiv.Perm A, finiteCyclePolynomial B σ) =
        MvPolynomial.hsymm B ℂ (Fintype.card A) := by
  have hs := sum_permutationFixedColoringSum (A := A)
    (fun b : B => (MvPolynomial.X b : MvPolynomial B ℂ))
  change (∑ σ : Equiv.Perm A, finiteCyclePolynomial B σ) =
    Fintype.card (Equiv.Perm A) • MvPolynomial.hsymm B ℂ (Fintype.card A) at hs
  rw [hs, Nat.card_eq_fintype_card, nsmul_eq_mul]
  have hn : (Fintype.card (Equiv.Perm A) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := Equiv.Perm A)
  have hc : (Fintype.card (Equiv.Perm A) : MvPolynomial B ℂ) =
      MvPolynomial.C (Fintype.card (Equiv.Perm A) : ℂ) := (map_natCast _ _).symm
  rw [hc, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hn, map_one, one_mul]

end
end ModifiedCartan


