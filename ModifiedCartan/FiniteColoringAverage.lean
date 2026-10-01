import ModifiedCartan.WeightedColoringBurnside
import ModifiedCartan.FiniteCyclePolynomials

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem permutationFixedColoringSum_average {A B D : Type*} [Fintype A] [Fintype B]
    (x : B → MvPolynomial D ℂ) :
    MvPolynomial.C ((Nat.card (Equiv.Perm A) : ℂ)⁻¹) *
      (∑ σ : Equiv.Perm A, permutationFixedColoringSum σ x) =
        ∑ s : Sym B (Fintype.card A), (s.val.map x).prod := by
  rw [sum_permutationFixedColoringSum, Nat.card_eq_fintype_card, nsmul_eq_mul]
  have hn : (Fintype.card (Equiv.Perm A) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := Equiv.Perm A)
  have hc : (Fintype.card (Equiv.Perm A) : MvPolynomial D ℂ) =
      MvPolynomial.C (Fintype.card (Equiv.Perm A) : ℂ) := (map_natCast _ _).symm
  rw [hc, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hn, map_one, one_mul]

end
end ModifiedCartan


