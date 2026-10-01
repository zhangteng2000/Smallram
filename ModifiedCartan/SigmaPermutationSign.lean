import ModifiedCartan.SigmaFiberPermutations
import ModifiedCartan.BlockInflation

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem sign_sigmaCongrRight {A : Type*} [Fintype A] (B : A → Type*)
    [∀ a, Fintype (B a)] [DecidableEq A] [∀ a, DecidableEq (B a)] (σ : ∀ a, Equiv.Perm (B a)) :
    Equiv.Perm.sign (Equiv.Perm.sigmaCongrRight σ) = ∏ a, Equiv.Perm.sign (σ a) := by
  obtain ⟨l, hl, hall⟩ := Finite.exists_univ_list A
  have hFin : l.toFinset = Finset.univ := by ext a; simp [hall a]
  rw [← sigmaFiberPermutation_list_product B σ l hl hall, map_list_prod, List.map_map]
  simp only [Function.comp_def, sigmaFiberPermutation_sign]
  rw [← List.prod_toFinset _ hl, hFin]

theorem blockInflation_sign {A : Type*} [Fintype A] [DecidableEq A] (κ : A → ℕ) (σ : Equiv.Perm A) :
    Equiv.Perm.sign (blockInflation κ σ) = Equiv.Perm.sign σ * (-1) ^ (∑ a, κ a) := by
  rw [blockInflation, map_mul, blockHeadPermutation, Equiv.Perm.sign_extendDomain,
    sign_sigmaCongrRight (fun a => Fin (κ a + 1)) (fun a => finRotate (κ a + 1))]
  simp only [sign_finRotate, Nat.add_sub_cancel]
  rw [Finset.prod_pow_eq_pow_sum]

end
end ModifiedCartan

