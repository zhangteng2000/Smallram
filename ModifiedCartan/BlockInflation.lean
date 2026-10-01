import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.BigOperators

open scoped Classical

namespace ModifiedCartan
noncomputable section

def blockHeadEquiv {A : Type*} (κ : A → ℕ) :
    A ≃ {p : (Σ a, Fin (κ a + 1)) // p.2.val = 0} where
  toFun a := ⟨⟨a, 0⟩, rfl⟩
  invFun p := p.val.1
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨⟨a, i⟩, hi⟩
    apply Subtype.ext
    have he : i = 0 := Fin.ext hi
    subst i
    rfl

def blockHeadPermutation {A : Type*} (κ : A → ℕ) (σ : Equiv.Perm A) :
    Equiv.Perm (Σ a, Fin (κ a + 1)) := σ.extendDomain (blockHeadEquiv κ)

theorem blockHeadPermutation_head {A : Type*} (κ : A → ℕ) (σ : Equiv.Perm A) (a : A) :
    blockHeadPermutation κ σ ⟨a, 0⟩ = ⟨σ a, 0⟩ :=
  Equiv.Perm.extendDomain_apply_image σ (blockHeadEquiv κ) a

theorem blockHeadPermutation_other {A : Type*} (κ : A → ℕ) (σ : Equiv.Perm A)
    (p : Σ a, Fin (κ a + 1)) (hp : p.2.val ≠ 0) : blockHeadPermutation κ σ p = p :=
  Equiv.Perm.extendDomain_apply_not_subtype σ (blockHeadEquiv κ) hp

/-- Replace each letter a by a consecutive block of kappa(a)+1 letters,
and join the end of block a to the start of block sigma(a). -/
def blockInflation {A : Type*} (κ : A → ℕ) (σ : Equiv.Perm A) :
    Equiv.Perm (Σ a, Fin (κ a + 1)) :=
  blockHeadPermutation κ σ * Equiv.Perm.sigmaCongrRight (fun a => finRotate (κ a + 1))

theorem blockInflation_internal {A : Type*} (κ : A → ℕ) (σ : Equiv.Perm A)
    (a : A) (i : ℕ) (hi : i < κ a) :
    blockInflation κ σ ⟨a, ⟨i, by omega⟩⟩ = ⟨a, ⟨i + 1, by omega⟩⟩ := by
  change blockHeadPermutation κ σ ⟨a, finRotate (κ a + 1) ⟨i, _⟩⟩ = _
  rw [finRotate_of_lt hi]
  exact blockHeadPermutation_other κ σ _ (by simp)

theorem blockInflation_last {A : Type*} (κ : A → ℕ) (σ : Equiv.Perm A) (a : A) :
    blockInflation κ σ ⟨a, Fin.last (κ a)⟩ = ⟨σ a, 0⟩ := by
  change blockHeadPermutation κ σ ⟨a, finRotate (κ a + 1) (Fin.last (κ a))⟩ = _
  rw [finRotate_last]
  exact blockHeadPermutation_head κ σ a

theorem blockInflation_pow_head {A : Type*} (κ : A → ℕ) (σ : Equiv.Perm A)
    (a : A) (i : ℕ) (hi : i ≤ κ a) :
    (blockInflation κ σ ^ i) ⟨a, 0⟩ = ⟨a, ⟨i, by omega⟩⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega)]
    exact blockInflation_internal κ σ a i (by omega)

theorem blockInflation_block_step {A : Type*} (κ : A → ℕ) (σ : Equiv.Perm A) (a : A) :
    (blockInflation κ σ ^ (κ a + 1)) ⟨a, 0⟩ = ⟨σ a, 0⟩ := by
  rw [pow_succ', Equiv.Perm.mul_apply, blockInflation_pow_head κ σ a (κ a) le_rfl]
  exact blockInflation_last κ σ a

theorem blockInflation_injective {A : Type*} (κ : A → ℕ) :
    Function.Injective (blockInflation κ) := by
  intro σ τ he
  apply Equiv.ext
  intro a
  have hp := congrArg (fun p : Equiv.Perm (Σ a, Fin (κ a + 1)) => p ⟨a, Fin.last (κ a)⟩) he
  rw [blockInflation_last, blockInflation_last] at hp
  exact congrArg Sigma.fst hp

end
end ModifiedCartan

