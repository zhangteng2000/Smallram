import ModifiedCartan.BlockInflation

open scoped Classical

namespace ModifiedCartan
noncomputable section

def IsBlockSuccessor {A : Type*} (κ : A → ℕ) (p : Equiv.Perm (Σ a, Fin (κ a + 1))) : Prop :=
  ∀ (a : A) (i : ℕ) (hi : i < κ a), p ⟨a, ⟨i, by omega⟩⟩ = ⟨a, ⟨i + 1, by omega⟩⟩

theorem blockInflation_isBlockSuccessor {A : Type*} (κ : A → ℕ) (σ : Equiv.Perm A) :
    IsBlockSuccessor κ (blockInflation κ σ) := blockInflation_internal κ σ

theorem blockSuccessor_end_is_head {A : Type*} (κ : A → ℕ)
    (p : Equiv.Perm (Σ a, Fin (κ a + 1))) (hp : IsBlockSuccessor κ p) (a : A) :
    (p ⟨a, Fin.last (κ a)⟩).2.val = 0 := by
  generalize he : p ⟨a, Fin.last (κ a)⟩ = q
  rcases q with ⟨b, j⟩
  by_contra hn
  have hpos : 0 < j.val := Nat.pos_of_ne_zero hn
  have hlt : j.val - 1 < κ b := by have := j.isLt; omega
  have hj : j.val - 1 + 1 = j.val := by omega
  have hi := hp b (j.val - 1) hlt
  have hi' : p ⟨b, ⟨j.val - 1, by omega⟩⟩ = ⟨b, j⟩ := by
    rw [hi]
    congr 1
    exact Fin.ext hj
  have hpoint := p.injective (he.trans hi'.symm)
  have hab : a = b := congrArg Sigma.fst hpoint
  subst b
  have hval : κ a = j.val - 1 := congrArg (fun t : Σ a, Fin (κ a + 1) => t.2.val) hpoint
  have := j.isLt
  omega

def blockSuccessorEndMap {A : Type*} (κ : A → ℕ)
    (p : Equiv.Perm (Σ a, Fin (κ a + 1))) (a : A) : A :=
  (p ⟨a, Fin.last (κ a)⟩).1

theorem blockSuccessor_end_apply {A : Type*} (κ : A → ℕ)
    (p : Equiv.Perm (Σ a, Fin (κ a + 1))) (hp : IsBlockSuccessor κ p) (a : A) :
    p ⟨a, Fin.last (κ a)⟩ = ⟨blockSuccessorEndMap κ p a, 0⟩ := by
  have h := blockSuccessor_end_is_head κ p hp a
  change p ⟨a, Fin.last (κ a)⟩ = ⟨(p ⟨a, Fin.last (κ a)⟩).1, 0⟩
  generalize he : p ⟨a, Fin.last (κ a)⟩ = q at h ⊢
  rcases q with ⟨b, i⟩
  have hi : i = 0 := Fin.ext h
  rw [hi]

theorem blockSuccessorEndMap_injective {A : Type*} (κ : A → ℕ)
    (p : Equiv.Perm (Σ a, Fin (κ a + 1))) (hp : IsBlockSuccessor κ p) :
    Function.Injective (blockSuccessorEndMap κ p) := by
  intro a b hab
  have he : p ⟨a, Fin.last (κ a)⟩ = p ⟨b, Fin.last (κ b)⟩ := by
    rw [blockSuccessor_end_apply κ p hp a, blockSuccessor_end_apply κ p hp b, hab]
  exact congrArg Sigma.fst (p.injective he)

def blockSuccessorPermutation {A : Type*} [Fintype A] (κ : A → ℕ)
    (p : Equiv.Perm (Σ a, Fin (κ a + 1))) (hp : IsBlockSuccessor κ p) : Equiv.Perm A :=
  Equiv.ofBijective (blockSuccessorEndMap κ p)
    ⟨blockSuccessorEndMap_injective κ p hp,
      Finite.surjective_of_injective (blockSuccessorEndMap_injective κ p hp)⟩

theorem blockSuccessor_reconstruction {A : Type*} [Fintype A] (κ : A → ℕ)
    (p : Equiv.Perm (Σ a, Fin (κ a + 1))) (hp : IsBlockSuccessor κ p) :
    blockInflation κ (blockSuccessorPermutation κ p hp) = p := by
  apply Equiv.ext
  rintro ⟨a, i⟩
  by_cases hi : i.val < κ a
  · rw [blockInflation_internal κ _ a i.val hi]
    exact (hp a i.val hi).symm
  · have hil : i = Fin.last (κ a) := Fin.ext (by change i.val = κ a; have := i.isLt; omega)
    rw [hil, blockInflation_last, blockSuccessor_end_apply κ p hp a]
    rfl

/-- Every permutation respecting the internal order of all blocks is obtained
uniquely by permuting their endpoints. -/
def blockSuccessorEquiv {A : Type*} [Fintype A] (κ : A → ℕ) :
    Equiv.Perm A ≃ {p : Equiv.Perm (Σ a, Fin (κ a + 1)) // IsBlockSuccessor κ p} where
  toFun σ := ⟨blockInflation κ σ, blockInflation_isBlockSuccessor κ σ⟩
  invFun p := blockSuccessorPermutation κ p.val p.property
  left_inv σ := blockInflation_injective κ (blockSuccessor_reconstruction κ _ _)
  right_inv p := Subtype.ext (blockSuccessor_reconstruction κ p.val p.property)

end
end ModifiedCartan

