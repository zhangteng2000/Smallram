import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Fintype.Sigma

open scoped Classical

namespace ModifiedCartan
noncomputable section

def sigmaFiberPermutation {A : Type*} [Fintype A] [DecidableEq A] (B : A → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    (a : A) (σ : Equiv.Perm (B a)) : Equiv.Perm (Σ a, B a) :=
  σ.viaFintypeEmbedding (Function.Embedding.sigmaMk a)

theorem sigmaFiberPermutation_same {A : Type*} [Fintype A] [DecidableEq A] (B : A → Type*)
    [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (a : A) (σ : Equiv.Perm (B a)) (b : B a) :
    sigmaFiberPermutation B a σ ⟨a, b⟩ = ⟨a, σ b⟩ :=
  Equiv.Perm.viaFintypeEmbedding_apply_image σ (Function.Embedding.sigmaMk a) b

theorem sigmaFiberPermutation_other {A : Type*} [Fintype A] [DecidableEq A] (B : A → Type*)
    [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (a c : A) (σ : Equiv.Perm (B a)) (b : B c) (hac : c ≠ a) :
    sigmaFiberPermutation B a σ ⟨c, b⟩ = ⟨c, b⟩ := by
  apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
  rintro ⟨d, hd⟩
  exact hac (congrArg Sigma.fst hd).symm

theorem sigmaFiberPermutation_sign {A : Type*} [Fintype A] [DecidableEq A] (B : A → Type*)
    [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (a : A) (σ : Equiv.Perm (B a)) :
    Equiv.Perm.sign (sigmaFiberPermutation B a σ) = Equiv.Perm.sign σ :=
  Equiv.Perm.viaFintypeEmbedding_sign σ (Function.Embedding.sigmaMk a)

theorem sigmaFiberPermutation_list_apply {A : Type*} [Fintype A] [DecidableEq A] (B : A → Type*)
    [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (σ : ∀ a, Equiv.Perm (B a)) (l : List A) (hl : l.Nodup)
    (a : A) (b : B a) :
    (l.map (fun c => sigmaFiberPermutation B c (σ c))).prod ⟨a, b⟩ =
      if a ∈ l then ⟨a, σ a b⟩ else ⟨a, b⟩ := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, ih (List.nodup_cons.mp hl).2]
    by_cases hal : a ∈ l
    · have hac : a ≠ c := fun h => (List.nodup_cons.mp hl).1 (h ▸ hal)
      simp only [if_pos hal, sigmaFiberPermutation_other B c a (σ c) (σ a b) hac,
        List.mem_cons, hal, or_true, if_true]
    · rw [if_neg hal]
      by_cases hac : a = c
      · subst c
        rw [sigmaFiberPermutation_same]
        simp
      · rw [sigmaFiberPermutation_other B c a (σ c) b hac]
        simp [hac, hal]

theorem sigmaFiberPermutation_list_product {A : Type*} [Fintype A] [DecidableEq A] (B : A → Type*)
    [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (σ : ∀ a, Equiv.Perm (B a)) (l : List A) (hl : l.Nodup)
    (hall : ∀ a, a ∈ l) :
    (l.map (fun c => sigmaFiberPermutation B c (σ c))).prod = Equiv.Perm.sigmaCongrRight σ := by
  apply Equiv.ext
  rintro ⟨a, b⟩
  rw [sigmaFiberPermutation_list_apply B σ l hl a b, if_pos (hall a)]
  rfl

end
end ModifiedCartan

