import ModifiedCartan.ExtraColorEmbeddings
import Mathlib.Tactic.Choose

open scoped Classical

namespace ModifiedCartan
noncomputable section

variable {A B : Type*} [DecidableEq A]

theorem extraColorEmbedding_surjective :
    Function.Surjective (extraColorEmbedding (A := A) (B := B)) := by
  intro f
  by_cases hn : ∃ a : A, f a = none
  · obtain ⟨a, ha⟩ := hn
    have hg : ∀ i : {i : A // i ≠ a}, ∃ b : B, f i.val = some b := by
      intro i
      cases hi : f i.val with
      | none => exact False.elim (i.property (f.injective (hi.trans ha.symm)))
      | some b => exact ⟨b, rfl⟩
    choose g hg using hg
    let G : {i : A // i ≠ a} ↪ B := ⟨g, by
      intro i j he
      apply Subtype.ext
      exact f.injective ((hg i).trans ((congrArg some he).trans (hg j).symm))⟩
    refine ⟨.inr ⟨a, G⟩, ?_⟩
    apply Function.Embedding.ext
    intro i
    change extraColorAt a G i = f i
    by_cases hi : i = a
    · subst i
      rw [extraColorAt_self]
      exact ha.symm
    · rw [extraColorAt_of_ne a G i hi]
      exact (hg ⟨i, hi⟩).symm
  · have hg : ∀ a : A, ∃ b : B, f a = some b := by
      intro a
      cases ha : f a with
      | none => exact False.elim (hn ⟨a, ha⟩)
      | some b => exact ⟨b, rfl⟩
    choose g hg using hg
    let G : A ↪ B := ⟨g, by
      intro a b he
      exact f.injective ((hg a).trans ((congrArg some he).trans (hg b).symm))⟩
    refine ⟨.inl G, ?_⟩
    apply Function.Embedding.ext
    intro a
    exact (hg a).symm

/-- Add one available color: it is unused, or used at exactly one position. -/
def extraColorEquiv : (A ↪ B) ⊕ (Σ a : A, {i : A // i ≠ a} ↪ B) ≃ (A ↪ Option B) :=
  Equiv.ofBijective extraColorEmbedding ⟨extraColorEmbedding_injective, extraColorEmbedding_surjective⟩

end
end ModifiedCartan


