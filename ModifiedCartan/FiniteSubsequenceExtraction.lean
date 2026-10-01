import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Fin.Basic

set_option autoImplicit false
namespace ModifiedCartan

/-- Finitely many subsequence-stable properties can be obtained on one
common subsequence when each can be extracted from every subsequence. -/
theorem finite_subsequence_extraction (n : ℕ) :
    ∀ P : Fin n → (ℕ → ℕ) → Prop,
      (∀ i ρ, StrictMono ρ → ∃ σ : ℕ → ℕ, StrictMono σ ∧ P i (ρ ∘ σ)) →
      (∀ i ρ σ, P i ρ → StrictMono σ → P i (ρ ∘ σ)) →
      ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∀ i, P i ρ := by
  induction n with
  | zero =>
    intro P _ _
    exact ⟨id, strictMono_id, fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro P hextract hstable
    obtain ⟨ρ, hρ, hPρ⟩ := ih (fun i => P i.castSucc)
      (fun i => hextract i.castSucc) (fun i => hstable i.castSucc)
    obtain ⟨σ, hσ, hlast⟩ := hextract (Fin.last n) ρ hρ
    refine ⟨ρ ∘ σ, hρ.comp hσ, ?_⟩
    intro i
    by_cases hi : i.val < n
    · let j : Fin n := ⟨i.val, hi⟩
      have hij : i = j.castSucc := Fin.ext rfl
      rw [hij]
      exact hstable j.castSucc ρ σ (hPρ j) hσ
    · have hij : i = Fin.last n := Fin.ext (by change i.val = n; omega)
      rw [hij]
      exact hlast

end ModifiedCartan
#print axioms ModifiedCartan.finite_subsequence_extraction
