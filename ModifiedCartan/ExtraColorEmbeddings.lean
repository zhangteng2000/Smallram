import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Embedding.Basic

open scoped Classical

namespace ModifiedCartan
noncomputable section

variable {A B : Type*} [DecidableEq A]

def extraColorAt (a : A) (f : {i : A // i ≠ a} ↪ B) : A ↪ Option B :=
  (Equiv.optionSubtypeNe a).symm.toEmbedding.trans f.optionMap

theorem extraColorAt_self (a : A) (f : {i : A // i ≠ a} ↪ B) :
    extraColorAt a f a = none := by
  simp [extraColorAt, Equiv.optionSubtypeNe_symm_self]

theorem extraColorAt_of_ne (a : A) (f : {i : A // i ≠ a} ↪ B) (i : A) (hi : i ≠ a) :
    extraColorAt a f i = some (f ⟨i, hi⟩) := by
  simp [extraColorAt, Equiv.optionSubtypeNe_symm_of_ne hi]

theorem extraColorAt_eq_none_iff (a : A) (f : {i : A // i ≠ a} ↪ B) (i : A) :
    extraColorAt a f i = none ↔ i = a := by
  constructor
  · intro hi
    exact (extraColorAt a f).injective (hi.trans (extraColorAt_self a f).symm)
  · intro hi
    subst i
    exact extraColorAt_self a f

def extraColorEmbedding : (A ↪ B) ⊕ (Σ a : A, {i : A // i ≠ a} ↪ B) → (A ↪ Option B)
  | .inl f => f.trans Function.Embedding.some
  | .inr ⟨a, f⟩ => extraColorAt a f

theorem extraColorEmbedding_injective :
    Function.Injective (extraColorEmbedding (A := A) (B := B)) := by
  intro x y he
  rcases x with f | ⟨a, f⟩ <;> rcases y with g | ⟨b, g⟩
  · have hfg : f = g := by
      apply Function.Embedding.ext
      intro i
      exact Option.some.inj (congrArg (fun F : A ↪ Option B => F i) he)
    exact congrArg Sum.inl hfg
  · have hh := congrArg (fun F : A ↪ Option B => F b) he
    change some (f b) = extraColorAt b g b at hh
    rw [extraColorAt_self] at hh
    cases hh
  · have hh := congrArg (fun F : A ↪ Option B => F a) he
    change extraColorAt a f a = some (g a) at hh
    rw [extraColorAt_self] at hh
    cases hh
  · change extraColorAt a f = extraColorAt b g at he
    have hab : a = b := (extraColorAt_eq_none_iff b g a).mp
      ((congrArg (fun F : A ↪ Option B => F a) he).symm.trans (extraColorAt_self a f))
    subst b
    have hfg : f = g := by
      apply Function.Embedding.ext
      intro i
      apply Option.some.inj
      simpa only [extraColorAt_of_ne a f i.val i.property,
        extraColorAt_of_ne a g i.val i.property] using
          congrArg (fun F : A ↪ Option B => F i.val) he
    exact congrArg (fun q => Sum.inr (⟨a, q⟩ : Σ a : A, {i : A // i ≠ a} ↪ B)) hfg

end
end ModifiedCartan


