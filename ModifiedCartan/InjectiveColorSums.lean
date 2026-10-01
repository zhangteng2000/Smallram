import ModifiedCartan.ExtraColorEquiv
import ModifiedCartan.FixedPointPermutationSums
import Mathlib.Data.Fintype.Pi

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem sum_injective_eq_sum_embeddings {A B V : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [AddCommMonoid V] (w : (A → B) → V) :
    (∑ f : A → B, if Function.Injective f then w f else 0) = ∑ f : A ↪ B, w f := by
  calc
    _ = ∑ f : {f : A → B // Function.Injective f}, w f.val :=
      sum_dite_eq_sum_subtype (Function.Injective : (A → B) → Prop) (fun f _ => w f)
    _ = _ := Equiv.sum_comp (Equiv.subtypeInjectiveEquivEmbedding A B) (fun f => w f)

def extraColorWeight {A B R : Type*} (u : A → R) (w : A → B → R) (i : A) : Option B → R
  | none => u i
  | some b => w i b

theorem sum_embeddings_extra_color {A B R : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [CommSemiring R] (u : A → R) (w : A → B → R) :
    (∑ f : A ↪ Option B, ∏ i : A, extraColorWeight u w i (f i)) =
      (∑ f : A ↪ B, ∏ i : A, w i (f i)) +
        ∑ a : A, u a * ∑ f : {i : A // i ≠ a} ↪ B, ∏ i : {i : A // i ≠ a}, w i.val (f i) := by
  rw [← Equiv.sum_comp (extraColorEquiv (A := A) (B := B))
    (fun f => ∏ i : A, extraColorWeight u w i (f i)), Fintype.sum_sum_type]
  change (∑ f : A ↪ B, ∏ i : A, w i (f i)) +
    (∑ p : Σ a : A, {i : A // i ≠ a} ↪ B,
      ∏ i : A, extraColorWeight u w i (extraColorAt p.1 p.2 i)) = _
  congr 1
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ a, extraColorAt_self]
  change u a * (∏ i : {i : A // i ≠ a}, extraColorWeight u w i.val (extraColorAt a f i.val)) = _
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [extraColorAt_of_ne a f i.val i.property]
  rfl

theorem sum_injective_extra_color {A B R : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [CommSemiring R] (u : A → R) (w : A → B → R) :
    (∑ f : A → Option B, if Function.Injective f then
      ∏ i : A, extraColorWeight u w i (f i) else 0) =
      (∑ f : A → B, if Function.Injective f then ∏ i : A, w i (f i) else 0) +
        ∑ a : A, u a * ∑ f : {i : A // i ≠ a} → B, if Function.Injective f then
          ∏ i : {i : A // i ≠ a}, w i.val (f i) else 0 := by
  rw [sum_injective_eq_sum_embeddings (fun f : A → Option B =>
    ∏ i : A, extraColorWeight u w i (f i))]
  simp_rw [sum_injective_eq_sum_embeddings]
  exact sum_embeddings_extra_color u w

end
end ModifiedCartan


