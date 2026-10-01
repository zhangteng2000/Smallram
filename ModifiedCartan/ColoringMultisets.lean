import Mathlib.Data.Multiset.Fintype
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Basic

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def coloringMultiset {A B : Type*} [Fintype A] (f : A → B) : Sym B (Fintype.card A) :=
  ⟨Finset.univ.val.map f, by simp⟩

theorem coloringMultiset_comp_equiv {A C B : Type*} [Fintype A] [Fintype C]
    (f : A → B) (e : C ≃ A) :
    (coloringMultiset (f ∘ e)).val = (coloringMultiset f).val := by
  change Finset.univ.val.map (f ∘ e) = Finset.univ.val.map f
  rw [← Multiset.map_map, Multiset.map_univ_val_equiv]

theorem coloringMultiset_count {A B : Type*} [Fintype A] (f : A → B) (b : B) :
    (coloringMultiset f).val.count b = Fintype.card {a : A // f a = b} := by
  simp only [coloringMultiset, Multiset.count_map, Fintype.card_subtype]
  rw [← Finset.filter_val]
  congr 2
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_comm]

/-- Equal color multiplicities give an actual permutation of the finite domain. -/
theorem coloringMultiset_eq_iff_permutation {A B : Type*} [Fintype A]
    (f g : A → B) :
    coloringMultiset f = coloringMultiset g ↔ ∃ σ : Equiv.Perm A, g ∘ σ = f := by
  constructor
  · intro h
    have hc (b : B) : Fintype.card {a : A // f a = b} = Fintype.card {a : A // g a = b} := by
      rw [← coloringMultiset_count, ← coloringMultiset_count, h]
    let e (b : B) : {a : A // f a = b} ≃ {a : A // g a = b} :=
      Fintype.equivOfCardEq (hc b)
    exact ⟨Equiv.ofFiberEquiv e, funext (Equiv.ofFiberEquiv_map e)⟩
  · rintro ⟨σ, hσ⟩
    apply Subtype.ext
    rw [← hσ]
    exact coloringMultiset_comp_equiv g σ

theorem coloringMultiset_surjective {A B : Type*} [Fintype A] :
    Function.Surjective (coloringMultiset : (A → B) → Sym B (Fintype.card A)) := by
  intro s
  let e : A ≃ s.val := Fintype.equivOfCardEq (by rw [Multiset.card_coe, s.property])
  refine ⟨fun a => ((e a : s.val) : B), ?_⟩
  apply Subtype.ext
  change (coloringMultiset ((fun t : s.val => (t : B)) ∘ e)).val = s.val
  rw [coloringMultiset_comp_equiv]
  exact Multiset.map_univ_coe s.val

end
end ModifiedCartan


