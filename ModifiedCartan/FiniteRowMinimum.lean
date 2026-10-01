import ModifiedCartan.SortedMinorOrders
import Mathlib.Data.Finset.Sort

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem fin_nat_le_strictMono {n : ℕ} {f : Fin n → ℕ} (hf : StrictMono f) (i : Fin n) :
    i.val ≤ f i := by
  have hb : ∀ k (hk : k < n), k ≤ f ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      have hlt := hf (show (⟨k, hk'⟩ : Fin n) < ⟨k + 1, hk⟩ from by simp)
      have hle := ih hk'
      omega
  exact hb i.val i.isLt

theorem finset_nat_sorted_sum (s : Finset ℕ) :
    (∑ i : Fin s.card, s.orderEmbOfFin rfl i) = ∑ x ∈ s, x := by
  calc
    _ = ∑ x ∈ Finset.univ.image (s.orderEmbOfFin rfl), x :=
      (Finset.sum_image (f := fun x : ℕ => x)
        (s.orderEmbOfFin rfl).injective.injOn).symm
    _ = _ := by rw [s.image_orderEmbOfFin_univ rfl]

/-- Distinct nonnegative integers have sum at least that of the first ones. -/
theorem finset_nat_sum_min (s : Finset ℕ) :
    (∑ i : Fin s.card, i.val) ≤ ∑ x ∈ s, x := by
  rw [← finset_nat_sorted_sum]
  exact Finset.sum_le_sum fun i _ => fin_nat_le_strictMono (s.orderEmbOfFin rfl).strictMono i

/-- Equality in the minimum sum forces every entry to be smaller than the cardinality. -/
theorem finset_nat_mem_lt_card_of_sum_eq (s : Finset ℕ)
    (hs : (∑ i : Fin s.card, i.val) = ∑ x ∈ s, x) {x : ℕ} (hx : x ∈ s) : x < s.card := by
  have he : (∑ i : Fin s.card, i.val) = ∑ i : Fin s.card, s.orderEmbOfFin rfl i := by
    rw [finset_nat_sorted_sum]
    exact hs
  have hp := (Finset.sum_eq_sum_iff_of_le (fun (i : Fin s.card) (_ : i ∈ Finset.univ) =>
    fin_nat_le_strictMono (s.orderEmbOfFin rfl).strictMono i)).mp he
  let i : Fin s.card := (s.orderIsoOfFin rfl).symm ⟨x, hx⟩
  have hi : s.orderEmbOfFin rfl i = x := by
    exact congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨x, hx⟩)
  have hv := hp i (Finset.mem_univ i)
  rw [hi] at hv
  exact hv ▸ i.isLt

theorem fintype_nat_sum_min_of_injective {A : Type*} [Fintype A]
    (f : A → ℕ) (hf : Function.Injective f) :
    (∑ i : Fin (Fintype.card A), i.val) ≤ ∑ a : A, f a := by
  have h := finset_nat_sum_min (Finset.univ.image f)
  have hc : (Finset.univ.image f).card = Fintype.card A := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ]
  rw [hc, Finset.sum_image hf.injOn] at h
  exact h

theorem fintype_nat_lt_card_of_min_sum {A : Type*} [Fintype A]
    (f : A → ℕ) (hf : Function.Injective f)
    (hs : (∑ i : Fin (Fintype.card A), i.val) = ∑ a : A, f a) (a : A) :
    f a < Fintype.card A := by
  have hc : (Finset.univ.image f).card = Fintype.card A := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ]
  have hs' : (∑ i : Fin (Finset.univ.image f).card, i.val) =
      ∑ x ∈ Finset.univ.image f, x := by
    rw [hc, Finset.sum_image hf.injOn]
    exact hs
  have h := finset_nat_mem_lt_card_of_sum_eq (Finset.univ.image f) hs'
    (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)
  rwa [hc] at h

end
end ModifiedCartan


