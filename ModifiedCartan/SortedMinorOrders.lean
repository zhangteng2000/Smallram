import ModifiedCartan.FinitePartitions
import ModifiedCartan.PolynomialMinors
import Mathlib.Order.Interval.Finset.Fin

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- A permutation cannot improve an increasing sequence coordinate by coordinate. -/
theorem sorted_le_of_permuted_le {N : ℕ} {a b : Fin N → ℕ}
    (ha : StrictMono a) (hb : Monotone b) (σ : Equiv.Perm (Fin N))
    (h : ∀ j, a (σ j) ≤ b j) : ∀ i, a i ≤ b i := by
  intro i
  by_contra! hi
  have hs : (Finset.Iic i).image σ ⊆ Finset.Iio i := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    have hk' : k ≤ i := Finset.mem_Iic.mp hk
    have hlt : a (σ k) < a i := (h k).trans_lt ((hb hk').trans_lt hi)
    apply Finset.mem_Iio.mpr
    by_contra! hki
    exact (not_lt_of_ge (ha.monotone hki)) hlt
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ σ.injective, Fin.card_Iic, Fin.card_Iio] at hc
  omega

theorem exists_order_above_permuted_bound {N : ℕ} {a b : Fin N → ℕ}
    (ha : StrictMono a) (hb : Monotone b) (hi : ∃ i, b i < a i)
    (σ : Equiv.Perm (Fin N)) : ∃ j, b j < a (σ j) := by
  by_contra! h
  have hall := sorted_le_of_permuted_le ha hb σ h
  obtain ⟨i, hi⟩ := hi
  exact (not_lt_of_ge (hall i)) hi

end
end ModifiedCartan


