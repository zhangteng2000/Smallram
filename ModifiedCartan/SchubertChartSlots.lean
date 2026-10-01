import ModifiedCartan.FinitePartitions
import Mathlib.Order.Interval.Finset.Fin

open scoped Classical BigOperators

namespace ModifiedCartan
noncomputable section

/-- Non-pivot exponents below the `j`th Schubert pivot, for the affine
    chart used in manuscript `lem:KP-correspondence`. -/
def schubertFreeOrders (n : ℕ) (τ : YoungDiagram) (j : Fin (n + 1)) : Finset ℕ :=
  Finset.range (partitionMinorOrders n τ j) \
    (Finset.Iio j).image (partitionMinorOrders n τ)

theorem mem_schubertFreeOrders {n : ℕ} (τ : YoungDiagram) (j : Fin (n + 1)) (k : ℕ) :
    k ∈ schubertFreeOrders n τ j ↔
      k < partitionMinorOrders n τ j ∧ ∀ i, k ≠ partitionMinorOrders n τ i := by
  simp only [schubertFreeOrders, Finset.mem_sdiff, Finset.mem_range,
    Finset.mem_image, Finset.mem_Iio]
  constructor
  · rintro ⟨hk, hn⟩
    refine ⟨hk, ?_⟩
    intro i he
    apply hn
    refine ⟨i, (partitionMinorOrders_strictMono n τ).lt_iff_lt.mp ?_, he.symm⟩
    rwa [← he]
  · rintro ⟨hk, hn⟩
    refine ⟨hk, ?_⟩
    rintro ⟨i, hi, he⟩
    exact hn i he.symm

theorem schubertFreeOrders_card {n : ℕ} (τ : YoungDiagram) (j : Fin (n + 1)) :
    (schubertFreeOrders n τ j).card = τ.rowLen (n - j.val) := by
  have hs : (Finset.Iio j).image (partitionMinorOrders n τ) ⊆
      Finset.range (partitionMinorOrders n τ j) := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_range.mpr ((partitionMinorOrders_strictMono n τ)
      (Finset.mem_Iio.mp hi))
  rw [schubertFreeOrders, Finset.card_sdiff_of_subset hs,
    Finset.card_range, Finset.card_image_of_injective _ (partitionMinorOrders_strictMono n τ).injective,
    Fin.card_Iio, partitionMinorOrders, Nat.add_sub_cancel_left]

/-- The actual free coefficient positions of the Schubert cell. -/
def SchubertChartSlot (n : ℕ) (τ : YoungDiagram) :=
  Σ j : Fin (n + 1), {k : ℕ // k ∈ schubertFreeOrders n τ j}

instance (n : ℕ) (τ : YoungDiagram) : Fintype (SchubertChartSlot n τ) :=
  inferInstanceAs (Fintype (Σ j : Fin (n + 1), {k : ℕ // k ∈ schubertFreeOrders n τ j}))

/-- The affine Schubert chart has exactly `|τ|` free coefficients.
    Auxiliary to manuscript `lem:KP-correspondence`; no degree formula is used. -/
theorem schubertChartSlot_card {n : ℕ} (τ : YoungDiagram) (hτ : PartitionFits n τ) :
    Fintype.card (SchubertChartSlot n τ) = partitionSize τ := by
  change Fintype.card (Σ j : Fin (n + 1), {k : ℕ // k ∈ schubertFreeOrders n τ j}) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_coe, schubertFreeOrders_card]
  rw [partitionSize_eq_sum_rowLen hτ]
  simpa only [Fin.revPerm_apply, Fin.val_rev, Nat.succ_sub_succ_eq_sub] using
    Equiv.sum_comp Fin.revPerm (fun i : Fin (n + 1) => τ.rowLen i.val)

end
end ModifiedCartan

#print axioms ModifiedCartan.schubertChartSlot_card
