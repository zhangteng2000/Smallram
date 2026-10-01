import ModifiedCartan.GrowthPathBoxes

open scoped BigOperators Classical

namespace ModifiedCartan

noncomputable section

def minorGrowthBoxEquiv {n : ℕ} {μ : YoungDiagram} (k : ℕ)
    (p : MinorGrowthPath n μ k) : Fin k ≃ SkewPartitionBoxes (minorGrowthEndpoint k p) μ :=
  Equiv.ofBijective (fun j => ⟨minorGrowthBoxes k p j,
    Finset.mem_sdiff.mpr ⟨minorGrowthBoxes_mem_endpoint k p j,
      minorGrowthBoxes_not_mem_start k p j⟩⟩) (by
    constructor
    · intro i j h
      exact minorGrowthBoxes_injective k p (congrArg Subtype.val h)
    · intro c
      obtain ⟨j, hj⟩ := (mem_skew_endpoint_iff k p c.val).mp c.property
      exact ⟨j, Subtype.ext hj⟩)

@[simp] theorem minorGrowthBoxEquiv_val {n : ℕ} {μ : YoungDiagram} (k : ℕ)
    (p : MinorGrowthPath n μ k) (j : Fin k) :
    (minorGrowthBoxEquiv k p j).val = minorGrowthBoxes k p j := rfl

theorem minorGrowthBoxEquiv_symm_strictMono {n : ℕ} {μ : YoungDiagram} (k : ℕ)
    (p : MinorGrowthPath n μ k) : StrictMono (minorGrowthBoxEquiv k p).symm := by
  intro a b hab
  apply lt_iff_le_and_ne.mpr
  constructor
  · apply minorGrowthBoxes_index_le_of_le k p
    have ha := congrArg Subtype.val ((minorGrowthBoxEquiv k p).apply_symm_apply a)
    have hb := congrArg Subtype.val ((minorGrowthBoxEquiv k p).apply_symm_apply b)
    simp only [minorGrowthBoxEquiv_val] at ha hb
    rw [ha, hb]
    exact hab.le
  · intro heq
    exact hab.ne ((minorGrowthBoxEquiv k p).symm.injective heq)

theorem minorGrowthSkewCard {n : ℕ} {μ : YoungDiagram} (k : ℕ)
    (p : MinorGrowthPath n μ k) :
    (minorGrowthEndpoint k p).cells.card - μ.cells.card = k := by
  change partitionSize (minorGrowthEndpoint k p) - partitionSize μ = k
  rw [partitionSize_minorGrowthEndpoint]
  omega

theorem minorGrowthSkewBoxes_card {n : ℕ} {μ : YoungDiagram} (k : ℕ)
    (p : MinorGrowthPath n μ k) :
    ((minorGrowthEndpoint k p).cells \ μ.cells).card = k := by
  rw [Finset.card_sdiff_of_subset (le_minorGrowthEndpoint k p)]
  exact minorGrowthSkewCard k p

/-- Label each newly inserted box by its insertion time. -/
def minorGrowthTableau {n : ℕ} {μ : YoungDiagram} (k : ℕ)
    (p : MinorGrowthPath n μ k) : StandardSkewTableau (minorGrowthEndpoint k p) μ :=
  ⟨(minorGrowthBoxEquiv k p).symm.trans
      (Fin.castOrderIso (minorGrowthSkewBoxes_card k p).symm).toEquiv,
    (Fin.castOrderIso (minorGrowthSkewBoxes_card k p).symm).strictMono.comp
      (minorGrowthBoxEquiv_symm_strictMono k p)⟩

@[simp] theorem minorGrowthTableau_label {n : ℕ} {μ : YoungDiagram} (k : ℕ)
    (p : MinorGrowthPath n μ k) (j : Fin k) :
    ((minorGrowthTableau k p).val (minorGrowthBoxEquiv k p j) : ℕ) = j := by
  simp [minorGrowthTableau]

end
end ModifiedCartan


