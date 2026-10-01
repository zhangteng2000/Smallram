import ModifiedCartan.MinorGrowthPaths

open scoped BigOperators Classical

namespace ModifiedCartan

noncomputable section

/-- Number of legal derivative paths with a specified endpoint. -/
def minorGrowthCount (n : ℕ) (μ ν : YoungDiagram) (k : ℕ) : ℕ :=
  Fintype.card {p : MinorGrowthPath n μ k // minorGrowthEndpoint k p = ν}

@[simp] theorem minorGrowthCount_zero (n : ℕ) (μ ν : YoungDiagram) :
    minorGrowthCount n μ ν 0 = if μ = ν then 1 else 0 := by
  unfold minorGrowthCount
  split_ifs with h
  · subst ν
    letI : Subsingleton (MinorGrowthPath n μ 0) :=
      inferInstanceAs (Subsingleton PUnit)
    letI : Unique {p : MinorGrowthPath n μ 0 // minorGrowthEndpoint 0 p = μ} :=
      { default := ⟨PUnit.unit, rfl⟩
        uniq := fun p => Subtype.ext (Subsingleton.elim _ _) }
    exact Fintype.card_unique
  · letI : IsEmpty {p : MinorGrowthPath n μ 0 // minorGrowthEndpoint 0 p = ν} :=
      ⟨fun p => h p.property⟩
    exact Fintype.card_eq_zero

theorem minorGrowthCount_eq_zero_of_not_le {n : ℕ} {μ ν : YoungDiagram}
    (k : ℕ) (h : ¬ μ ≤ ν) : minorGrowthCount n μ ν k = 0 := by
  letI : IsEmpty {p : MinorGrowthPath n μ k // minorGrowthEndpoint k p = ν} :=
    ⟨fun p => h (p.property ▸ le_minorGrowthEndpoint k p.val)⟩
  exact Fintype.card_eq_zero

theorem minorGrowthCount_eq_zero_of_size_ne {n : ℕ} {μ ν : YoungDiagram}
    (k : ℕ) (h : partitionSize ν ≠ partitionSize μ + k) : minorGrowthCount n μ ν k = 0 := by
  letI : IsEmpty {p : MinorGrowthPath n μ k // minorGrowthEndpoint k p = ν} :=
    ⟨fun p => h (p.property ▸ partitionSize_minorGrowthEndpoint k p.val)⟩
  exact Fintype.card_eq_zero

theorem minorGrowthCount_succ (n : ℕ) (μ ν : YoungDiagram) (k : ℕ) :
    minorGrowthCount n μ ν (k + 1) =
      ∑ i : LegalMinorRow n μ, minorGrowthCount n (growMinorPartition i) ν k := by
  let e : {p : MinorGrowthPath n μ (k + 1) // minorGrowthEndpoint (k + 1) p = ν} ≃
      Σ i : LegalMinorRow n μ,
        {p : MinorGrowthPath n (growMinorPartition i) k // minorGrowthEndpoint k p = ν} :=
    { toFun := fun p => ⟨p.val.1, p.val.2, p.property⟩
      invFun := fun p => ⟨⟨p.1, p.2.val⟩, p.2.property⟩
      left_inv := by rintro ⟨⟨i, p⟩, hp⟩; rfl
      right_inv := by rintro ⟨i, ⟨p, hp⟩⟩; rfl }
  have he := Fintype.card_congr e
  simpa only [Fintype.card_sigma, minorGrowthCount] using he

end
end ModifiedCartan


