import ModifiedCartan.TableauPrefixes

open scoped BigOperators Classical

namespace ModifiedCartan

noncomputable section

theorem rowLen_eq_of_minimal_missing_box {μ : YoungDiagram} {c : ℕ × ℕ}
    (hnot : c ∉ μ) (hmin : ∀ d, d ≤ c → d ≠ c → d ∈ μ) : c.2 = μ.rowLen c.1 := by
  have hge : μ.rowLen c.1 ≤ c.2 := by
    rw [YoungDiagram.mem_iff_lt_rowLen] at hnot
    omega
  by_contra heq
  have hlt : μ.rowLen c.1 < c.2 := by omega
  have hm := hmin (c.1, μ.rowLen c.1) ⟨le_rfl, hlt.le⟩ (by
    intro hh
    have := congrArg Prod.snd hh
    omega)
  rw [YoungDiagram.mem_iff_lt_rowLen] at hm
  exact lt_irrefl _ hm

theorem addableRow_of_minimal_missing_box {μ : YoungDiagram} {c : ℕ × ℕ}
    (hnot : c ∉ μ) (hmin : ∀ d, d ≤ c → d ≠ c → d ∈ μ) :
    AddablePartitionRow μ c.1 := by
  by_cases hr : c.1 = 0
  · exact Or.inl hr
  · right
    have hm := hmin (c.1 - 1, c.2) ⟨by omega, le_rfl⟩ (by
      intro hh
      have := congrArg Prod.fst hh
      omega)
    rw [YoungDiagram.mem_iff_lt_rowLen] at hm
    rw [rowLen_eq_of_minimal_missing_box hnot hmin] at hm
    exact hm

namespace StandardSkewTableau

theorem not_mem_initialDiagram_at_label {ν μ : YoungDiagram}
    (T : StandardSkewTableau ν μ) (c : SkewPartitionBoxes ν μ) :
    c.val ∉ T.initialDiagram (T.val c : ℕ) := by
  rw [T.mem_initialDiagram]
  rintro (hc | ⟨hc, hl⟩)
  · exact (Finset.mem_sdiff.mp c.property).2 hc
  · exact lt_irrefl _ hl

theorem predecessor_mem_initialDiagram_at_label {ν μ : YoungDiagram}
    (T : StandardSkewTableau ν μ) (c : SkewPartitionBoxes ν μ)
    (d : ℕ × ℕ) (hd : d ≤ c.val) (hne : d ≠ c.val) :
    d ∈ T.initialDiagram (T.val c : ℕ) := by
  rw [T.mem_initialDiagram]
  by_cases hm : d ∈ μ
  · exact Or.inl hm
  · have hdν := ν.isLowerSet hd (Finset.mem_sdiff.mp c.property).1
    have hd' : d ∈ ν.cells \ μ.cells := Finset.mem_sdiff.mpr ⟨hdν, hm⟩
    have hlt : (⟨d, hd'⟩ : SkewPartitionBoxes ν μ) < c :=
      lt_iff_le_and_ne.mpr ⟨hd, fun heq => hne (congrArg Subtype.val heq)⟩
    exact Or.inr ⟨hd', T.property hlt⟩

theorem initialDiagram_addable_at_label {ν μ : YoungDiagram}
    (T : StandardSkewTableau ν μ) (c : SkewPartitionBoxes ν μ) :
    AddablePartitionRow (T.initialDiagram (T.val c : ℕ)) c.val.1 :=
  addableRow_of_minimal_missing_box (T.not_mem_initialDiagram_at_label c)
    (T.predecessor_mem_initialDiagram_at_label c)

theorem mem_initialDiagram_succ_at_label {ν μ : YoungDiagram}
    (T : StandardSkewTableau ν μ) (c : SkewPartitionBoxes ν μ) (d : ℕ × ℕ) :
    d ∈ T.initialDiagram ((T.val c : ℕ) + 1) ↔
      d = c.val ∨ d ∈ T.initialDiagram (T.val c : ℕ) := by
  rw [T.mem_initialDiagram, T.mem_initialDiagram]
  constructor
  · rintro (hd | ⟨hd, hl⟩)
    · exact Or.inr (Or.inl hd)
    · by_cases heq : (T.val ⟨d, hd⟩ : ℕ) = (T.val c : ℕ)
      · left
        exact congrArg Subtype.val (T.val.injective (Fin.ext heq))
      · right
        exact Or.inr ⟨hd, by omega⟩
  · rintro (rfl | hd | ⟨hd, hl⟩)
    · exact Or.inr ⟨c.property, Nat.lt_succ_self _⟩
    · exact Or.inl hd
    · exact Or.inr ⟨hd, by omega⟩

/-- Consecutive stages differ by exactly the box with the intervening label. -/
theorem initialDiagram_succ_at_label {ν μ : YoungDiagram}
    (T : StandardSkewTableau ν μ) (c : SkewPartitionBoxes ν μ) :
    T.initialDiagram ((T.val c : ℕ) + 1) =
      addPartitionBox (T.initialDiagram (T.val c : ℕ)) c.val.1
        (T.initialDiagram_addable_at_label c) := by
  apply YoungDiagram.ext
  ext d
  change d ∈ T.initialDiagram ((T.val c : ℕ) + 1) ↔ d ∈ addPartitionBox _ _ _
  rw [T.mem_initialDiagram_succ_at_label, mem_addPartitionBox,
    ← rowLen_eq_of_minimal_missing_box (T.not_mem_initialDiagram_at_label c)
      (T.predecessor_mem_initialDiagram_at_label c)]

end StandardSkewTableau
end
end ModifiedCartan


