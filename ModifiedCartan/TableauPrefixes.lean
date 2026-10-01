import ModifiedCartan.SkewTableaux

open scoped BigOperators Classical

namespace ModifiedCartan

noncomputable section

namespace StandardSkewTableau

/-- The box is filled before stage `k`. -/
def Before {ν μ : YoungDiagram} (T : StandardSkewTableau ν μ) (k : ℕ)
    (c : ℕ × ℕ) : Prop :=
  ∃ hc : c ∈ ν.cells \ μ.cells, (T.val ⟨c, hc⟩ : ℕ) < k

theorem before_iff {ν μ : YoungDiagram} (T : StandardSkewTableau ν μ) (k : ℕ)
    {c : ℕ × ℕ} (hc : c ∈ ν.cells \ μ.cells) :
    T.Before k c ↔ (T.val ⟨c, hc⟩ : ℕ) < k := by
  exact ⟨fun h => h.choose_spec, fun h => ⟨hc, h⟩⟩

def initialDiagramCells {ν μ : YoungDiagram} (T : StandardSkewTableau ν μ) (k : ℕ) :
    Finset (ℕ × ℕ) := μ.cells ∪ (ν.cells \ μ.cells).filter (T.Before k)

@[simp] theorem mem_initialDiagramCells {ν μ : YoungDiagram} (T : StandardSkewTableau ν μ)
    (k : ℕ) (c : ℕ × ℕ) : c ∈ T.initialDiagramCells k ↔ c ∈ μ ∨ T.Before k c := by
  simp only [initialDiagramCells, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | ⟨hc, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hc, hc, h⟩

theorem initialDiagramCells_isLowerSet {ν μ : YoungDiagram} (T : StandardSkewTableau ν μ)
    (k : ℕ) : IsLowerSet (T.initialDiagramCells k : Set (ℕ × ℕ)) := by
  intro a b hba ha
  rw [Finset.mem_coe, mem_initialDiagramCells] at ha ⊢
  rcases ha with ha | ⟨ha, hlabel⟩
  · exact Or.inl (μ.isLowerSet hba ha)
  · by_cases hb : b ∈ μ
    · exact Or.inl hb
    · have hbν : b ∈ ν := ν.isLowerSet hba (Finset.mem_sdiff.mp ha).1
      have hb' : b ∈ ν.cells \ μ.cells := Finset.mem_sdiff.mpr ⟨hbν, hb⟩
      have hmono : (T.val ⟨b, hb'⟩ : ℕ) ≤ (T.val ⟨a, ha⟩ : ℕ) :=
        T.property.monotone hba
      exact Or.inr ⟨hb', lt_of_le_of_lt hmono hlabel⟩

/-- The intermediate Young diagram after the first `k` labels are inserted. -/
def initialDiagram {ν μ : YoungDiagram} (T : StandardSkewTableau ν μ) (k : ℕ) : YoungDiagram :=
  ⟨T.initialDiagramCells k, T.initialDiagramCells_isLowerSet k⟩

@[simp] theorem mem_initialDiagram {ν μ : YoungDiagram} (T : StandardSkewTableau ν μ)
    (k : ℕ) (c : ℕ × ℕ) : c ∈ T.initialDiagram k ↔ c ∈ μ ∨ T.Before k c :=
  T.mem_initialDiagramCells k c

theorem le_initialDiagram {ν μ : YoungDiagram} (T : StandardSkewTableau ν μ) (k : ℕ) :
    μ ≤ T.initialDiagram k := fun c hc => (T.mem_initialDiagram k c).mpr (Or.inl hc)

theorem initialDiagram_le {ν μ : YoungDiagram} (T : StandardSkewTableau ν μ)
    (h : μ ≤ ν) (k : ℕ) : T.initialDiagram k ≤ ν := by
  intro c hc
  rcases (T.mem_initialDiagram k c).mp hc with hc | ⟨hc, _⟩
  · exact h hc
  · exact (Finset.mem_sdiff.mp hc).1

theorem initialDiagram_monotone {ν μ : YoungDiagram} (T : StandardSkewTableau ν μ) :
    Monotone T.initialDiagram := by
  intro k l hkl c hc
  rw [T.mem_initialDiagram] at hc ⊢
  rcases hc with hc | ⟨hc, hlabel⟩
  · exact Or.inl hc
  · exact Or.inr ⟨hc, hlabel.trans_le hkl⟩

@[simp] theorem initialDiagram_zero {ν μ : YoungDiagram} (T : StandardSkewTableau ν μ) :
    T.initialDiagram 0 = μ := by
  apply YoungDiagram.ext
  ext c
  simp [Before]

@[simp] theorem initialDiagram_card {ν μ : YoungDiagram} (T : StandardSkewTableau ν μ)
    (h : μ ≤ ν) : T.initialDiagram (ν.cells \ μ.cells).card = ν := by
  apply le_antisymm (T.initialDiagram_le h _)
  intro c hc
  rw [T.mem_initialDiagram]
  by_cases hm : c ∈ μ
  · exact Or.inl hm
  · have hc' : c ∈ ν.cells \ μ.cells := Finset.mem_sdiff.mpr ⟨hc, hm⟩
    exact Or.inr ⟨hc', (T.val ⟨c, hc'⟩).isLt⟩

end StandardSkewTableau
end
end ModifiedCartan



