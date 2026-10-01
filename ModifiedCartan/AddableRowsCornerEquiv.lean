import ModifiedCartan.YoungCornerRowDrops

open scoped Classical

namespace ModifiedCartan
noncomputable section

abbrev YoungAddableRow (μ : YoungDiagram) :=
  {r : Fin (μ.colLen 0 + 1) // AddablePartitionRow μ r.val}

def youngFirstAddableRow (μ : YoungDiagram) : YoungAddableRow μ :=
  ⟨⟨0, Nat.zero_lt_succ _⟩, Or.inl rfl⟩

def youngAddableRowAfterCorner (μ : YoungDiagram) (b : YoungCorner μ) : YoungAddableRow μ :=
  ⟨⟨b.val.val.1 + 1, Nat.succ_lt_succ (youngCorner_row_lt_height μ b)⟩,
    Or.inr (by simpa using youngCorner_row_drop μ b)⟩

def youngOptionCornerRow (μ : YoungDiagram) : Option (YoungCorner μ) → YoungAddableRow μ
  | none => youngFirstAddableRow μ
  | some b => youngAddableRowAfterCorner μ b

theorem youngOptionCornerRow_bijective (μ : YoungDiagram) :
    Function.Bijective (youngOptionCornerRow μ) := by
  constructor
  · intro b c he
    cases b with
    | none =>
      cases c with
      | none => rfl
      | some c =>
        have hh := congrArg (fun r : YoungAddableRow μ => r.val.val) he
        change 0 = c.val.val.1 + 1 at hh
        omega
    | some b =>
      cases c with
      | none =>
        have hh := congrArg (fun r : YoungAddableRow μ => r.val.val) he
        change b.val.val.1 + 1 = 0 at hh
        omega
      | some c =>
        congr 1
        apply youngCorner_row_injective μ
        change b.val.val.1 = c.val.val.1
        have hh := congrArg (fun r : YoungAddableRow μ => r.val.val) he
        change b.val.val.1 + 1 = c.val.val.1 + 1 at hh
        omega
  · intro r
    by_cases hr : r.val.val = 0
    · exact ⟨none, Subtype.ext (Fin.ext hr.symm)⟩
    · have hsucc : r.val.val - 1 + 1 = r.val.val := by omega
      have hdrop : μ.rowLen (r.val.val - 1 + 1) < μ.rowLen (r.val.val - 1) := by
        rw [hsucc]
        exact r.property.resolve_left hr
      refine ⟨some (youngCornerOfRowDrop μ (r.val.val - 1) hdrop), Subtype.ext (Fin.ext ?_)⟩
      exact hsucc

/-- Addable rows consist of the top row and one row immediately after each removable corner. -/
def youngOptionCornerEquivAddableRow (μ : YoungDiagram) : Option (YoungCorner μ) ≃ YoungAddableRow μ :=
  Equiv.ofBijective (youngOptionCornerRow μ) (youngOptionCornerRow_bijective μ)

theorem youngAddableRow_card (μ : YoungDiagram) :
    Fintype.card (YoungAddableRow μ) = Fintype.card (YoungCorner μ) + 1 := by
  rw [← Fintype.card_congr (youngOptionCornerEquivAddableRow μ), Fintype.card_option]

end
end ModifiedCartan


