import ModifiedCartan.SkewBoxInsertion

open scoped BigOperators Classical

namespace ModifiedCartan

noncomputable section

namespace StandardSkewTableau

/-- Fill the missing first box by zero and shift the tail labels up by one. -/
def prependLabel {ν μ : YoungDiagram} {r : ℕ} {h : AddablePartitionRow μ r}
    (S : StandardSkewTableau ν (addPartitionBox μ r h)) (hc : (r, μ.rowLen r) ∈ ν)
    (c : SkewPartitionBoxes ν μ) : Fin (ν.cells \ μ.cells).card :=
  if he : c.val = (r, μ.rowLen r) then
    ⟨0, Finset.card_pos.mpr ⟨_, addedBox_mem_skew hc⟩⟩
  else
    ⟨(S.val (skewBoxAfter h c he) : ℕ) + 1, by
      have hs := (S.val (skewBoxAfter h c he)).isLt
      have hh := skewCells_card_addPartitionBox h hc
      omega⟩

theorem prependLabel_val_eq_zero {ν μ : YoungDiagram} {r : ℕ} {h : AddablePartitionRow μ r}
    (S : StandardSkewTableau ν (addPartitionBox μ r h)) (hc : (r, μ.rowLen r) ∈ ν)
    (c : SkewPartitionBoxes ν μ) (he : c.val = (r, μ.rowLen r)) :
    (S.prependLabel hc c : ℕ) = 0 := by
  simp [prependLabel, he]

theorem prependLabel_val_of_ne {ν μ : YoungDiagram} {r : ℕ} {h : AddablePartitionRow μ r}
    (S : StandardSkewTableau ν (addPartitionBox μ r h)) (hc : (r, μ.rowLen r) ∈ ν)
    (c : SkewPartitionBoxes ν μ) (he : c.val ≠ (r, μ.rowLen r)) :
    (S.prependLabel hc c : ℕ) = (S.val (skewBoxAfter h c he) : ℕ) + 1 := by
  simp [prependLabel, he]

theorem prependLabel_injective {ν μ : YoungDiagram} {r : ℕ} {h : AddablePartitionRow μ r}
    (S : StandardSkewTableau ν (addPartitionBox μ r h)) (hc : (r, μ.rowLen r) ∈ ν) :
    Function.Injective (S.prependLabel hc) := by
  intro a b hab
  have hv := congrArg Fin.val hab
  by_cases ha : a.val = (r, μ.rowLen r)
  · by_cases hb : b.val = (r, μ.rowLen r)
    · exact Subtype.ext (ha.trans hb.symm)
    · rw [S.prependLabel_val_eq_zero hc a ha, S.prependLabel_val_of_ne hc b hb] at hv
      omega
  · by_cases hb : b.val = (r, μ.rowLen r)
    · rw [S.prependLabel_val_of_ne hc a ha, S.prependLabel_val_eq_zero hc b hb] at hv
      omega
    · rw [S.prependLabel_val_of_ne hc a ha, S.prependLabel_val_of_ne hc b hb] at hv
      have he : S.val (skewBoxAfter h a ha) = S.val (skewBoxAfter h b hb) := by
        apply Fin.ext
        omega
      apply Subtype.ext
      exact congrArg (fun c : SkewPartitionBoxes ν (addPartitionBox μ r h) => c.val)
        (S.val.injective he)

theorem prependLabel_strictMono {ν μ : YoungDiagram} {r : ℕ} {h : AddablePartitionRow μ r}
    (S : StandardSkewTableau ν (addPartitionBox μ r h)) (hc : (r, μ.rowLen r) ∈ ν) :
    StrictMono (S.prependLabel hc) := by
  intro a b hab
  change (S.prependLabel hc a : ℕ) < (S.prependLabel hc b : ℕ)
  by_cases ha : a.val = (r, μ.rowLen r)
  · have hb : b.val ≠ (r, μ.rowLen r) := by
      intro hb
      exact hab.ne (Subtype.ext (ha.trans hb.symm))
    rw [S.prependLabel_val_eq_zero hc a ha, S.prependLabel_val_of_ne hc b hb]
    omega
  · by_cases hb : b.val = (r, μ.rowLen r)
    · have hle : a.val ≤ b.val := hab.le
      rw [hb] at hle
      exact ((Finset.mem_sdiff.mp a.property).2 (mem_of_le_addable_box h hle ha)).elim
    · have ht : (S.val (skewBoxAfter h a ha) : ℕ) <
          (S.val (skewBoxAfter h b hb) : ℕ) := S.property hab
      rw [S.prependLabel_val_of_ne hc a ha, S.prependLabel_val_of_ne hc b hb]
      omega

def prependTableau {ν μ : YoungDiagram} {r : ℕ} {h : AddablePartitionRow μ r}
    (S : StandardSkewTableau ν (addPartitionBox μ r h)) (hc : (r, μ.rowLen r) ∈ ν) :
    StandardSkewTableau ν μ :=
  ⟨Equiv.ofBijective (S.prependLabel hc)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨S.prependLabel_injective hc, by simp⟩), S.prependLabel_strictMono hc⟩

@[simp] theorem prependTableau_first_label {ν μ : YoungDiagram} {r : ℕ}
    {h : AddablePartitionRow μ r} (S : StandardSkewTableau ν (addPartitionBox μ r h))
    (hc : (r, μ.rowLen r) ∈ ν) :
    ((S.prependTableau hc).val ⟨(r, μ.rowLen r), addedBox_mem_skew hc⟩ : ℕ) = 0 :=
  S.prependLabel_val_eq_zero hc _ rfl

theorem prependTableau_label_of_ne {ν μ : YoungDiagram} {r : ℕ}
    {h : AddablePartitionRow μ r} (S : StandardSkewTableau ν (addPartitionBox μ r h))
    (hc : (r, μ.rowLen r) ∈ ν) (c : SkewPartitionBoxes ν μ)
    (he : c.val ≠ (r, μ.rowLen r)) :
    ((S.prependTableau hc).val c : ℕ) = (S.val (skewBoxAfter h c he) : ℕ) + 1 :=
  S.prependLabel_val_of_ne hc c he

end StandardSkewTableau
end
end ModifiedCartan


