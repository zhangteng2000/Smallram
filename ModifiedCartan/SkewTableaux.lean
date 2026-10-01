import ModifiedCartan.PartitionBoxes

open scoped BigOperators Classical

namespace ModifiedCartan

noncomputable section

/-- Boxes of the skew diagram `ν / μ`. -/
abbrev SkewPartitionBoxes (ν μ : YoungDiagram) :=
  {c : ℕ × ℕ // c ∈ ν.cells \ μ.cells}

/-- Actual standard skew tableaux: a bijective filling, starting at zero,
strictly increasing in the product order on boxes. Adding one to each entry
is the convention `1,...,|ν|-|μ|` of LaTeX `eq:Plucker-translation`. -/
def StandardSkewTableau (ν μ : YoungDiagram) :=
  {e : SkewPartitionBoxes ν μ ≃ Fin (ν.cells \ μ.cells).card // StrictMono e}

instance (ν μ : YoungDiagram) : Fintype (StandardSkewTableau ν μ) := by
  unfold StandardSkewTableau
  infer_instance

/-- The finite count of standard skew tableaux; it is zero outside containment. -/
def standardSkewTableauCount (ν μ : YoungDiagram) : ℕ :=
  if μ ≤ ν then Fintype.card (StandardSkewTableau ν μ) else 0

theorem skewPartitionBoxes_card {ν μ : YoungDiagram} (h : μ ≤ ν) :
    (ν.cells \ μ.cells).card = partitionSize ν - partitionSize μ :=
  Finset.card_sdiff_of_subset h

@[simp] theorem standardSkewTableauCount_of_not_le {ν μ : YoungDiagram}
    (h : ¬ μ ≤ ν) : standardSkewTableauCount ν μ = 0 := by
  simp [standardSkewTableauCount, h]

theorem StandardSkewTableau.row_strict {ν μ : YoungDiagram}
    (T : StandardSkewTableau ν μ) (a b : SkewPartitionBoxes ν μ)
    (hr : a.val.1 = b.val.1) (hc : a.val.2 < b.val.2) : T.val a < T.val b := by
  apply T.property
  apply lt_iff_le_and_ne.mpr
  constructor
  · exact ⟨hr.le, hc.le⟩
  · intro heq
    have := congrArg (fun c : SkewPartitionBoxes ν μ => c.val.2) heq
    omega

theorem StandardSkewTableau.column_strict {ν μ : YoungDiagram}
    (T : StandardSkewTableau ν μ) (a b : SkewPartitionBoxes ν μ)
    (hr : a.val.1 < b.val.1) (hc : a.val.2 = b.val.2) : T.val a < T.val b := by
  apply T.property
  apply lt_iff_le_and_ne.mpr
  constructor
  · exact ⟨hr.le, hc.le⟩
  · intro heq
    have := congrArg (fun c : SkewPartitionBoxes ν μ => c.val.1) heq
    omega

/-- Product-order monotonicity is exactly the usual row-and-column condition. -/
theorem strictMono_skew_iff_row_column {ν μ : YoungDiagram}
    (e : SkewPartitionBoxes ν μ → ℕ) :
    StrictMono e ↔
      (∀ a b : SkewPartitionBoxes ν μ, a.val.1 = b.val.1 → a.val.2 < b.val.2 → e a < e b) ∧
      (∀ a b : SkewPartitionBoxes ν μ, a.val.1 < b.val.1 → a.val.2 = b.val.2 → e a < e b) := by
  constructor
  · intro h
    constructor
    · intro a b hr hc
      apply h
      apply lt_iff_le_and_ne.mpr
      refine ⟨⟨hr.le, hc.le⟩, ?_⟩
      intro heq
      have := congrArg (fun c : SkewPartitionBoxes ν μ => c.val.2) heq
      omega
    · intro a b hr hc
      apply h
      apply lt_iff_le_and_ne.mpr
      refine ⟨⟨hr.le, hc.le⟩, ?_⟩
      intro heq
      have := congrArg (fun c : SkewPartitionBoxes ν μ => c.val.1) heq
      omega
  · rintro ⟨hrow, hcol⟩ a b hab
    have hab_le : a.val ≤ b.val := hab.le
    have hrowle := hab_le.1
    have hcolle := hab_le.2
    by_cases hr : a.val.1 = b.val.1
    · apply hrow a b hr
      have hne : a.val.2 ≠ b.val.2 := by
        intro heq
        exact hab.ne (Subtype.ext (Prod.ext hr heq))
      omega
    · have hrl : a.val.1 < b.val.1 := by omega
      by_cases hc : a.val.2 = b.val.2
      · exact hcol a b hrl hc
      · have hcl : a.val.2 < b.val.2 := by omega
        have hmν : (a.val.1, b.val.2) ∈ ν :=
          ν.up_left_mem hab_le.1 le_rfl (Finset.mem_sdiff.mp b.property).1
        have hmμ : (a.val.1, b.val.2) ∉ μ := by
          intro hm
          exact (Finset.mem_sdiff.mp a.property).2
            (μ.up_left_mem le_rfl hab_le.2 hm)
        let c : SkewPartitionBoxes ν μ :=
          ⟨(a.val.1, b.val.2), Finset.mem_sdiff.mpr ⟨hmν, hmμ⟩⟩
        exact lt_trans (hrow a c rfl hcl) (hcol c b hrl rfl)

@[simp] theorem standardSkewTableauCount_self (μ : YoungDiagram) :
    standardSkewTableauCount μ μ = 1 := by
  letI : IsEmpty (SkewPartitionBoxes μ μ) :=
    ⟨fun c => by simpa using c.property⟩
  letI : IsEmpty (Fin (μ.cells \ μ.cells).card) := by
    simpa using (inferInstance : IsEmpty (Fin 0))
  let e : SkewPartitionBoxes μ μ ≃ Fin (μ.cells \ μ.cells).card :=
    Equiv.equivOfIsEmpty _ _
  let t : StandardSkewTableau μ μ := ⟨e, fun {a} => isEmptyElim a⟩
  haveI : Subsingleton (StandardSkewTableau μ μ) := by
    refine ⟨fun a b => Subtype.ext ?_⟩
    apply Equiv.ext
    intro c
    exact isEmptyElim c
  letI : Unique (StandardSkewTableau μ μ) := uniqueOfSubsingleton t
  simp [standardSkewTableauCount]

end
end ModifiedCartan




