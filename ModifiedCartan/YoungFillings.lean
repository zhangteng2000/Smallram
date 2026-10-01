import ModifiedCartan.YoungPermutationSubgroups

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- Bijective fillings by the letters 0,...,size-1. -/
abbrev YoungFilling (μ : YoungDiagram) := YoungBoxes μ ≃ Fin (partitionSize μ)

def YoungRowStandard {μ : YoungDiagram} (T : YoungFilling μ) : Prop :=
  ∀ a b : YoungBoxes μ, a.val.1 = b.val.1 → a.val.2 < b.val.2 → T a < T b

def YoungColumnStandard {μ : YoungDiagram} (T : YoungFilling μ) : Prop :=
  ∀ a b : YoungBoxes μ, a.val.1 < b.val.1 → a.val.2 = b.val.2 → T a < T b

/-- Standard Young tableaux as actual increasing bijective fillings. -/
def StandardYoungTableau (μ : YoungDiagram) := {T : YoungFilling μ // StrictMono T}

instance (μ : YoungDiagram) : Fintype (StandardYoungTableau μ) := by
  unfold StandardYoungTableau
  infer_instance

/-- Removing the empty diagram preserves the actual box order. -/
def emptySkewBoxOrderIso (μ : YoungDiagram) : SkewPartitionBoxes μ ⊥ ≃o YoungBoxes μ where
  toFun b := ⟨b.val, (Finset.mem_sdiff.mp b.property).1⟩
  invFun b := ⟨b.val, by simpa using b.property⟩
  left_inv b := rfl
  right_inv b := rfl
  map_rel_iff' := Iff.rfl

def increasingEquivCongr {A B C D : Type*} [Preorder A] [Preorder B] [Preorder C] [Preorder D]
    (e : A ≃o B) (f : C ≃o D) :
    {g : A ≃ C // StrictMono g} ≃ {g : B ≃ D // StrictMono g} where
  toFun g := ⟨(e.symm.toEquiv.trans g.val).trans f.toEquiv,
    f.strictMono.comp (g.property.comp e.symm.strictMono)⟩
  invFun g := ⟨(e.toEquiv.trans g.val).trans f.symm.toEquiv,
    f.symm.strictMono.comp (g.property.comp e.strictMono)⟩
  left_inv g := by
    apply Subtype.ext
    apply Equiv.ext
    intro a
    change f.symm (f (g.val (e.symm (e a)))) = g.val a
    simp
  right_inv g := by
    apply Subtype.ext
    apply Equiv.ext
    intro b
    change f (f.symm (g.val (e (e.symm b)))) = g.val b
    simp

theorem young_filling_standard_iff {μ : YoungDiagram} (T : YoungFilling μ) :
    StrictMono T ↔ YoungRowStandard T ∧ YoungColumnStandard T := by
  let e := emptySkewBoxOrderIso μ
  constructor
  · intro h
    have hp := (strictMono_skew_iff_row_column (fun b => (T (e b)).val)).mp
      (Fin.val_strictMono.comp (h.comp e.strictMono))
    constructor
    · intro a b hr hc
      simpa using hp.1 (e.symm a) (e.symm b) hr hc
    · intro a b hr hc
      simpa using hp.2 (e.symm a) (e.symm b) hr hc
  · rintro ⟨hr, hc⟩
    have hp : StrictMono (fun b : SkewPartitionBoxes μ ⊥ => (T (e b)).val) :=
      (strictMono_skew_iff_row_column _).mpr
        ⟨fun a b ha hb => hr (e a) (e b) ha hb,
          fun a b ha hb => hc (e a) (e b) ha hb⟩
    intro a b hab
    simpa using hp (e.symm.strictMono hab)

/-- The tableau count agrees with the actual skew-tableau count already used in translation. -/
theorem standardYoungTableau_card (μ : YoungDiagram) :
    Fintype.card (StandardYoungTableau μ) = standardSkewTableauCount μ ⊥ := by
  have hn : (μ.cells \ (⊥ : YoungDiagram).cells).card = partitionSize μ := by
    simp [partitionSize]
  let e := increasingEquivCongr (emptySkewBoxOrderIso μ) (Fin.castOrderIso hn)
  rw [standardSkewTableauCount, if_pos bot_le]
  exact (Fintype.card_congr e).symm

end
end ModifiedCartan


