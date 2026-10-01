import ModifiedCartan.PartitionCorners

open scoped Classical

namespace ModifiedCartan
noncomputable section

def youngBoxBeforeRemoval (μ : YoungDiagram) (b : YoungCorner μ)
    (a : YoungBoxes (removePartitionBox μ b)) : YoungBoxes μ :=
  ⟨a.val, ((mem_removePartitionBox μ b a.val).mp a.property).2⟩

theorem youngBoxBeforeRemoval_ne (μ : YoungDiagram) (b : YoungCorner μ)
    (a : YoungBoxes (removePartitionBox μ b)) : youngBoxBeforeRemoval μ b a ≠ b.val := by
  intro he
  exact ((mem_removePartitionBox μ b a.val).mp a.property).1 (congrArg Subtype.val he)

theorem youngBoxBeforeRemoval_injective (μ : YoungDiagram) (b : YoungCorner μ) :
    Function.Injective (youngBoxBeforeRemoval μ b) := by
  intro a c he
  have hv := congrArg (fun x : YoungBoxes μ => x.val) he
  exact Subtype.ext hv

def youngBoxAfterRemoval (μ : YoungDiagram) (b : YoungCorner μ)
    (a : YoungBoxes μ) (ha : a ≠ b.val) : YoungBoxes (removePartitionBox μ b) :=
  ⟨a.val, (mem_removePartitionBox μ b a.val).mpr
    ⟨fun he => ha (Subtype.ext he), a.property⟩⟩

@[simp] theorem youngBoxBeforeAfterRemoval (μ : YoungDiagram) (b : YoungCorner μ)
    (a : YoungBoxes μ) (ha : a ≠ b.val) :
    youngBoxBeforeRemoval μ b (youngBoxAfterRemoval μ b a ha) = a := rfl

@[simp] theorem youngBoxAfterBeforeRemoval (μ : YoungDiagram) (b : YoungCorner μ)
    (a : YoungBoxes (removePartitionBox μ b)) :
    youngBoxAfterRemoval μ b (youngBoxBeforeRemoval μ b a)
      (youngBoxBeforeRemoval_ne μ b a) = a := rfl

def youngRemovedBoxesEquiv (μ : YoungDiagram) (b : YoungCorner μ) :
    YoungBoxes (removePartitionBox μ b) ≃ {a : YoungBoxes μ // a ≠ b.val} where
  toFun a := ⟨youngBoxBeforeRemoval μ b a, youngBoxBeforeRemoval_ne μ b a⟩
  invFun a := youngBoxAfterRemoval μ b a.val a.property
  left_inv a := rfl
  right_inv a := rfl

end
end ModifiedCartan


