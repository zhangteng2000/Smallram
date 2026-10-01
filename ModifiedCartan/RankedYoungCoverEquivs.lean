import ModifiedCartan.YoungLatticeDifferential

open scoped Classical

namespace ModifiedCartan
noncomputable section

def youngPredecessorSizedEquiv (μ : YoungDiagram) (n : ℕ) (hμ : partitionSize μ = n) :
    YoungPredecessor μ ≃ {δ : SizedYoungDiagram (n - 1) // PartitionCovers μ δ.val} where
  toFun δ := ⟨⟨δ.val, by have := δ.property.2; omega⟩, δ.property⟩
  invFun δ := ⟨δ.val.val, δ.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def youngSuccessorSizedEquiv (μ : YoungDiagram) (n : ℕ) (hμ : partitionSize μ = n) :
    YoungSuccessor μ ≃ {ξ : SizedYoungDiagram (n + 1) // PartitionCovers ξ.val μ} where
  toFun ξ := ⟨⟨ξ.val, by have := ξ.property.2; omega⟩, ξ.property⟩
  invFun ξ := ⟨ξ.val.val, ξ.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def youngCommonSuccessorSizedEquiv (μ ν : YoungDiagram) (n : ℕ) (hμ : partitionSize μ = n) :
    {ξ : SizedYoungDiagram (n + 1) // PartitionCovers ξ.val μ ∧ PartitionCovers ξ.val ν} ≃
      YoungCommonSuccessor μ ν where
  toFun ξ := ⟨⟨ξ.val.val, ξ.property.1⟩, ξ.property.2⟩
  invFun ξ := ⟨⟨ξ.val.val, by have := ξ.val.property.2; omega⟩, ξ.val.property, ξ.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def youngCommonPredecessorSizedEquiv (μ ν : YoungDiagram) (n : ℕ) (hμ : partitionSize μ = n) :
    {δ : SizedYoungDiagram (n - 1) // PartitionCovers μ δ.val ∧ PartitionCovers ν δ.val} ≃
      YoungCommonPredecessor μ ν where
  toFun δ := ⟨⟨δ.val.val, δ.property.1⟩, δ.property.2⟩
  invFun δ := ⟨⟨δ.val.val, by have := δ.val.property.2; omega⟩, δ.val.property, δ.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

end
end ModifiedCartan


