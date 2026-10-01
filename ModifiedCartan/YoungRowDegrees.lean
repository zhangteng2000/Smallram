import ModifiedCartan.YoungColoringMinimum

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

theorem coloringDegree_map {A B C : Type*} [Fintype A] (f : A → B) (g : B → C) :
    coloringDegree (g ∘ f) = Finsupp.mapDomain g (coloringDegree f) := by
  simp only [coloringDegree, Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single,
    Function.comp_apply]

def partitionRowDegree (μ : YoungDiagram) : ℕ →₀ ℕ :=
  coloringDegree (fun b : YoungBoxes μ => b.val.1)

def youngRowBoxesEquiv (μ : YoungDiagram) (r : ℕ) :
    Fin (μ.rowLen r) ≃ {b : YoungBoxes μ // b.val.1 = r} where
  toFun j := ⟨⟨(r, j.val), YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt⟩, rfl⟩
  invFun b := ⟨b.val.val.2, by
    have h := YoungDiagram.mem_iff_lt_rowLen.mp b.val.property
    simpa only [b.property] using h⟩
  left_inv j := rfl
  right_inv b := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext b.property.symm rfl

theorem partitionRowDegree_apply (μ : YoungDiagram) (r : ℕ) :
    partitionRowDegree μ r = μ.rowLen r := by
  letI : DecidableEq ℕ := Classical.decEq _
  rw [partitionRowDegree, coloringDegree_apply, ← Nat.card_eq_fintype_card,
    ← Nat.card_congr (youngRowBoxesEquiv μ r), Nat.card_fin]

theorem partitionRowDegree_injective : Function.Injective partitionRowDegree := by
  intro μ ν h
  apply YoungDiagram.ext
  ext b
  have hr : μ.rowLen b.1 = ν.rowLen b.1 := by
    rw [← partitionRowDegree_apply, ← partitionRowDegree_apply, h]
  change (b.1, b.2) ∈ μ ↔ (b.1, b.2) ∈ ν
  rw [YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_rowLen, hr]

/-- At the minimum row weight, a column-injective coloring has exactly the
row multiplicities of the diagram. -/
theorem weightColoring_minimum_degree {m : ℕ} (μ : YoungDiagram) (d : Fin m →₀ ℕ)
    (f : WeightColoring (YoungBoxes μ) d)
    (hf : ∀ a b, a.val.2 = b.val.2 → f.val a = f.val b → a = b)
    (hw : finiteColorWeight d = partitionRowWeight μ) :
    Finsupp.mapDomain Fin.val d = partitionRowDegree μ := by
  have h := youngColumn_minimum_coloringDegree μ (fun b => (f.val b).val)
    (fun a b hc he => hf a b hc (Fin.ext he))
    ((weightColoring_finite_weight μ d f).trans hw)
  change coloringDegree (Fin.val ∘ f.val) = _ at h
  rwa [coloringDegree_map, f.property] at h

theorem weightColoring_column_collision_of_le_ne {m : ℕ} (μ : YoungDiagram) (d : Fin m →₀ ℕ)
    (hd : finiteColorWeight d ≤ partitionRowWeight μ)
    (hne : Finsupp.mapDomain Fin.val d ≠ partitionRowDegree μ)
    (f : WeightColoring (YoungBoxes μ) d) :
    ∃ a b : YoungBoxes μ, a ≠ b ∧ a.val.2 = b.val.2 ∧ f.val a = f.val b := by
  by_cases hi : ∀ a b : YoungBoxes μ, a.val.2 = b.val.2 → f.val a = f.val b → a = b
  · have hmin := youngColumn_total_min μ (fun b => (f.val b).val)
      (fun a b hc hv => hi a b hc (Fin.ext hv))
    rw [weightColoring_finite_weight μ d f] at hmin
    exact (hne (weightColoring_minimum_degree μ d f hi (Nat.le_antisymm hd hmin))).elim
  · push Not at hi
    obtain ⟨a, b, hc, hf, hne⟩ := hi
    exact ⟨a, b, hne, hc, hf⟩

end
end ModifiedCartan


