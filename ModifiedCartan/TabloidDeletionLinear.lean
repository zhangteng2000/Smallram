import ModifiedCartan.InsertedTabloids

open scoped Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

def youngTabloidInsertLinear (μ : YoungDiagram) (b : YoungCorner μ) :
    YoungPermutationModule (removePartitionBox μ b) →ₗ[ℂ] YoungPermutationModule μ :=
  (MonoidAlgebra.coeffLinearEquiv ℂ).symm.toLinearMap ∘ₗ
    Finsupp.lmapDomain ℂ ℂ (youngTabloidInsert μ b) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

/-- Delete a specified corner letter on its row slice and kill the other rows. -/
def youngTabloidDeleteLinear (μ : YoungDiagram) (b : YoungCorner μ) :
    YoungPermutationModule μ →ₗ[ℂ] YoungPermutationModule (removePartitionBox μ b) :=
  (MonoidAlgebra.coeffLinearEquiv ℂ).symm.toLinearMap ∘ₗ
    Finsupp.lcomapDomain (youngTabloidInsert μ b) (youngTabloidInsert_injective μ b) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

@[simp] theorem youngTabloidDeleteLinear_coeff (μ : YoungDiagram) (b : YoungCorner μ)
    (v : YoungPermutationModule μ) (t : YoungTabloid (removePartitionBox μ b)) :
    (youngTabloidDeleteLinear μ b v).coeff t = v.coeff (youngTabloidInsert μ b t) := rfl

theorem youngTabloidDeleteLinear_insertLinear (μ : YoungDiagram) (b : YoungCorner μ)
    (v : YoungPermutationModule (removePartitionBox μ b)) :
    youngTabloidDeleteLinear μ b (youngTabloidInsertLinear μ b v) = v := by
  apply MonoidAlgebra.ext
  exact Finsupp.comapDomain_mapDomain (youngTabloidInsert μ b)
    (youngTabloidInsert_injective μ b) v.coeff

theorem youngTabloidInsertLinear_single (μ : YoungDiagram) (b : YoungCorner μ)
    (t : YoungTabloid (removePartitionBox μ b)) (z : ℂ) :
    youngTabloidInsertLinear μ b (MonoidAlgebra.single t z) =
      MonoidAlgebra.single (youngTabloidInsert μ b t) z := by
  apply MonoidAlgebra.ext
  exact Finsupp.mapDomain_single

theorem youngTabloidDeleteLinear_single_insert (μ : YoungDiagram) (b : YoungCorner μ)
    (t : YoungTabloid (removePartitionBox μ b)) (z : ℂ) :
    youngTabloidDeleteLinear μ b (MonoidAlgebra.single (youngTabloidInsert μ b t) z) =
      MonoidAlgebra.single t z := by
  rw [← youngTabloidInsertLinear_single, youngTabloidDeleteLinear_insertLinear]

theorem youngTabloidDeleteLinear_single_of_row_ne (μ : YoungDiagram) (b : YoungCorner μ)
    (t : YoungTabloid μ) (z : ℂ) (ht : youngTabloidRows μ t b.val ≠ b.val.val.1) :
    youngTabloidDeleteLinear μ b (MonoidAlgebra.single t z) = 0 := by
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro s
  rw [youngTabloidDeleteLinear_coeff]
  change (Finsupp.single t z) (youngTabloidInsert μ b s) = 0
  apply Finsupp.single_eq_of_ne'
  intro he
  apply ht
  rw [he, youngTabloidInsert_row]

/-- The deletion map intertwines the actual smaller symmetric-group action
with the restriction fixing the removed corner. -/
theorem youngTabloidDeleteLinear_action (μ : YoungDiagram) (b : YoungCorner μ)
    (g : Equiv.Perm (YoungBoxes (removePartitionBox μ b))) (v : YoungPermutationModule μ) :
    youngTabloidDeleteLinear μ b
      (youngTabloidRepresentation μ (youngRemovalPermutationEquiv μ b g).val v) =
        youngTabloidRepresentation (removePartitionBox μ b) g (youngTabloidDeleteLinear μ b v) := by
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro t
  simp only [youngTabloidDeleteLinear_coeff, youngTabloidRepresentation,
    Representation.coeff_ofMulAction, youngTabloidInsert_action, map_inv, Subgroup.coe_inv]

theorem youngTabloidDeleteLinear_eq_zero_iff (μ : YoungDiagram) (b : YoungCorner μ)
    (v : YoungPermutationModule μ) :
    youngTabloidDeleteLinear μ b v = 0 ↔
      ∀ t : YoungTabloid μ, youngTabloidRows μ t b.val = b.val.val.1 → v.coeff t = 0 := by
  constructor
  · intro h t ht
    obtain ⟨s, rfl⟩ := youngTabloidInsert_surjective_row μ b t ht
    rw [← youngTabloidDeleteLinear_coeff, h]
    rfl
  · intro h
    apply MonoidAlgebra.ext
    apply Finsupp.ext
    intro s
    rw [youngTabloidDeleteLinear_coeff]
    exact h _ (youngTabloidInsert_row μ b s)

/-- On the next row cutoff, the kernel of deletion is exactly the previous
cutoff. This is an actual kernel computation, before restricting to Specht. -/
theorem youngTabloidDeleteLinear_kernel_cutoff (μ : YoungDiagram) (b : YoungCorner μ)
    (v : YoungPermutationModule μ)
    (hv : v ∈ youngTabloidRowCutoffSubmodule μ b.val (b.val.val.1 + 1)) :
    youngTabloidDeleteLinear μ b v = 0 ↔ v ∈ youngTabloidRowCutoffSubmodule μ b.val b.val.val.1 := by
  rw [youngTabloidDeleteLinear_eq_zero_iff]
  constructor
  · intro h t ht
    by_cases he : youngTabloidRows μ t b.val = b.val.val.1
    · exact h t he
    · exact hv t (by omega)
  · intro h t ht
    exact h t ht.ge

end
end ModifiedCartan


