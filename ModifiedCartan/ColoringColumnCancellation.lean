import ModifiedCartan.WeightColoringRepresentation
import ModifiedCartan.YoungTabloidCancellation

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

theorem weightColoring_swap_fixed {B : Type*} (μ : YoungDiagram) (d : B →₀ ℕ)
    (f : WeightColoring (YoungBoxes μ) d) (a b : YoungBoxes μ)
    (hc : f.val a = f.val b) : Equiv.swap a b • f = f := by
  rw [weightColoring_fixed_iff]
  exact permutationFiberSubgroup_swap_mem f.val hc

/-- A column-sign vector has zero coefficient at every coloring with a
same-column collision. -/
theorem columnSignVector_collision_coeff {B : Type*} (μ : YoungDiagram) (d : B →₀ ℕ)
    (v : ℂ[WeightColoring (YoungBoxes μ) d])
    (hv : ∀ c : youngColumnSubgroup μ,
      weightColoringRepresentation (YoungBoxes μ) d c.val v = youngPermutationSign μ c.val • v)
    (f : WeightColoring (YoungBoxes μ) d) (a b : YoungBoxes μ)
    (hne : a ≠ b) (hcol : a.val.2 = b.val.2) (hc : f.val a = f.val b) :
    v.coeff f = 0 := by
  let c : youngColumnSubgroup μ := ⟨Equiv.swap a b,
    permutationFiberSubgroup_swap_mem (fun b : YoungBoxes μ => b.val.2) hcol⟩
  have h := congrArg (fun u : ℂ[WeightColoring (YoungBoxes μ) d] => u.coeff f) (hv c)
  have hs : youngPermutationSign μ c.val = -1 := youngPermutationSign_swap μ a b hne
  change (Representation.ofMulAction ℂ (Equiv.Perm (YoungBoxes μ))
    (WeightColoring (YoungBoxes μ) d) c.val v).coeff f = _ at h
  rw [Representation.coeff_ofMulAction, hs, MonoidAlgebra.coeff_smul_apply, neg_one_smul] at h
  have hi : c.val⁻¹ • f = f := by
    change (Equiv.swap a b)⁻¹ • f = f
    rw [Equiv.swap_inv, weightColoring_swap_fixed μ d f a b hc]
  rw [hi] at h
  have hz : (2 : ℂ) * v.coeff f = 0 := by
    calc
      _ = v.coeff f + v.coeff f := by ring
      _ = v.coeff f + -v.coeff f := congrArg (fun z : ℂ => v.coeff f + z) h
      _ = 0 := add_neg_cancel _
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

end
end ModifiedCartan


