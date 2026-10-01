import ModifiedCartan.YoungTabloidCancellation

open scoped BigOperators Classical MonoidAlgebra

namespace ModifiedCartan
noncomputable section

/-- Signed averaging over a subgroup of the box permutations. -/
def youngSubgroupAlternatingOperator (μ : YoungDiagram)
    (H : Subgroup (Equiv.Perm (YoungBoxes μ))) : Module.End ℂ (YoungPermutationModule μ) :=
  ∑ g : H, youngPermutationSign μ g.val • youngTabloidRepresentation μ g.val

theorem youngSubgroupAlternatingOperator_mul (μ : YoungDiagram)
    (H : Subgroup (Equiv.Perm (YoungBoxes μ))) (d : H) :
    youngSubgroupAlternatingOperator μ H * youngTabloidRepresentation μ d.val =
      youngPermutationSign μ d.val • youngSubgroupAlternatingOperator μ H := by
  simp only [youngSubgroupAlternatingOperator, Finset.sum_mul, smul_mul_assoc,
    ← map_mul (youngTabloidRepresentation μ), Finset.smul_sum, smul_smul]
  apply Fintype.sum_equiv (Equiv.mulRight d)
  intro c
  change youngPermutationSign μ c.val • youngTabloidRepresentation μ (c.val * d.val) =
    (youngPermutationSign μ d.val * youngPermutationSign μ (c.val * d.val)) •
      youngTabloidRepresentation μ (c.val * d.val)
  rw [youngPermutationSign_mul]
  have hs : youngPermutationSign μ d.val *
      (youngPermutationSign μ c.val * youngPermutationSign μ d.val) =
        youngPermutationSign μ c.val := by
    calc
      _ = youngPermutationSign μ c.val *
          (youngPermutationSign μ d.val * youngPermutationSign μ d.val) := by ring
      _ = _ := by rw [youngPermutationSign_mul_self, mul_one]
  rw [hs]

theorem youngSubgroupAlternatingOperator_apply_action (μ : YoungDiagram)
    (H : Subgroup (Equiv.Perm (YoungBoxes μ))) (d : H) (v : YoungPermutationModule μ) :
    youngSubgroupAlternatingOperator μ H (youngTabloidRepresentation μ d.val v) =
      youngPermutationSign μ d.val • youngSubgroupAlternatingOperator μ H v := by
  exact congrArg (fun A : Module.End ℂ (YoungPermutationModule μ) => A v)
    (youngSubgroupAlternatingOperator_mul μ H d)

/-- An odd stabilizer forces the signed average to vanish. -/
theorem youngSubgroupAlternatingOperator_zero_of_odd_stabilizer (μ : YoungDiagram)
    (H : Subgroup (Equiv.Perm (YoungBoxes μ))) (d : H) (v : YoungPermutationModule μ)
    (hd : youngTabloidRepresentation μ d.val v = v) (hs : youngPermutationSign μ d.val = -1) :
    youngSubgroupAlternatingOperator μ H v = 0 := by
  have h := youngSubgroupAlternatingOperator_apply_action μ H d v
  rw [hd, hs, neg_one_smul] at h
  let w := youngSubgroupAlternatingOperator μ H v
  have hw : (2 : ℂ) • w = 0 := by
    calc
      _ = w + w := by rw [two_smul]
      _ = w + -w := congrArg (fun x => w + x) h
      _ = 0 := add_neg_cancel w
  exact (smul_eq_zero.mp hw).resolve_left (by norm_num)

end
end ModifiedCartan


