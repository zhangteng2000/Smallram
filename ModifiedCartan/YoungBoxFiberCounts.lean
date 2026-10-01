import ModifiedCartan.YoungTranspositionScalar
import ModifiedCartan.FixedPointPermutationSums

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

def youngRowFiberEquiv (μ : YoungDiagram) (r : ℕ) :
    {a : YoungBoxes μ // r = a.val.1} ≃ Fin (μ.rowLen r) where
  toFun a := ⟨a.val.val.2, by
    simpa only [a.property] using (YoungDiagram.mem_iff_lt_rowLen.mp a.val.property)⟩
  invFun j := ⟨⟨(r, j.val), YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt⟩, rfl⟩
  left_inv a := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext a.property rfl
  right_inv j := rfl

def youngColumnFiberEquiv (μ : YoungDiagram) (c : ℕ) :
    {a : YoungBoxes μ // c = a.val.2} ≃ Fin (μ.colLen c) where
  toFun a := ⟨a.val.val.1, by
    simpa only [a.property] using (YoungDiagram.mem_iff_lt_colLen.mp a.val.property)⟩
  invFun j := ⟨⟨(j.val, c), YoungDiagram.mem_iff_lt_colLen.mpr j.isLt⟩, rfl⟩
  left_inv a := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext rfl a.property
  right_inv j := rfl

theorem sum_youngRow_indicator (μ : YoungDiagram) (r : ℕ) :
    (∑ a : YoungBoxes μ, if r = a.val.1 then (1 : ℂ) else 0) = μ.rowLen r := by
  have he := sum_dite_eq_sum_subtype (fun a : YoungBoxes μ => r = a.val.1) (fun _ _ => (1 : ℂ))
  simp only [dite_eq_ite] at he
  rw [he]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [Fintype.card_congr (youngRowFiberEquiv μ r), Fintype.card_fin]

theorem sum_youngColumn_indicator (μ : YoungDiagram) (c : ℕ) :
    (∑ a : YoungBoxes μ, if c = a.val.2 then (1 : ℂ) else 0) = μ.colLen c := by
  have he := sum_dite_eq_sum_subtype (fun a : YoungBoxes μ => c = a.val.2) (fun _ _ => (1 : ℂ))
  simp only [dite_eq_ite] at he
  rw [he]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [Fintype.card_congr (youngColumnFiberEquiv μ c), Fintype.card_fin]

theorem sum_youngPairContent {μ : YoungDiagram} (a : YoungBoxes μ) :
    (∑ b : YoungBoxes μ, youngPairContent a b) =
      (μ.rowLen a.val.1 : ℂ) - (μ.colLen a.val.2 : ℂ) := by
  simp only [youngPairContent, Finset.sum_sub_distrib,
    sum_youngRow_indicator, sum_youngColumn_indicator]

end
end ModifiedCartan


