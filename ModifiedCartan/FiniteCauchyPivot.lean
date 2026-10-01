import ModifiedCartan.DeterminantFirstPivot

open scoped BigOperators Classical

namespace ModifiedCartan
noncomputable section

/-- Auxiliary finite Cauchy kernel for paper `lem:KP-correspondence`. -/
abbrev finiteCauchyMatrix {K : Type*} [Field K] {n : ℕ}
    (x y : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  fun i j => (1 - x i * y j)⁻¹

theorem cauchy_pivot_entry {K : Type*} [Field K] (a b c d : K)
    (_hac : 1 - a * c ≠ 0) (had : 1 - a * d ≠ 0)
    (hbc : 1 - b * c ≠ 0) (hbd : 1 - b * d ≠ 0) :
    (1 - b * d)⁻¹ - ((1 - b * c)⁻¹ / (1 - a * c)⁻¹) * (1 - a * d)⁻¹ =
      ((b - a) / (1 - b * c)) * (((d - c) / (1 - a * d)) * (1 - b * d)⁻¹) := by
  field_simp [had, hbc, hbd]
  field_simp [show 1 - d * a ≠ 0 by simpa [mul_comm] using had]
  ring

theorem finiteCauchyMatrix_det_succ {K : Type*} [Field K] {n : ℕ}
    (x y : Fin (n + 1) → K) (h : ∀ i j, 1 - x i * y j ≠ 0) :
    (finiteCauchyMatrix x y).det =
      (1 - x 0 * y 0)⁻¹ *
        ((∏ i : Fin n, (x i.succ - x 0) / (1 - x i.succ * y 0)) *
          ((∏ j : Fin n, (y j.succ - y 0) / (1 - x 0 * y j.succ)) *
            (finiteCauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ)).det)) := by
  rw [det_first_pivot _ (inv_ne_zero (h 0 0))]
  have he : (fun i j : Fin n =>
      finiteCauchyMatrix x y i.succ j.succ -
        (finiteCauchyMatrix x y i.succ 0 / finiteCauchyMatrix x y 0 0) *
          finiteCauchyMatrix x y 0 j.succ) =
      Matrix.of (fun i j => ((x i.succ - x 0) / (1 - x i.succ * y 0)) *
        (((y j.succ - y 0) / (1 - x 0 * y j.succ)) *
          finiteCauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ) i j)) := by
    ext i j
    exact cauchy_pivot_entry _ _ _ _ (h 0 0) (h 0 j.succ) (h i.succ 0) (h i.succ j.succ)
  have hr := Matrix.det_mul_column
    (fun i : Fin n => (x i.succ - x 0) / (1 - x i.succ * y 0))
    (Matrix.of (fun i j : Fin n =>
      ((y j.succ - y 0) / (1 - x 0 * y j.succ)) *
        finiteCauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ) i j))
  have hc := Matrix.det_mul_row
    (fun j : Fin n => (y j.succ - y 0) / (1 - x 0 * y j.succ))
    (finiteCauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ))
  erw [he, hr, hc]

end
end ModifiedCartan

#print axioms ModifiedCartan.finiteCauchyMatrix_det_succ
