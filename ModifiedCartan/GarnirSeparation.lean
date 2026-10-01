import ModifiedCartan.GarnirBelt
import ModifiedCartan.YoungFillings
import Mathlib.Order.Fin.Basic

open scoped Classical

namespace ModifiedCartan
noncomputable section

theorem youngRowStandard_of_adjacent (μ : YoungDiagram) (T : YoungFilling μ)
    (h : ∀ (r j : ℕ) (hl : (r, j) ∈ μ) (hr : (r, j + 1) ∈ μ),
      T ⟨(r, j), hl⟩ < T ⟨(r, j + 1), hr⟩) : YoungRowStandard T := by
  rintro ⟨⟨r, j⟩, hj⟩ ⟨⟨s, k⟩, hk⟩ hrs hjk
  dsimp at hrs hjk
  subst s
  have hj' := YoungDiagram.mem_iff_lt_rowLen.mp hj
  have hk' := YoungDiagram.mem_iff_lt_rowLen.mp hk
  cases hn : μ.rowLen r with
  | zero => omega
  | succ m =>
    let f : Fin (m + 1) → Fin (partitionSize μ) := fun i =>
      T ⟨(r, i.val), YoungDiagram.mem_iff_lt_rowLen.mpr (by rw [hn]; exact i.isLt)⟩
    have hf : StrictMono f := Fin.strictMono_iff_lt_succ.mpr (fun i => h r i.val _ _)
    exact hf (a := ⟨j, by omega⟩) (b := ⟨k, by omega⟩) hjk

theorem young_not_row_standard_adjacent_inversion (μ : YoungDiagram) (T : YoungFilling μ)
    (hn : ¬ YoungRowStandard T) :
    ∃ (r j : ℕ) (hl : (r, j) ∈ μ) (hr : (r, j + 1) ∈ μ),
      T ⟨(r, j + 1), hr⟩ < T ⟨(r, j), hl⟩ := by
  by_contra h
  push Not at h
  apply hn
  apply youngRowStandard_of_adjacent μ T
  intro r j hl hr
  apply lt_of_le_of_ne (h r j hl hr)
  intro he
  have hc := congrArg (fun b : YoungBoxes μ => b.val.2) (T.injective he)
  dsimp at hc
  omega

theorem youngColumnStandard_le {μ : YoungDiagram} {T : YoungFilling μ}
    (hT : YoungColumnStandard T) (a b : YoungBoxes μ)
    (hr : a.val.1 ≤ b.val.1) (hc : a.val.2 = b.val.2) : T a ≤ T b := by
  rcases lt_or_eq_of_le hr with hlt | heq
  · exact (hT a b hlt hc).le
  · have hab : a = b := Subtype.ext (Prod.ext heq hc)
    rw [hab]

/-- At an adjacent row inversion, every label in the left tail is larger
than every label in the right head. -/
theorem garnir_labels_separated (μ : YoungDiagram) (T : YoungFilling μ)
    (hT : YoungColumnStandard T) (r j : ℕ) (hl : (r, j) ∈ μ) (hr : (r, j + 1) ∈ μ)
    (hinv : T ⟨(r, j + 1), hr⟩ < T ⟨(r, j), hl⟩)
    (a b : YoungBoxes μ) (ha : a ∈ garnirLeft μ r j) (hb : b ∈ garnirRight μ r j) :
    T b < T a := by
  have ha' := (mem_garnirLeft μ r j a).mp ha
  have hb' := (mem_garnirRight μ r j b).mp hb
  have hleft : T ⟨(r, j), hl⟩ ≤ T a := youngColumnStandard_le hT _ _ ha'.2 ha'.1.symm
  have hright : T b ≤ T ⟨(r, j + 1), hr⟩ := youngColumnStandard_le hT _ _ hb'.2 hb'.1
  exact hright.trans_lt (hinv.trans_le hleft)

end
end ModifiedCartan


