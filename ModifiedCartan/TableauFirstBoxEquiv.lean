import ModifiedCartan.TableauTail
import ModifiedCartan.TableauPrepend

open scoped BigOperators Classical

namespace ModifiedCartan

noncomputable section

namespace StandardSkewTableau

@[ext] theorem ext_labels {ν μ : YoungDiagram} {T S : StandardSkewTableau ν μ}
    (h : ∀ c, (T.val c : ℕ) = (S.val c : ℕ)) : T = S := by
  apply Subtype.ext
  apply Equiv.ext
  intro c
  exact Fin.ext (h c)

theorem prepend_tailTableau {ν μ : YoungDiagram} (T : StandardSkewTableau ν μ)
    {r : ℕ} (h : AddablePartitionRow μ r) (hc : (r, μ.rowLen r) ∈ ν)
    (hzero : (T.val ⟨(r, μ.rowLen r), addedBox_mem_skew hc⟩ : ℕ) = 0) :
    (T.tailTableau h hc hzero).prependTableau hc = T := by
  apply ext_labels
  intro c
  by_cases he : c.val = (r, μ.rowLen r)
  · have hec : c = ⟨(r, μ.rowLen r), addedBox_mem_skew hc⟩ := Subtype.ext he
    subst c
    rw [prependTableau_first_label, hzero]
  · rw [prependTableau_label_of_ne _ hc c he, tailTableau_label, skewBoxBefore_after]
    have hp := T.label_pos_after_first h hc hzero (skewBoxAfter h c he)
    rw [skewBoxBefore_after] at hp
    omega

theorem tail_prependTableau {ν μ : YoungDiagram} {r : ℕ}
    {h : AddablePartitionRow μ r} (S : StandardSkewTableau ν (addPartitionBox μ r h))
    (hc : (r, μ.rowLen r) ∈ ν) :
    (S.prependTableau hc).tailTableau h hc (S.prependTableau_first_label hc) = S := by
  apply ext_labels
  intro c
  rw [tailTableau_label, prependTableau_label_of_ne _ hc _ (skewBoxBefore_ne_added h c),
    skewBoxAfter_before]
  omega

/-- Exact bijection behind the first-box recurrence for actual tableau counts. -/
def firstBoxEquiv {ν μ : YoungDiagram} {r : ℕ}
    (h : AddablePartitionRow μ r) (hc : (r, μ.rowLen r) ∈ ν) :
    {T : StandardSkewTableau ν μ //
      (T.val ⟨(r, μ.rowLen r), addedBox_mem_skew hc⟩ : ℕ) = 0} ≃
      StandardSkewTableau ν (addPartitionBox μ r h) where
  toFun T := T.val.tailTableau h hc T.property
  invFun S := ⟨S.prependTableau hc, S.prependTableau_first_label hc⟩
  left_inv T := Subtype.ext (T.val.prepend_tailTableau h hc T.property)
  right_inv S := S.tail_prependTableau hc

end StandardSkewTableau
end
end ModifiedCartan


