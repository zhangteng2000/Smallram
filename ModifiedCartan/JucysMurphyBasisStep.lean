import ModifiedCartan.JucysMurphyRestriction
import ModifiedCartan.LastLetterSpectrum

open scoped Classical

namespace ModifiedCartan
noncomputable section

variable {A : Type*} [Fintype A] [LinearOrder A]

/-- An actual tableau-indexed simultaneous eigenbasis with distinct joint values. -/
structure SimpleJucysMurphyBasis (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ) where
  basis : Module.Basis (StandardYoungTableau μ) ℂ (YoungSpechtModule μ)
  values : StandardYoungTableau μ → A → ℂ
  values_injective : Function.Injective values
  eigen : ∀ t i, (spechtRepresentationOn μ h).asAlgebraHom (jucysMurphyElement i) (basis t) =
    values t i • basis t

def simpleJucysMurphyBasisStep (μ : YoungDiagram) (h : Fintype.card A = partitionSize μ)
    (a : A) (ha : ∀ i : A, i ≤ a)
    (D : ∀ b : YoungCorner μ, SimpleJucysMurphyBasis (removePartitionBox μ b)
      (card_erase_eq_partition_remove μ h a b)) : SimpleJucysMurphyBasis μ h := by
  have hpos : 0 < partitionSize μ := by rw [← h]; exact Fintype.card_pos_iff.mpr ⟨a⟩
  let B := spechtCornerBasis μ h a (fun c => (D c).basis)
  let e := lastLetterSpectrum a (fun c : YoungCorner μ => (c.val.val.2 : ℂ) - (c.val.val.1 : ℂ))
    (fun c => (D c).values)
  have he : Function.Injective e := lastLetterSpectrum_injective a _ (youngCorner_content_injective μ)
    _ (fun c => (D c).values_injective)
  have hB (p : Σ c : YoungCorner μ, StandardYoungTableau (removePartitionBox μ c)) (i : A) :
      (spechtRepresentationOn μ h).asAlgebraHom (jucysMurphyElement i) (B p) = e p i • B p := by
    change (spechtRepresentationOn μ h).asAlgebraHom (jucysMurphyElement i)
      (spechtCornerBasis μ h a (fun c => (D c).basis) p) = _
    rw [spechtCornerBasis_apply]
    change (spechtRepresentationOn μ h).asAlgebraHom (jucysMurphyElement i)
      (spechtCornerEmbedding μ h a p.1 ((D p.1).basis p.2)) =
      e p i • spechtCornerEmbedding μ h a p.1 ((D p.1).basis p.2)
    by_cases hi : i = a
    · subst i
      change _ = (if h : a = a then _ else _) • _
      rw [dite_eq_left rfl]
      exact jucysMurphy_corner_max μ h a ha p.1 ((D p.1).basis p.2)
    · let i' : ↥(Finset.univ.erase a) := ⟨i, by simp [hi]⟩
      have hv := jucysMurphy_corner_restriction μ h a ha p.1 i' ((D p.1).basis p.2)
      rw [(D p.1).eigen p.2 i', map_smul] at hv
      simpa only [e, lastLetterSpectrum, dite_eq_right hi] using hv
  let E := youngTableauCornerEquiv μ hpos
  refine { basis := B.reindex E.symm
           values := fun t => e (E t)
           values_injective := he.comp E.injective
           eigen := ?_ }
  intro t i
  rw [Module.Basis.reindex_apply]
  exact hB (E t) i

end
end ModifiedCartan


