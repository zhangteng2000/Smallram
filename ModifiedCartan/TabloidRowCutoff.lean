import ModifiedCartan.SupportedPermutations
import ModifiedCartan.FillingCoefficients

open scoped Classical

namespace ModifiedCartan
noncomputable section

def youngLetterStabilizer (μ : YoungDiagram) (a : YoungBoxes μ) :
    Subgroup (Equiv.Perm (YoungBoxes μ)) :=
  supportedPermutationSubgroup (Finset.univ.erase a)

theorem youngLetterStabilizer_fixes (μ : YoungDiagram) (a : YoungBoxes μ)
    (g : youngLetterStabilizer μ a) : g.val a = a := g.property a (by simp)

theorem youngTabloidRows_letter_action (μ : YoungDiagram) (a : YoungBoxes μ)
    (g : youngLetterStabilizer μ a) (t : YoungTabloid μ) :
    youngTabloidRows μ (g.val • t) a = youngTabloidRows μ t a := by
  rw [youngTabloidRows_smul]
  have hg : g.val⁻¹ a = a := youngLetterStabilizer_fixes μ a g⁻¹
  rw [hg]

theorem youngTabloidRows_lt_height (μ : YoungDiagram) (t : YoungTabloid μ) (a : YoungBoxes μ) :
    youngTabloidRows μ t a < μ.colLen 0 := by
  induction t using Quotient.inductionOn with | h g =>
    change (g⁻¹ a).val.1 < μ.colLen 0
    exact (YoungDiagram.mem_iff_lt_colLen.mp (g⁻¹ a).property).trans_le
      (μ.colLen_anti 0 (g⁻¹ a).val.2 (Nat.zero_le _))

/-- Vectors supported on tabloids where a fixed letter lies strictly above
the row cutoff. -/
def youngTabloidRowCutoffSubmodule (μ : YoungDiagram) (a : YoungBoxes μ) (r : ℕ) :
    Submodule ℂ (YoungPermutationModule μ) where
  carrier := {v | ∀ t : YoungTabloid μ, r ≤ youngTabloidRows μ t a → v.coeff t = 0}
  zero_mem' := by intro t ht; rfl
  add_mem' := by
    intro v w hv hw t ht
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, hv t ht, hw t ht, add_zero]
  smul_mem' := by
    intro z v hv t ht
    simp only [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, hv t ht, smul_zero]

theorem youngTabloidRowCutoffSubmodule_mono (μ : YoungDiagram) (a : YoungBoxes μ) :
    Monotone (youngTabloidRowCutoffSubmodule μ a) := by
  intro r s hrs v hv t ht
  exact hv t (hrs.trans ht)

theorem youngTabloidRowCutoffSubmodule_zero (μ : YoungDiagram) (a : YoungBoxes μ) :
    youngTabloidRowCutoffSubmodule μ a 0 = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro v hv
  change v = 0
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro t
  exact hv t (Nat.zero_le _)

theorem youngTabloidRowCutoffSubmodule_height (μ : YoungDiagram) (a : YoungBoxes μ) :
    youngTabloidRowCutoffSubmodule μ a (μ.colLen 0) = ⊤ := by
  apply le_antisymm le_top
  intro v _ t ht
  exact False.elim ((youngTabloidRows_lt_height μ t a).not_ge ht)

def youngLetterRepresentation (μ : YoungDiagram) (a : YoungBoxes μ) :
    Representation ℂ (youngLetterStabilizer μ a) (YoungPermutationModule μ) :=
  (youngTabloidRepresentation μ).comp (youngLetterStabilizer μ a).subtype

/-- Fixing a letter preserves its row cutoff, giving an actual invariant subspace. -/
def youngTabloidRowCutoff (μ : YoungDiagram) (a : YoungBoxes μ) (r : ℕ) :
    Subrepresentation (youngLetterRepresentation μ a) where
  toSubmodule := youngTabloidRowCutoffSubmodule μ a r
  apply_mem_toSubmodule := by
    intro g v hv t ht
    change (youngTabloidRepresentation μ g.val v).coeff t = 0
    rw [youngTabloidRepresentation, Representation.coeff_ofMulAction]
    have hrow := youngTabloidRows_letter_action μ a g⁻¹ t
    change youngTabloidRows μ (g.val⁻¹ • t) a = youngTabloidRows μ t a at hrow
    apply hv
    rwa [hrow]

end
end ModifiedCartan


