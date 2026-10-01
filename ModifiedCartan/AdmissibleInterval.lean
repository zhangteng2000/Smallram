import FewInflection.Results
import Mathlib.NumberTheory.Real.Irrational

open scoped Topology
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan

theorem admissibleOrder_not_irrational {n : ℕ} {μ : ℝ}
    (hμ : FewInflection.AdmissibleOrder n μ) : ¬ Irrational μ := by
  rcases hμ with ⟨k, q, _, _, rfl⟩
  intro h
  apply h
  exact ⟨(1 + (k : ℚ) / (q : ℚ)), by push_cast; rfl⟩

/-- The interval collapse in Step 3 of `prop:indices`. The proved density
of irrational numbers suffices, because every admissible order is rational;
local finiteness of the admissible set is unnecessary for this conclusion. -/
theorem admissible_interval_eq {n : ℕ} {a b : EReal}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (h : ∀ μ : ℝ, 0 < μ → a ≤ (μ : EReal) → (μ : EReal) ≤ b →
      FewInflection.AdmissibleOrder n μ) : a = b := by
  apply le_antisymm hab
  by_contra hba
  have hab' : a < b := lt_of_not_ge hba
  obtain ⟨x, hax, hxb⟩ := EReal.exists_between_coe_real hab'
  obtain ⟨y, hxy, hyb⟩ := EReal.exists_between_coe_real hxb
  obtain ⟨μ, hμirr, hxμ, hμy⟩ := exists_irrational_btwn (EReal.coe_lt_coe_iff.mp hxy)
  have hμpos : 0 < μ := by
    have hxpos : (0 : EReal) < (x : EReal) := ha.trans_lt hax
    exact (EReal.coe_lt_coe_iff.mp hxpos).trans hxμ
  have haμ : a ≤ (μ : EReal) := hax.le.trans (EReal.coe_le_coe_iff.mpr hxμ.le)
  have hμb : (μ : EReal) ≤ b := (EReal.coe_le_coe_iff.mpr hμy.le).trans hyb.le
  exact admissibleOrder_not_irrational (h μ hμpos haμ hμb) hμirr

end ModifiedCartan
#print axioms ModifiedCartan.admissible_interval_eq
