import ModifiedCartan.WeakGradientCalculus
import Mathlib.Analysis.Convex.Basic

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- The open supporting cone for a phase, with all ties to other values removed. -/
def strictPhaseCone (A : Finset ℂ) (a : ℂ) : Set ℂ :=
  {w | ∀ b ∈ A, b ≠ a → 0 < ((a - b) * w).re}

theorem isOpen_strictPhaseCone (A : Finset ℂ) (a : ℂ) : IsOpen (strictPhaseCone A a) := by
  have heq : strictPhaseCone A a = ⋂ b ∈ A, {w | b ≠ a → 0 < ((a - b) * w).re} := by
    ext w
    simp only [strictPhaseCone, mem_setOf_eq, mem_iInter]
  rw [heq]
  apply isOpen_biInter_finset
  intro b _
  by_cases hba : b = a
  · simp only [hba, ne_eq, not_true_eq_false, false_implies, setOf_true]
    exact isOpen_univ
  · simp only [hba, ne_eq, not_false_eq_true, true_implies]
    exact isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_const.mul continuous_id))

theorem convex_strictPhaseCone (A : Finset ℂ) (a : ℂ) : Convex ℝ (strictPhaseCone A a) := by
  intro x hx y hy p q hp hq hpq b hb hba
  have hx' := hx b hb hba
  have hy' := hy b hb hba
  have hpos : 0 < p * ((a - b) * x).re + q * ((a - b) * y).re := by
    by_cases hp0 : p = 0
    · have hq1 : q = 1 := by linarith
      simpa only [hp0, hq1, zero_mul, one_mul, zero_add] using hy'
    · have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
      exact add_pos_of_pos_of_nonneg (mul_pos hp' hx') (mul_nonneg hq hy'.le)
  simpa only [mul_add, mul_smul_comm, Complex.smul_re, smul_eq_mul, Complex.add_re] using hpos

theorem strictPhaseCone_smul {A : Finset ℂ} {a w : ℂ}
    (hw : w ∈ strictPhaseCone A a) {t : ℝ} (ht : 0 < t) : t • w ∈ strictPhaseCone A a := by
  intro b hb hba
  simpa only [mul_smul_comm, Complex.smul_re, smul_eq_mul] using mul_pos ht (hw b hb hba)

theorem strictPhaseCone_halfPlane {A : Finset ℂ} {a w : ℂ}
    (hw : w ∈ strictPhaseCone A a) {b : ℂ} (hb : b ∈ A) : ((b - a) * w).re ≤ 0 := by
  by_cases hba : b = a
  · simp only [hba, sub_self, zero_mul, Complex.zero_re, le_refl]
  · have hh := hw b hb hba
    have he : ((b - a) * w).re = -((a - b) * w).re := by
      rw [← Complex.neg_re, ← neg_mul, neg_sub]
    rw [he]
    exact neg_nonpos.mpr hh.le

theorem strictPhaseCone_ae_halfPlane {U : Set ℂ} {g : ℂ → ℂ} {A : Finset ℂ}
    (hA : ∀ᵐ z ∂volume.restrict U, g z ∈ A) {a w : ℂ} (hw : w ∈ strictPhaseCone A a) :
    ∀ᵐ z ∂volume.restrict U, ((g z - a) * w).re ≤ 0 :=
  hA.mono (fun _ hz => strictPhaseCone_halfPlane hw hz)

end ModifiedCartan
#print axioms ModifiedCartan.convex_strictPhaseCone
