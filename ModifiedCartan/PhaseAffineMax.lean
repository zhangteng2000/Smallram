import ModifiedCartan.StrictPhaseCone
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.Lattice

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

noncomputable def phaseAffineMax (A : Finset ℂ) (hA : A.Nonempty) (k : ℝ) (c x : ℂ) : ℝ :=
  A.sup' hA (fun a => k + (a * (x - c)).re)

theorem continuous_phaseAffineMax (A : Finset ℂ) (hA : A.Nonempty) (k : ℝ) (c : ℂ) :
    Continuous (phaseAffineMax A hA k c) :=
  Continuous.finset_sup'_apply hA (fun a _ => continuous_const.add
    (Complex.continuous_re.comp (continuous_const.mul (continuous_id.sub continuous_const))))

theorem phaseAffineMax_eq_on_strict_cone {A : Finset ℂ} (hA : A.Nonempty) (k : ℝ)
    {a c x : ℂ} (ha : a ∈ A) (hx : x - c ∈ strictPhaseCone A a) :
    phaseAffineMax A hA k c x = k + (a * (x - c)).re := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro b hb
    have hh := strictPhaseCone_halfPlane hx hb
    simp only [sub_mul, Complex.sub_re] at hh
    linarith
  · exact Finset.le_sup' (fun b => k + (b * (x - c)).re) ha

theorem convexOn_phaseAffineMax {V : Set ℂ} (hV : Convex ℝ V)
    (A : Finset ℂ) (hA : A.Nonempty) (k : ℝ) (c : ℂ) :
    ConvexOn ℝ V (phaseAffineMax A hA k c) := by
  refine ⟨hV, ?_⟩
  intro x hx y hy p q hp hq hpq
  apply Finset.sup'_le
  intro a ha
  have he : k + (a * (p • x + q • y - c)).re =
      p * (k + (a * (x - c)).re) + q * (k + (a * (y - c)).re) := by
    simp only [mul_sub, mul_add, mul_smul_comm, Complex.sub_re, Complex.add_re,
      Complex.smul_re, smul_eq_mul]
    have hh := congrArg (fun t : ℝ => t * (k - (a * c).re)) hpq
    nlinarith
  rw [he]
  exact add_le_add (mul_le_mul_of_nonneg_left (Finset.le_sup' (fun b => k + (b * (x - c)).re) ha) hp)
    (mul_le_mul_of_nonneg_left (Finset.le_sup' (fun b => k + (b * (y - c)).re) ha) hq)

end ModifiedCartan
#print axioms ModifiedCartan.convexOn_phaseAffineMax

