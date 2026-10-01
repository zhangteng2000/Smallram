import ModifiedCartan.WeakGradientLocalConstancy
import ModifiedCartan.ClassicalWeakGradient

open scoped Topology
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem classicalComplexGradient_affine (a z : ℂ) :
    classicalComplexGradient (fun w => (a * w).re) z = a :=
  classicalComplexGradient_re_of_hasDerivAt (hasDerivAt_const_mul a)

theorem hasWeakComplexGradient_affine (U : Set ℂ) (a : ℂ) :
    HasWeakComplexGradient U (fun w => (a * w).re) (fun _ => a) := by
  have hd : ContDiff ℝ 1 (fun w : ℂ => (a * w).re) :=
    Complex.reCLM.contDiff.comp (contDiff_const.mul contDiff_id)
  have he : classicalComplexGradient (fun w => (a * w).re) = (fun _ => a) :=
    funext (classicalComplexGradient_affine a)
  rw [← he]
  exact contDiff_hasWeakComplexGradient hd U

theorem HasWeakComplexGradient.affine_difference_of_ae_const
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U) {u : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : HasWeakComplexGradient U u g) (hc : Continuous u) {a : ℂ}
    (hg : g =ᵐ[volume.restrict U] (fun _ => a)) {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U) :
    u y - u x = (a * (y - x)).re := by
  have hv := hu.add (hasWeakComplexGradient_affine U (-a))
  have hvc : Continuous (u + fun z => (-a * z).re) :=
    hc.add (Complex.continuous_re.comp (continuous_const.mul continuous_id))
  have hzero : (g + fun _ => -a) =ᵐ[volume.restrict U] (fun _ => 0) := by
    filter_upwards [hg] with z hz
    simp only [Pi.add_apply, hz, add_neg_cancel]
  obtain ⟨k, hk⟩ := hv.exists_const_of_ae_zero hU hUc hvc hzero
  have hx' := hk x hx
  have hy' := hk y hy
  simp only [Pi.add_apply, neg_mul, Complex.neg_re] at hx' hy'
  simp only [mul_sub, Complex.sub_re]
  linarith

end ModifiedCartan
#print axioms ModifiedCartan.HasWeakComplexGradient.affine_difference_of_ae_const

