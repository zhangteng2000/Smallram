import ModifiedCartan.DichotomyKernels
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped Topology
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem exp_time_difference (a : ℂ) (t s : ℝ) :
    Complex.exp (a * ((t - s : ℝ) : ℂ)) =
      Complex.exp (a * (t : ℂ)) * Complex.exp (-a * (s : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem dichotomyIntegral_forward_eq {a : ℂ} (ha : a.re < 0)
    (T : ℝ) (f : ℝ → ℂ) {t : ℝ} (ht : T ≤ t) :
    dichotomyIntegral a T f t = Complex.exp (a * (t : ℂ)) *
      ∫ s in T..t, Complex.exp (-a * (s : ℂ)) * f s := by
  unfold dichotomyIntegral
  simp only [dichotomyKernel, ite_eq_left ha, ← indicator_mul_left]
  rw [setIntegral_indicator measurableSet_Iic, Ici_inter_Iic,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]
  simp_rw [exp_time_difference, mul_assoc]
  exact intervalIntegral.integral_const_mul _ _

theorem dichotomyIntegral_backward_eq {a : ℂ} (ha : 0 ≤ a.re)
    (T : ℝ) (f : ℝ → ℂ) {t : ℝ} (ht : T ≤ t) :
    dichotomyIntegral a T f t = -Complex.exp (a * (t : ℂ)) *
      ∫ s in Ici t, Complex.exp (-a * (s : ℂ)) * f s := by
  unfold dichotomyIntegral
  simp only [dichotomyKernel, ite_eq_right (not_lt.mpr ha), neg_mul, ← indicator_mul_left]
  rw [integral_neg, setIntegral_indicator measurableSet_Ici,
    inter_eq_right.mpr (Ici_subset_Ici.mpr ht)]
  simp_rw [exp_time_difference, mul_assoc]
  rw [integral_const_mul]
  ring

theorem integrable_exp_weight {a : ℂ} (ha : 0 ≤ a.re) {T : ℝ} {f : ℝ → ℂ}
    (hf : IntegrableOn f (Ici T)) :
    IntegrableOn (fun s : ℝ => Complex.exp (-a * (s : ℂ)) * f s) (Ici T) := by
  have hc : Continuous (fun s : ℝ => Complex.exp (-a * (s : ℂ))) := by fun_prop
  apply Integrable.bdd_mul hf hc.aestronglyMeasurable (c := Real.exp (-a.re * T))
  filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
  rw [Complex.norm_exp, Real.exp_le_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  exact mul_le_mul_of_nonpos_left hs (neg_nonpos.mpr ha)

noncomputable def dichotomyInitialConstant (a : ℂ) (T : ℝ) (f : ℝ → ℂ) : ℂ :=
  if a.re < 0 then 0 else -(∫ s in Ici T, Complex.exp (-a * (s : ℂ)) * f s)

theorem dichotomyIntegral_primitive_eq (a : ℂ) {T : ℝ} {f : ℝ → ℂ}
    (hf : IntegrableOn f (Ici T)) {t : ℝ} (ht : T ≤ t) :
    dichotomyIntegral a T f t = Complex.exp (a * (t : ℂ)) *
      (dichotomyInitialConstant a T f + ∫ s in T..t, Complex.exp (-a * (s : ℂ)) * f s) := by
  by_cases ha : a.re < 0
  · simpa only [dichotomyInitialConstant, ite_eq_left ha, zero_add]
      using dichotomyIntegral_forward_eq ha T f ht
  · have hw := integrable_exp_weight (le_of_not_gt ha) hf
    have he := intervalIntegral.integral_Ici_sub_Ici' hw (hw.mono_set (Ici_subset_Ici.mpr ht))
    rw [dichotomyIntegral_backward_eq (le_of_not_gt ha) T f ht]
    simp only [dichotomyInitialConstant, ite_eq_right ha]
    rw [← he]
    ring

/-- The actual integral equation differentiates to u'=a*u+f, including the endpoint. -/
theorem dichotomyIntegral_hasDerivWithinAt (a : ℂ) {T : ℝ} {f : ℝ → ℂ}
    (hf : IntegrableOn f (Ici T)) (hc : Continuous f) {t : ℝ} (ht : T ≤ t) :
    HasDerivWithinAt (dichotomyIntegral a T f)
      (a * dichotomyIntegral a T f t + f t) (Ici T) t := by
  let p : ℝ → ℂ := fun s => Complex.exp (-a * (s : ℂ)) * f s
  have hp : Continuous p := by dsimp [p]; fun_prop
  have hd := intervalIntegral.integral_hasDerivAt_right (hp.intervalIntegrable T t)
    hp.aestronglyMeasurable.stronglyMeasurableAtFilter hp.continuousAt
  have he : HasDerivAt (fun s : ℝ => Complex.exp (a * (s : ℂ)))
      (Complex.exp (a * (t : ℂ)) * a) t := by
    simpa only [mul_one, id_eq] using! (((hasDerivAt_id (t : ℂ)).const_mul a).cexp).comp_ofReal
  have hprod := he.mul (hd.const_add (dichotomyInitialConstant a T f))
  have hexp : Complex.exp (a * (t : ℂ)) * Complex.exp (-a * (t : ℂ)) = 1 := by
    rw [← Complex.exp_add, show a * (t : ℂ) + -a * (t : ℂ) = 0 by ring, Complex.exp_zero]
  have hvalue : (Complex.exp (a * (t : ℂ)) * a) *
        (dichotomyInitialConstant a T f + ∫ s in T..t, p s) +
        Complex.exp (a * (t : ℂ)) * p t = a * dichotomyIntegral a T f t + f t := by
    rw [dichotomyIntegral_primitive_eq a hf ht]
    dsimp [p]
    calc
      _ = a * (Complex.exp (a * (t : ℂ)) *
          (dichotomyInitialConstant a T f + ∫ s in T..t, Complex.exp (-a * (s : ℂ)) * f s)) +
          (Complex.exp (a * (t : ℂ)) * Complex.exp (-a * (t : ℂ))) * f t := by ring
      _ = _ := by rw [hexp, one_mul]
  rw [hvalue] at hprod
  exact hprod.hasDerivWithinAt.congr_of_mem
    (fun s hs => dichotomyIntegral_primitive_eq a hf hs) ht

theorem dichotomyIntegral_continuousOn (a : ℂ) {T : ℝ} {f : ℝ → ℂ}
    (hf : IntegrableOn f (Ici T)) (hc : Continuous f) :
    ContinuousOn (dichotomyIntegral a T f) (Ici T) :=
  fun _ ht => (dichotomyIntegral_hasDerivWithinAt a hf hc ht).continuousWithinAt

end ModifiedCartan
#print axioms ModifiedCartan.dichotomyIntegral_hasDerivWithinAt

