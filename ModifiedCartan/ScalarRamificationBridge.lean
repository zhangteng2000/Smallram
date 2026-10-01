import ModifiedCartan.ScalarCurveLift
import ModifiedCartan.WronskianNontrivial
import FewInflection.FundamentalAnalytic

open scoped Topology BigOperators
open Filter Set MeromorphicOn
set_option autoImplicit false
namespace ModifiedCartan

theorem scalar_wronskian_formula (F : Curve 1) (z : ℂ) :
    FewInflection.wronskian 1 F.coord z =
      F.coord 0 z * deriv (F.coord 1) z - F.coord 1 z * deriv (F.coord 0) z := by
  let A : Matrix (Fin 2) (Fin 2) ℂ := fun i j => iteratedDeriv (i : ℕ) (F.coord j) z
  simpa only [FewInflection.wronskian, A, Fin.val_zero, Fin.val_one,
    iteratedDeriv_zero, iteratedDeriv_one] using! Matrix.det_fin_two A

theorem scalar_curve_coordinate_nontrivial (F : Curve 1)
    (hlin : F.linearlyNonDegenerate) (j : Index 1) : ∃ z, F.coord j z ≠ 0 := by
  by_contra hn
  push Not at hn
  have h : LinearIndependent ℂ F.coord := hlin
  exact h.ne_zero j (funext hn)

/-- The literal quotient rule identifies the scalar derivative with the
Wronskian, away only from the actual discrete exceptional set. -/
theorem scalar_deriv_times_denominator_sq {f : ℂ → ℂ} (hf : Meromorphic f)
    (F : Curve 1) (hlin : F.linearlyNonDegenerate)
    (he : f =ᶠ[codiscreteWithin (univ : Set ℂ)] (fun z => F.coord 1 z / F.coord 0 z)) :
    deriv f * (F.coord 0) ^ 2 =ᶠ[codiscreteWithin (univ : Set ℂ)]
      (fun z => FewInflection.wronskian 1 F.coord z) := by
  have hp : MeromorphicOn (F.coord 1) univ := fun z _ => (F.holomorphic 1).analyticAt z |>.meromorphicAt
  have hq : MeromorphicOn (F.coord 0) univ := fun z _ => (F.holomorphic 0).analyticAt z |>.meromorphicAt
  have hd := hf.meromorphicOn.deriv_eventuallyEq_codiscreteWithin (hp.div hq) he
  have hqn := MeromorphicAt.MeromorphicOn.codiscreteWithin_setOfPred_ne_zero hq
    (fun z _ => entire_meromorphicOrder_ne_top (F.holomorphic 0)
      (scalar_curve_coordinate_nontrivial F hlin 0) z)
  filter_upwards [hd, hqn] with z hz hzq
  change deriv f z * (F.coord 0 z) ^ 2 = _
  rw [hz, deriv_div (F.holomorphic 1 z) (F.holomorphic 0 z) hzq,
    div_mul_cancel₀ _ (pow_ne_zero _ hzq), scalar_wronskian_formula]
  ring

/-- Exact identification of the intrinsic scalar critical divisor with the
Wronskian divisor of its actual reduced lift. LaTeX `smal`, used in `thm:A`. -/
theorem scalarCriticalDivisor_eq_wronskian {f : ℂ → ℂ} (hf : Meromorphic f)
    (F : Curve 1) (hlin : F.linearlyNonDegenerate)
    (he : f =ᶠ[codiscreteWithin (univ : Set ℂ)] (fun z => F.coord 1 z / F.coord 0 z))
    (hD : divisor (F.coord 0) univ = (divisor f univ)⁻) :
    scalarCriticalDivisor f = divisor (fun z => FewInflection.wronskian 1 F.coord z) univ := by
  let W : ℂ → ℂ := fun z => FewInflection.wronskian 1 F.coord z
  have hWA : Differentiable ℂ W :=
    fun z => (FewInflection.analyticAt_wronskian (fun j => (F.holomorphic j).analyticAt z)).differentiableAt
  have hW : MeromorphicOn W univ := fun z _ => (hWA.analyticAt z).meromorphicAt
  have hWfin (z : ℂ) : meromorphicOrderAt W z ≠ ⊤ :=
    entire_meromorphicOrder_ne_top hWA (curve_wronskian_nontrivial F hlin) z
  have hq : MeromorphicOn (F.coord 0) univ := fun z _ => (F.holomorphic 0).analyticAt z |>.meromorphicAt
  have hd : MeromorphicOn (deriv f) univ := hf.meromorphicOn.deriv
  have hq2 : MeromorphicOn ((F.coord 0) ^ 2) univ := hq.pow 2
  have hprod := hd.mul hq2
  have hident := scalar_deriv_times_denominator_sq hf F hlin he
  have hdfin (z : ℂ) : meromorphicOrderAt (deriv f) z ≠ ⊤ := by
    intro htop
    have ho := meromorphicOrderAt_congr
      ((hprod z (mem_univ z)).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
        (hW z (mem_univ z)) (mem_univ z) PerfectSpace.univ_preperfect hident)
    rw [meromorphicOrderAt_mul (hd z (mem_univ z)) (hq2 z (mem_univ z)), htop] at ho
    exact hWfin z (by simpa only [WithTop.top_add] using ho.symm)
  have hqfin (z : ℂ) : meromorphicOrderAt ((F.coord 0) ^ 2) z ≠ ⊤ := by
    rw [meromorphicOrderAt_pow (hq z (mem_univ z))]
    have hh := entire_meromorphicOrder_ne_top (F.holomorphic 0)
      (scalar_curve_coordinate_nontrivial F hlin 0) z
    lift meromorphicOrderAt (F.coord 0) z to ℤ using hh with k hk
    change ((2 : ℤ) : WithTop ℤ) * (k : WithTop ℤ) ≠ ⊤
    rw [← WithTop.coe_mul]
    exact WithTop.coe_ne_top
  have heD := divisor_congr_codiscreteWithin hident isOpen_univ
  rw [divisor_mul hd hq2 (fun z _ => hdfin z) (fun z _ => hqfin z), divisor_pow hq, hD] at heD
  exact heD

theorem scalarCriticalDivisor_nonneg_of_lift {f : ℂ → ℂ} (hf : Meromorphic f)
    (F : Curve 1) (hlin : F.linearlyNonDegenerate)
    (he : f =ᶠ[codiscreteWithin (univ : Set ℂ)] (fun z => F.coord 1 z / F.coord 0 z))
    (hD : divisor (F.coord 0) univ = (divisor f univ)⁻) : 0 ≤ scalarCriticalDivisor f := by
  rw [scalarCriticalDivisor_eq_wronskian hf F hlin he hD]
  exact (show AnalyticOnNhd ℂ (fun z => FewInflection.wronskian 1 F.coord z) univ from
    fun z _ => FewInflection.analyticAt_wronskian (fun j => (F.holomorphic j).analyticAt z)).divisor_nonneg

theorem scalarRamification_eq_curve {f : ℂ → ℂ} (hf : Meromorphic f)
    (F : Curve 1) (hlin : F.linearlyNonDegenerate)
    (he : f =ᶠ[codiscreteWithin (univ : Set ℂ)] (fun z => F.coord 1 z / F.coord 0 z))
    (hD : divisor (F.coord 0) univ = (divisor f univ)⁻) : scalarRamification f = ramification F := by
  unfold scalarRamification
  rw [scalarCriticalDivisor_eq_wronskian hf F hlin he hD]
  change _ = ValueDistribution.logCounting (fun z => FewInflection.wronskian 1 F.coord z) 0
  rw [ValueDistribution.logCounting_zero, posPart_eq_self.mpr]
  exact (show AnalyticOnNhd ℂ (fun z => FewInflection.wronskian 1 F.coord z) univ from
    fun z _ => FewInflection.analyticAt_wronskian (fun j => (F.holomorphic j).analyticAt z)).divisor_nonneg

end ModifiedCartan
#print axioms ModifiedCartan.scalarCriticalDivisor_eq_wronskian
#print axioms ModifiedCartan.scalarRamification_eq_curve


