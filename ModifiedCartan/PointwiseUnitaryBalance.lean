import ModifiedCartan.UnitaryComponentRegularity
import Mathlib.MeasureTheory.Measure.OpenPos

open scoped Topology BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem continuousOn_nonneg_of_ae_nonneg {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℝ} (hf : ContinuousOn f U)
    (hpos : ∀ᵐ z ∂volume.restrict U, 0 ≤ f z) : ∀ z ∈ U, 0 ≤ f z := by
  have hmax : (fun z => max 0 (f z)) =ᵐ[volume.restrict U] f :=
    hpos.mono (fun _ hz => max_eq_right hz)
  have he := Measure.eqOn_open_of_ae_eq hmax hU (continuousOn_const.sup hf) hf
  intro z hz
  rw [← he hz]
  exact le_max_left _ _

theorem ArbitraryRadiusLimitData.unitary_component_real_gradient {n : ℕ} {f : Curve n}
    {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    {ns : ℕ → ℕ} (hns : StrictMono ns) (V : ℕ → Matrix.unitaryGroup (Index n) ℂ)
    (j : Index n) {u : ℂ → EReal} {v : ℂ → ℝ}
    (hrep : u =ᵐ[volume.restrict (ball (0 : ℂ) 4)] (fun z => (v z : EReal)))
    (hlim : LocalERealLpConvergence 1 (ball (0 : ℂ) 4)
      (fun ν => normalizedExtendedLog (characteristic f (r (d.subseq (ns ν))))
        (fun z => (polynomialMatrixGauge (d.polynomial (ns ν))
          (V ν : Matrix (Index n) (Index n) ℂ) j).eval z)) v) :
    ∃ g : ℂ → ℂ, HasWeakComplexGradient (ball (0 : ℂ) 4) (fun z => (u z).toReal) g ∧
      ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 4),
        g z ^ (n + 1) + ∑ i : Index n, d.fullCoefficient i z * g z ^ i.val = 0 := by
  obtain ⟨g, hg, he⟩ := d.unitary_component_gradient_equation hns V j hlim
  refine ⟨g, hg.congr_function_ae isOpen_ball ?_, he⟩
  filter_upwards [hrep] with z hz
  change v z = (u z).toReal
  rw [hz, EReal.toReal_coe]

/-- The AE inequality in `eq:point-balance` holds everywhere after the
regularity of the actual components has been proved. -/
theorem ArbitraryRadiusLimitData.unitary_component_sum_nonneg {n : ℕ} {f : Curve n}
    {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    {ns : ℕ → ℕ} (hns : StrictMono ns) (V : ℕ → Matrix.unitaryGroup (Index n) ℂ)
    {u : Index n → ℂ → EReal} {v : Index n → ℂ → ℝ}
    (hu : ∀ j, IsSubharmonicOn (ball (0 : ℂ) 4) (u j))
    (hrep : ∀ j, u j =ᵐ[volume.restrict (ball (0 : ℂ) 4)] (fun z => (v j z : EReal)))
    (hlim : ∀ j, LocalERealLpConvergence 1 (ball (0 : ℂ) 4)
      (fun ν => normalizedExtendedLog (characteristic f (r (d.subseq (ns ν))))
        (fun z => (polynomialMatrixGauge (d.polynomial (ns ν))
          (V ν : Matrix (Index n) (Index n) ℂ) j).eval z)) (v j))
    (hsum : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 4), 0 ≤ ∑ j, u j z) :
    ∀ z ∈ ball (0 : ℂ) 4, 0 ≤ ∑ j, (u j z).toReal := by
  have hreg (j : Index n) := d.unitary_component_regular hns V j (hu j) (hrep j) (hlim j)
  apply continuousOn_nonneg_of_ae_nonneg isOpen_ball
    (continuousOn_finsetSum Finset.univ (fun j _ => (hreg j).2.continuousOn))
  filter_upwards [hsum, ae_restrict_mem measurableSet_ball] with z hz hzball
  have he : (∑ j, u j z) = ((∑ j, (u j z).toReal : ℝ) : EReal) := by
    rw [ereal_coe_finset_sum]
    exact Finset.sum_congr rfl (fun j _ => (hreg j).1 z hzball)
  rw [he] at hz
  exact_mod_cast hz

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.unitary_component_real_gradient
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.unitary_component_sum_nonneg
