import ModifiedCartan.UnitaryComponentGradient
import ModifiedCartan.BasisAtPoint
import ModifiedCartan.FiniteLogMax
import Mathlib.Topology.Order.Lattice

open scoped Topology BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

theorem ArbitraryRadiusLimitData.unitary_component_regular {n : ℕ} {f : Curve n}
    {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    {ns : ℕ → ℕ} (hns : StrictMono ns) (V : ℕ → Matrix.unitaryGroup (Index n) ℂ)
    (j : Index n) {u : ℂ → EReal} {v : ℂ → ℝ}
    (hu : IsSubharmonicOn (ball (0 : ℂ) 4) u)
    (hrep : u =ᵐ[volume.restrict (ball (0 : ℂ) 4)] (fun z => (v z : EReal)))
    (hlim : LocalERealLpConvergence 1 (ball (0 : ℂ) 4)
      (fun ν => normalizedExtendedLog (characteristic f (r (d.subseq (ns ν))))
        (fun z => (polynomialMatrixGauge (d.polynomial (ns ν))
          (V ν : Matrix (Index n) (Index n) ℂ) j).eval z)) v) :
    (∀ z ∈ ball (0 : ℂ) 4, u z = ((u z).toReal : EReal)) ∧
      LocallyLipschitzOn (ball (0 : ℂ) 4) (fun z => (u z).toReal) := by
  obtain ⟨g, hg, he⟩ := d.unitary_component_gradient_equation hns V j hlim
  exact hu.locallyLipschitzOn_of_gradient_equation isOpen_ball hrep hg
    (fun i => (d.fullCoefficient_analytic i).continuousOn.mono (subset_univ _)) he

/-- Step 1 of `prop:homogeneity`: continuity is proved for the already fixed
norm limit, using an actual regular unitary basis at a good center. -/
theorem ArbitraryRadiusLimitData.norm_limit_continuous {n : ℕ} {f : Curve n}
    {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ) :
    (∀ z ∈ ball (0 : ℂ) 4, d.U z = ((d.U z).toReal : EReal)) ∧
      ContinuousOn (fun z => (d.U z).toReal) (ball (0 : ℂ) 4) := by
  obtain ⟨a, _, ha⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (isOpen_ball.measure_ne_zero volume (nonempty_ball.mpr (by norm_num : (0 : ℝ) < 2))) d.good_centers.full_measure
  obtain ⟨ns, hns, V, u, v, hu, hmax, _, _⟩ := Paper.lem_basis_at_point d a ha
  have hreg (j : Index n) := d.unitary_component_regular hns V j
    (hu j).1 (hu j).2.2.1 (hu j).2.2.2
  let M : ℂ → ℝ := fun z => Finset.univ.sup' Finset.univ_nonempty (fun j => (u j z).toReal)
  have hMc : ContinuousOn M (ball (0 : ℂ) 4) :=
    ContinuousOn.finset_sup'_apply Finset.univ_nonempty (fun j _ => (hreg j).2.continuousOn)
  have he (z : ℂ) (hz : z ∈ ball (0 : ℂ) 4) : d.U z = (M z : EReal) := by
    rw [hmax hz]
    change Finset.univ.sup (fun j => u j z) = ((Finset.univ.sup' Finset.univ_nonempty (fun j => (u j z).toReal) : ℝ) : EReal)
    rw [ereal_coe_finset_sup']
    exact Finset.sup_congr rfl (fun j _ => (hreg j).1 z hz)
  have her : EqOn (fun z => (d.U z).toReal) M (ball (0 : ℂ) 4) := by
    intro z hz
    change (d.U z).toReal = M z
    rw [he z hz, EReal.toReal_coe]
  refine ⟨?_, hMc.congr her⟩
  intro z hz
  rw [he z hz, EReal.toReal_coe]

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.unitary_component_regular
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.norm_limit_continuous
