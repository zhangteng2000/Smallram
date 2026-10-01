import ModifiedCartan.LinearPicardSolution
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Normed.Group.Bounded

open scoped Topology
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- A continuous coefficient on a compact interval has actual solutions with
any prescribed initial value. Outside the interval it is extended by clipping. -/
theorem continuousOn_linearODE_solution_exists {B : ℝ → V →L[ℝ] V} {a b : ℝ}
    (hab : a ≤ b) (hB : ContinuousOn B (Icc a b)) (t0 : ℝ) (v : V) :
    ∃ X : ℝ → V, X t0 = v ∧ Continuous X ∧
      ∀ t ∈ Icc a b, HasDerivAt X (B t (X t)) t := by
  let p : ℝ → ℝ := fun t => max a (min b t)
  have hp : Continuous p := continuous_const.max (continuous_const.min continuous_id)
  have hpmem (t : ℝ) : p t ∈ Icc a b :=
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hpeq {t : ℝ} (ht : t ∈ Icc a b) : p t = t := by
    simp only [p, min_eq_right ht.2, max_eq_right ht.1]
  let C : ℝ → V →L[ℝ] V := fun t => B (p t)
  have hC : Continuous C := hB.comp_continuous hp hpmem
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hB
  have hbound (t : ℝ) : ‖C t‖ ≤ max M 0 := (hM (p t) (hpmem t)).trans (le_max_left M 0)
  obtain ⟨X, hX, hd⟩ := bounded_linearODE_solution_exists hC (le_max_right M 0) hbound t0 v
  refine ⟨X, hX, (show Differentiable ℝ X from fun t => (hd t).differentiableAt).continuous, ?_⟩
  intro t ht
  simpa only [C, hpeq ht] using hd t

theorem continuousOn_linearODE_lipschitz {B : ℝ → V →L[ℝ] V} {a b : ℝ}
    (hB : ContinuousOn B (Icc a b)) :
    ∃ K : NNReal, ∀ t ∈ Icc a b, LipschitzWith K (B t) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hB
  refine ⟨⟨max M 0, le_max_right M 0⟩, ?_⟩
  intro t ht
  apply ContinuousLinearMap.lipschitzWith_of_opNorm_le
  exact (hM t ht).trans (le_max_left M 0)

theorem continuousOn_linearODE_unique_right {B : ℝ → V →L[ℝ] V} {a b : ℝ}
    (hB : ContinuousOn B (Icc a b)) {f g : ℝ → V}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hdf : ∀ t ∈ Ico a b, HasDerivAt f (B t (f t)) t)
    (hdg : ∀ t ∈ Ico a b, HasDerivAt g (B t (g t)) t)
    (he : f a = g a) : EqOn f g (Icc a b) := by
  obtain ⟨K, hK⟩ := continuousOn_linearODE_lipschitz hB
  apply ODE_solution_unique_of_mem_Icc_right (v := fun t x => B t x) (s := fun _ => univ)
    (fun t ht => (hK t (Ico_subset_Icc_self ht)).lipschitzOnWith) hf
    (fun t ht => (hdf t ht).hasDerivWithinAt) (fun _ _ => mem_univ _) hg
    (fun t ht => (hdg t ht).hasDerivWithinAt) (fun _ _ => mem_univ _) he

theorem continuousOn_linearODE_unique_left {B : ℝ → V →L[ℝ] V} {a b : ℝ}
    (hB : ContinuousOn B (Icc a b)) {f g : ℝ → V}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hdf : ∀ t ∈ Ioc a b, HasDerivAt f (B t (f t)) t)
    (hdg : ∀ t ∈ Ioc a b, HasDerivAt g (B t (g t)) t)
    (he : f b = g b) : EqOn f g (Icc a b) := by
  obtain ⟨K, hK⟩ := continuousOn_linearODE_lipschitz hB
  apply ODE_solution_unique_of_mem_Icc_left (v := fun t x => B t x) (s := fun _ => univ)
    (fun t ht => (hK t (Ioc_subset_Icc_self ht)).lipschitzOnWith) hf
    (fun t ht => (hdf t ht).hasDerivWithinAt) (fun _ _ => mem_univ _) hg
    (fun t ht => (hdg t ht).hasDerivWithinAt) (fun _ _ => mem_univ _) he

end ModifiedCartan
#print axioms ModifiedCartan.continuousOn_linearODE_solution_exists
#print axioms ModifiedCartan.continuousOn_linearODE_unique_right
#print axioms ModifiedCartan.continuousOn_linearODE_unique_left

