import ModifiedCartan.DiagonalTail
import Mathlib.Topology.Instances.Matrix

open scoped Topology BoundedContinuousFunction
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem eventually_linearIndependent_of_exponential_normalization
    (lam : ι → ℂ) (X : ι → ℝ → ι → ℂ)
    (hX : ∀ j, Tendsto (fun t : ℝ => Complex.exp (-lam j * (t : ℂ)) • X j t)
      atTop (𝓝 (Pi.single j (1 : ℂ)))) :
    ∀ᶠ t : ℝ in atTop, LinearIndependent ℂ (fun j => X j t) := by
  let B : ℝ → Matrix ι ι ℂ := fun t j => Complex.exp (-lam j * (t : ℂ)) • X j t
  have hB : Tendsto B atTop (𝓝 (1 : Matrix ι ι ℂ)) := by
    apply tendsto_pi_nhds.mpr
    intro j
    have he : (Pi.single j (1 : ℂ)) = (1 : Matrix ι ι ℂ) j := by
      funext i
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    simpa only [B, he] using hX j
  have hdet : Tendsto (fun t => (B t).det) atTop (𝓝 (1 : ℂ)) := by
    simpa only [Function.comp_apply, id_eq, Matrix.det_one] using! (continuous_id.matrix_det.tendsto (1 : Matrix ι ι ℂ)).comp hB
  have hn := hdet.eventually (eventually_ne_nhds (one_ne_zero : (1 : ℂ) ≠ 0))
  filter_upwards [hn] with t ht
  have hli := Matrix.linearIndependent_rows_of_det_ne_zero ht
  let w : ι → ℂˣ := fun j => Units.mk0 (Complex.exp (lam j * (t : ℂ))) (Complex.exp_ne_zero _)
  have hw := hli.units_smul w
  have he : w • (fun j => B t j) = (fun j => X j t) := by
    funext j i
    change Complex.exp (lam j * (t : ℂ)) *
      (Complex.exp (-lam j * (t : ℂ)) * X j t i) = X j t i
    rw [← mul_assoc, ← Complex.exp_add,
      show lam j * (t : ℂ) + -lam j * (t : ℂ) = 0 by ring, Complex.exp_zero, one_mul]
  rw [he] at hw
  exact hw

theorem diagonal_tail_fundamental_system_exists (lam : ι → ℂ)
    {A : ℝ → (ι → ℂ) →L[ℂ] (ι → ℂ)} (hA : Continuous A) (t0 : ℝ)
    (hAi : IntegrableOn A (Ici t0)) :
    ∃ T : ℝ, t0 ≤ T ∧ ∃ X : ι → ℝ → ι → ℂ,
      (∀ j t, T ≤ t → HasDerivWithinAt (X j)
        (fun i => lam i * X j t i + A t (X j t) i) (Ici T) t) ∧
      (∀ t, T ≤ t → LinearIndependent ℂ (fun j => X j t)) ∧
      (∀ j, Tendsto (fun t : ℝ => Complex.exp (-lam j * (t : ℂ)) • X j t)
        atTop (𝓝 (Pi.single j (1 : ℂ)))) := by
  obtain ⟨T, hT, X, hd, hl⟩ := diagonal_tail_solutions_exists lam hA t0 hAi
  obtain ⟨S, hS⟩ := eventually_atTop.mp (eventually_linearIndependent_of_exponential_normalization lam X hl)
  refine ⟨max T S, hT.trans (le_max_left T S), X, ?_, ?_, hl⟩
  · intro j t ht
    exact (hd j t ((le_max_left T S).trans ht)).mono (Ici_subset_Ici.mpr (le_max_left T S))
  · intro t ht
    exact hS t ((le_max_right T S).trans ht)

end ModifiedCartan
#print axioms ModifiedCartan.eventually_linearIndependent_of_exponential_normalization
#print axioms ModifiedCartan.diagonal_tail_fundamental_system_exists


