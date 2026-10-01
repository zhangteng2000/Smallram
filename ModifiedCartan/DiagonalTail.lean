import ModifiedCartan.DichotomyFixedPoint
import Mathlib.Analysis.Calculus.Deriv.Mul

open scoped Topology BoundedContinuousFunction
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem diagonal_exponential_hasDerivWithinAt (lam : ι → ℂ) (μ : ℂ)
    (A : (ι → ℂ) →L[ℂ] (ι → ℂ)) (v : ι → ℂ) {u : ℝ → ι → ℂ}
    {S : Set ℝ} {t : ℝ} (hv : ∀ i, (lam i - μ) * v i = 0)
    (hu : HasDerivWithinAt u
      (fun i => (lam i - μ) * u t i + A (v + u t) i) S t) :
    HasDerivWithinAt (fun s : ℝ => Complex.exp (μ * (s : ℂ)) • (v + u s))
      (fun i => lam i * (Complex.exp (μ * (t : ℂ)) • (v + u t)) i +
        A (Complex.exp (μ * (t : ℂ)) • (v + u t)) i) S t := by
  have he : HasDerivAt (fun s : ℝ => Complex.exp (μ * (s : ℂ)))
      (Complex.exp (μ * (t : ℂ)) * μ) t := by
    simpa only [mul_one, id_eq] using! (((hasDerivAt_id (t : ℂ)).const_mul μ).cexp).comp_ofReal
  apply hasDerivWithinAt_pi.mpr
  intro i
  have hd := he.hasDerivWithinAt.mul ((hasDerivWithinAt_pi.mp hu i).const_add (v i))
  have hd' : HasDerivWithinAt
      (fun s : ℝ => Complex.exp (μ * (s : ℂ)) * (v i + u s i))
      (lam i * (Complex.exp (μ * (t : ℂ)) * (v i + u t i)) +
        Complex.exp (μ * (t : ℂ)) * A (v + u t) i) S t := by
    apply hd.congr_deriv
    linear_combination -Complex.exp (μ * (t : ℂ)) * hv i
  simpa only [map_smul, Pi.smul_apply, Pi.add_apply, smul_eq_mul] using! hd'

theorem diagonal_exponential_normalization (μ : ℂ) (v : ι → ℂ)
    (u : ℝ → ι → ℂ) (t : ℝ) :
    Complex.exp (-μ * (t : ℂ)) • (Complex.exp (μ * (t : ℂ)) • (v + u t)) = v + u t := by
  rw [smul_smul, ← Complex.exp_add,
    show -μ * (t : ℂ) + μ * (t : ℂ) = 0 by ring, Complex.exp_zero, one_smul]

/-- The small-norm tail is obtained from actual integrability. No asymptotic
solution or spectral separation is required as an extra assumption. -/
theorem diagonal_tail_solutions_exists (lam : ι → ℂ)
    {A : ℝ → (ι → ℂ) →L[ℂ] (ι → ℂ)} (hA : Continuous A) (t0 : ℝ)
    (hAi : IntegrableOn A (Ici t0)) :
    ∃ T : ℝ, t0 ≤ T ∧ ∃ X : ι → ℝ → ι → ℂ,
      (∀ j t, T ≤ t → HasDerivWithinAt (X j)
        (fun i => lam i * X j t i + A t (X j t) i) (Ici T) t) ∧
      (∀ j, Tendsto (fun t : ℝ => Complex.exp (-lam j * (t : ℂ)) • X j t)
        atTop (𝓝 (Pi.single j (1 : ℂ)))) := by
  have htail : Tendsto (fun T : ℝ => ∫ s in Ici T, ‖A s‖) atTop (𝓝 0) :=
    tendsto_integral_Ici_zero tendsto_id
  have hs : ∀ᶠ T : ℝ in atTop, (∫ s in Ici T, ‖A s‖) < 1 :=
    htail.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨T, hT0, hT⟩ := ((eventually_ge_atTop t0).and hs).exists
  have hAT : IntegrableOn A (Ici T) := hAi.mono_set (Ici_subset_Ici.mpr hT0)
  have hex (j : ι) := dichotomy_tail_solution_exists (fun i => lam i - lam j)
    hA hAT (Pi.single j (1 : ℂ)) hT
  choose u hu hlim using hex
  let X : ι → ℝ → ι → ℂ := fun j t =>
    Complex.exp (lam j * (t : ℂ)) • (Pi.single j (1 : ℂ) + u j t)
  refine ⟨T, hT0, X, ?_, ?_⟩
  · intro j t ht
    apply diagonal_exponential_hasDerivWithinAt lam (lam j) (A t) (Pi.single j (1 : ℂ))
      (u := fun s => u j s) _ (hu j t ht)
    intro i
    by_cases hi : i = j
    · subst i
      simp
    · simp [Pi.single_eq_of_ne hi]
  · intro j
    have he : (fun t : ℝ => Complex.exp (-lam j * (t : ℂ)) • X j t) =
        (fun t => Pi.single j (1 : ℂ) + u j t) := by
      funext t
      exact diagonal_exponential_normalization (lam j) (Pi.single j (1 : ℂ)) (fun s => u j s) t
    rw [he]
    simpa only [add_zero] using tendsto_const_nhds.add (hlim j)

end ModifiedCartan
#print axioms ModifiedCartan.diagonal_tail_solutions_exists



