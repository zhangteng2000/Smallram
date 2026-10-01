import ModifiedCartan.EuclideanDiagonalTail
import ModifiedCartan.LinearODEExtension
import ModifiedCartan.LinearODEIndependent

open scoped Topology
open Filter Set MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- LaTeX `lem:integrable-system`. The full fundamental system, including
extension to the original starting time, with the exact Euclidean operator norm
and exponential normalizations from the manuscript. -/
theorem Paper.lem_integrable_system {q : ℕ} (hq : 1 ≤ q)
    (lam : Fin q → ℂ) (hlam : Function.Injective (fun j => (lam j).re))
    (E : ℝ → Matrix (Fin q) (Fin q) ℂ) (t0 : ℝ)
    (hE : ContinuousOn (fun t => Matrix.toEuclideanCLM (n := Fin q) (𝕜 := ℂ) (E t)) (Ici t0))
    (hEi : IntegrableOn (fun t => Matrix.toEuclideanCLM (n := Fin q) (𝕜 := ℂ) (E t)) (Ici t0)) :
    ∃ X : Fin q → ℝ → EuclideanSpace ℂ (Fin q),
      (∀ j t, t0 ≤ t → HasDerivWithinAt (X j)
        (Matrix.toEuclideanCLM (n := Fin q) (𝕜 := ℂ) (Matrix.diagonal lam + E t) (X j t)) (Ici t0) t) ∧
      (∀ t, t0 ≤ t → LinearIndependent ℂ (fun j => X j t)) ∧
      (∀ j, Tendsto (fun t : ℝ => Complex.exp (-lam j * (t : ℂ)) • X j t)
        atTop (𝓝 (WithLp.toLp 2 (Pi.single j (1 : ℂ))))) := by
  let B : ℝ → EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q) :=
    fun t => Matrix.toEuclideanCLM (n := Fin q) (𝕜 := ℂ) (Matrix.diagonal lam + E t)
  have hB : ContinuousOn B (Ici t0) := by
    have hc : ContinuousOn (fun t =>
        Matrix.toEuclideanCLM (n := Fin q) (𝕜 := ℂ) (Matrix.diagonal lam) +
        Matrix.toEuclideanCLM (n := Fin q) (𝕜 := ℂ) (E t)) (Ici t0) := continuousOn_const.add hE
    apply hc.congr
    intro t _
    exact map_add (Matrix.toEuclideanCLM (n := Fin q) (𝕜 := ℂ)) (Matrix.diagonal lam) (E t)
  let BR : ℝ → EuclideanSpace ℂ (Fin q) →L[ℝ] EuclideanSpace ℂ (Fin q) :=
    fun t => (B t).restrictScalars ℝ
  have hBR : ContinuousOn BR (Ici t0) :=
    (ContinuousLinearMap.continuous_restrictScalars ℝ).comp_continuousOn hB
  obtain ⟨T, hT, X, hd, hli, hl⟩ := euclidean_diagonal_tail_fundamental_system_exists lam E t0 hE hEi
  have hext (j : Fin q) := linearODE_extend_from_tail hT hBR (f := X j)
    (fun t ht => hd j t ht)
  choose Y hYd hYeq using hext
  have hYli : LinearIndependent ℂ (fun j => Y j (T + 1)) := by
    have he : (fun j => Y j (T + 1)) = (fun j => X j (T + 1)) :=
      funext (fun j => hYeq j (T + 1) le_rfl)
    rw [he]
    exact hli (T + 1) (by linarith)
  have hYall := linearODE_family_independent_of_one_time hB (show t0 ≤ T + 1 by linarith)
    Y hYd hYli
  refine ⟨Y, (fun j t ht => (hYd j t ht).hasDerivWithinAt), hYall, ?_⟩
  intro j
  apply (hl j).congr'
  filter_upwards [eventually_ge_atTop (T + 1)] with t ht
  rw [hYeq j t ht]

end ModifiedCartan
#print axioms ModifiedCartan.Paper.lem_integrable_system
