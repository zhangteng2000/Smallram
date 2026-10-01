import FewInflection.DerivativeMinors

/-!
# Limits of derivative minors

The determinant is continuous in a finite matrix.  Consequently convergence of
the finitely many derivative entries in a fixed minor implies convergence of
the minor itself.  This is the arbitrary-order analogue of the Wronskian
limit lemma.
-/

open scoped Topology
open Filter

namespace FewInflection

noncomputable section

theorem tendsto_derivativeMinor_of_tendsto_iteratedDeriv
    {ι : Type*} {p : Filter ι} {n : ℕ}
    {orders : Index n → ℕ}
    {F : ι → Index n → ℂ → ℂ} {G : Index n → ℂ → ℂ} {z : ℂ}
    (h : ∀ i j : Index n,
      Tendsto (fun ν => iteratedDeriv (orders i) (F ν j) z) p
        (𝓝 (iteratedDeriv (orders i) (G j) z))) :
    Tendsto (fun ν => derivativeMinor orders (F ν) z) p
      (𝓝 (derivativeMinor orders G z)) := by
  let M : Matrix (Index n) (Index n) ℂ :=
    fun i j => iteratedDeriv (orders i) (G j) z
  let Mν : ι → Matrix (Index n) (Index n) ℂ := fun ν i j =>
    iteratedDeriv (orders i) (F ν j) z
  have hM : Tendsto Mν p (𝓝 M) := by
    dsimp [M, Mν]
    exact (tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => h i j)
  have hdet : Tendsto (fun ν => (Mν ν).det) p (𝓝 M.det) := by
    exact (Continuous.matrix_det (continuous_id)).continuousAt.tendsto.comp hM
  simpa [M, Mν, derivativeMinor] using hdet

end

end FewInflection
