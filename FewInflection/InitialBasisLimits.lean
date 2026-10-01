import FewInflection.InitialBasis

/-!
# Limits of initial-value bases

At a point with nonzero limiting Wronskian, inversion of the finite jet matrix
is continuous.  Together with convergence of the function values at a second
point, this gives convergence of the corresponding initial-basis value.  The
statement is finite-dimensional and keeps all nonvanishing hypotheses
explicit.
-/

open scoped BigOperators Topology
open Filter

namespace FewInflection

noncomputable section

theorem tendsto_initialBasis_of_tendsto_iteratedDeriv
    {ι : Type*} {p : Filter ι} {n : ℕ}
    {F : ι → Index n → ℂ → ℂ} {G : Index n → ℂ → ℂ}
    {a x : ℂ} (hjet : ∀ i j : Index n,
      Tendsto (fun ν => iteratedDeriv (i : ℕ) (F ν j) a) p
        (𝓝 (iteratedDeriv (i : ℕ) (G j) a)))
    (hvalue : ∀ j : Index n,
      Tendsto (fun ν => F ν j x) p (𝓝 (G j x)))
    (hW : wronskian n G a ≠ 0) (j : Index n) :
    Tendsto (fun ν => initialBasis (F ν) a j x) p
      (𝓝 (initialBasis G a j x)) := by
  let M : Matrix (Index n) (Index n) ℂ := jetMatrix G a
  let Mν : ι → Matrix (Index n) (Index n) ℂ :=
    fun ν => jetMatrix (F ν) a
  have hM : Tendsto Mν p (𝓝 M) := by
    dsimp [M, Mν, jetMatrix]
    exact tendsto_pi_nhds.2 (fun i => tendsto_pi_nhds.2 (fun k => hjet i k))
  have hMdet : M.det ≠ 0 := by
    dsimp [M]
    rw [jetMatrix_det_eq_wronskian]
    exact hW
  have hinv : Tendsto (fun ν => (Mν ν)⁻¹) p (𝓝 (M⁻¹)) := by
    have hinvdet : ContinuousAt Ring.inverse M.det := by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hMdet
    exact (continuousAt_matrix_inv M hinvdet).tendsto.comp hM
  have hcoeff : ∀ k : Index n,
      Tendsto (fun ν => (Mν ν)⁻¹ k j) p (𝓝 (M⁻¹ k j)) := by
    intro k
    exact (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hinv k)) j
  have hsum : Tendsto
      (fun ν => ∑ k : Index n, (Mν ν)⁻¹ k j * F ν k x) p
      (𝓝 (∑ k : Index n, M⁻¹ k j * G k x)) := by
    simpa only [Finset.sum_apply] using
      (tendsto_finsetSum (x := p) (s := (Finset.univ : Finset (Index n)))
        (fun k hk => (hcoeff k).mul (hvalue k)))
  simpa [initialBasis, initialBasisCoeff, M, Mν, jetMatrix] using hsum

end

end FewInflection
