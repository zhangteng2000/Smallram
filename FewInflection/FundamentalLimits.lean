import FewInflection.WronskianLimits

open scoped BigOperators Topology
open Filter

namespace FewInflection
noncomputable section

/-! Cramer's formula in a form suitable for taking limits. -/
theorem fundamentalCoefficients_eq_inv_smul_cramer
    {n : ℕ} {g : Index n → ℂ → ℂ} {z : ℂ}
    (hW : wronskian n g z ≠ 0) :
    fundamentalCoefficients n g z =
      (wronskian n g z)⁻¹ •
        Matrix.cramer
          (Matrix.transpose
            (fun (i j : Index n) => iteratedDeriv (i : ℕ) (g j) z))
          (fun j => -iteratedDeriv (n + 1) (g j) z) := by
  funext i
  have hcr := fundamentalCoefficients_cramer hW
  have hi := congrFun hcr i
  simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
  field_simp [hW]
  simpa [wronskian, mul_comm] using hi

/-! The Cramer map is continuous in both the jet matrix and its right-hand
side.  The proof expands each Cramer coordinate as a determinant of an
updated column, so it uses only Mathlib's finite-dimensional continuity API. -/
theorem tendsto_cramer_of_tendsto
    {ι : Type*} {p : Filter ι} {n : ℕ}
    {Mν : ι → Matrix (Fin n) (Fin n) ℂ}
    {M : Matrix (Fin n) (Fin n) ℂ}
    {bν : ι → Fin n → ℂ} {b : Fin n → ℂ}
    (hM : Tendsto Mν p (𝓝 M)) (hb : Tendsto bν p (𝓝 b)) :
    Tendsto (fun ν => Matrix.cramer (Mν ν) (bν ν)) p
      (𝓝 (Matrix.cramer M b)) := by
  apply tendsto_pi_nhds.2
  intro i
  simp only [Matrix.cramer_apply]
  have hprod : Tendsto (fun ν => (Mν ν, bν ν)) p (𝓝 (M, b)) := by
    simpa only [nhds_prod_eq] using hM.prodMk hb
  have hu : Continuous (fun q : Matrix (Fin n) (Fin n) ℂ × (Fin n → ℂ) =>
      q.1.updateCol i q.2) := by
    fun_prop
  have hd : Continuous (fun q : Matrix (Fin n) (Fin n) ℂ × (Fin n → ℂ) =>
      (q.1.updateCol i q.2).det) :=
    Continuous.matrix_det hu
  have ht := hd.continuousAt.tendsto.comp hprod
  simpa [Function.comp_def] using ht

/-! Fundamental coefficients are continuous at every nonzero Wronskian point
with respect to convergence of all finite derivative jets.  The eventual
nonzero condition is derived from the nonzero limiting Wronskian; it is not an
extra hypothesis hidden in the conclusion. -/
theorem tendsto_fundamentalCoefficients_of_tendsto_iteratedDeriv
    {ι : Type*} {p : Filter ι} {n : ℕ}
    {F : ι → Index n → ℂ → ℂ} {G : Index n → ℂ → ℂ} {z : ℂ}
    (hjet : ∀ k : ℕ, ∀ j : Index n,
      Tendsto (fun ν => iteratedDeriv k (F ν j) z) p
        (𝓝 (iteratedDeriv k (G j) z)))
    (hWzero : wronskian n G z ≠ 0) :
    Tendsto (fun ν => fundamentalCoefficients n (F ν) z) p
      (𝓝 (fundamentalCoefficients n G z)) := by
  let M : Matrix (Index n) (Index n) ℂ :=
    fun i j => iteratedDeriv (i : ℕ) (G j) z
  let Mν : ι → Matrix (Index n) (Index n) ℂ := fun ν i j =>
    iteratedDeriv (i : ℕ) (F ν j) z
  let rhs : Index n → ℂ := fun j => -iteratedDeriv (n + 1) (G j) z
  let rhsν : ι → Index n → ℂ := fun ν j => -iteratedDeriv (n + 1) (F ν j) z
  have hM : Tendsto Mν p (𝓝 M) := by
    dsimp [M, Mν]
    exact (tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j =>
      hjet (i : ℕ) j)
  have hWlim : Tendsto (fun ν => wronskian n (F ν) z) p
      (𝓝 (wronskian n G z)) :=
    tendsto_wronskian_of_tendsto_iteratedDeriv (fun i j => hjet (i : ℕ) j)
  have hWevent : ∀ᶠ ν in p, wronskian n (F ν) z ≠ 0 :=
    hWlim.eventually_ne hWzero
  have hMT0 : Tendsto
      (fun ν => Matrix.transpose
        (fun (i j : Index n) => iteratedDeriv (i : ℕ) (F ν j) z)) p
      (𝓝 (Matrix.transpose
        (fun (i j : Index n) => iteratedDeriv (i : ℕ) (G j) z))) := by
    exact (tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j =>
      hjet (j : ℕ) i)
  have hMT : Tendsto (fun ν => Matrix.transpose (Mν ν)) p
      (𝓝 (Matrix.transpose M)) := by
    simpa [M, Mν] using hMT0
  have hRhs : Tendsto rhsν p (𝓝 rhs) := by
    dsimp [rhsν, rhs]
    exact (tendsto_pi_nhds.2 fun j => (hjet (n + 1) j).neg)
  have hcr : Tendsto
      (fun ν => Matrix.cramer (Matrix.transpose (Mν ν)) (rhsν ν)) p
      (𝓝 (Matrix.cramer (Matrix.transpose M) rhs)) :=
    tendsto_cramer_of_tendsto hMT hRhs
  have hWinv : Tendsto (fun ν => (wronskian n (F ν) z)⁻¹) p
      (𝓝 (wronskian n G z)⁻¹) := hWlim.inv₀ hWzero
  have hcoef : Tendsto
      (fun ν => (wronskian n (F ν) z)⁻¹ •
        Matrix.cramer (Matrix.transpose (Mν ν)) (rhsν ν)) p
      (𝓝 ((wronskian n G z)⁻¹ • Matrix.cramer (Matrix.transpose M) rhs)) :=
    hWinv.smul hcr
  have heq : (wronskian n G z)⁻¹ • Matrix.cramer (Matrix.transpose M) rhs =
      fundamentalCoefficients n G z := by
    symm
    exact fundamentalCoefficients_eq_inv_smul_cramer hWzero
  rw [heq] at hcoef
  apply hcoef.congr'
  filter_upwards [hWevent] with ν hν
  symm
  simpa [Mν, rhsν, wronskian] using
    (fundamentalCoefficients_eq_inv_smul_cramer
      (g := F ν) (z := z) hν)

theorem tendsto_fundamentalCoefficients_of_locallyUniformlyOn
    {ι : Type*} {p : Filter ι} {n : ℕ}
    {F : ι → Index n → ℂ → ℂ} {G : Index n → ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U)
    (hF : ∀ j : Index n,
      TendstoLocallyUniformlyOn (fun ν => F ν j) (G j) p U)
    (hholF : ∀ᶠ ν in p, ∀ j : Index n, Differentiable ℂ (F ν j))
    (hWzero : wronskian n G z ≠ 0) :
    Tendsto (fun ν => fundamentalCoefficients n (F ν) z) p
      (𝓝 (fundamentalCoefficients n G z)) := by
  apply tendsto_fundamentalCoefficients_of_tendsto_iteratedDeriv (hjet := ?_) hWzero
  intro k j
  exact tendsto_iteratedDeriv_of_locallyUniformlyOn_at hU hz (hF j)
    (hholF.mono fun ν hν => hν j) k

end
end FewInflection
