import ModifiedCartan.ArbitraryCoefficients
import ModifiedCartan.ReplacementLogLimits
import ModifiedCartan.GoodCenters
import ModifiedCartan.OriginBound

open scoped Topology ENNReal BigOperators
open Filter Set Metric MeasureTheory
set_option autoImplicit false
namespace ModifiedCartan

/-- Literal good-center data in LaTeX `eq:good-centers`. The root list
contains every root of the actual polynomial Wronskian, with multiplicity. -/
structure GoodCenterData {n : ℕ} (s : ℕ → ℝ) (p : ℕ → Index n → Polynomial ℂ)
    (a : (ν : ℕ) → Fin (FewInflection.polynomialWronskian (p ν)).natDegree → ℂ) where
  centers : Set ℂ
  subset : centers ⊆ ball (0 : ℂ) 2 \ {0}
  full_measure : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 2), z ∈ centers
  wronskian_ne_zero : ∀ z ∈ centers, ∀ ν,
    (FewInflection.polynomialWronskian (p ν)).eval z ≠ 0
  log_wronskian : ∀ z ∈ centers,
    Tendsto (fun ν => Real.log ‖(FewInflection.polynomialWronskian (p ν)).eval z‖ / s ν)
      atTop (𝓝 0)
  root_sum_bound : ∀ z ∈ centers, ∃ B : ℝ, 0 < B ∧ ∀ᶠ ν in atTop,
    reciprocalDistanceSum Finset.univ (a ν) z / s ν ≤ B

/-- The literal finite-limsup assertion in `eq:good-centers`. -/
theorem GoodCenterData.limsup_lt_top {n : ℕ} {s : ℕ → ℝ}
    {p : ℕ → Index n → Polynomial ℂ}
    {a : (ν : ℕ) → Fin (FewInflection.polynomialWronskian (p ν)).natDegree → ℂ}
    (h : GoodCenterData s p a) {z : ℂ} (hz : z ∈ h.centers) :
    Filter.limsup (fun ν => ((reciprocalDistanceSum Finset.univ (a ν) z / s ν : ℝ) : EReal))
      atTop < ⊤ := by
  obtain ⟨B, _, hb⟩ := h.root_sum_bound z hz
  have hh : Filter.limsup
      (fun ν => ((reciprocalDistanceSum Finset.univ (a ν) z / s ν : ℝ) : EReal)) atTop ≤ (B : EReal) := by
    apply Filter.limsup_le_of_le (by isBoundedDefault)
    filter_upwards [hb] with ν hν
    exact_mod_cast hν
  exact hh.trans_lt (EReal.coe_lt_top B)

/-- All objects of LaTeX `sec:arbitrary-limits` on one common subsequence.
The construction theorem, rather than this data type, supplies existence. -/
structure ArbitraryRadiusLimitData {n : ℕ} (f : Curve n) (r : ℕ → ℝ) (ρ : ℝ) where
  subseq : ℕ → ℕ
  strictMono : StrictMono subseq
  scale_pos : ∀ ν, 0 < characteristic f (r (subseq ν))
  scale_tendsto : Tendsto (fun ν => characteristic f (r (subseq ν))) atTop atTop
  C : ℝ
  A : ℝ
  L : ℝ
  C_pos : 0 < C
  A_pos : 0 < A
  L_pos : 0 < L
  gauge : ℕ → ℂ → ℂ
  polynomial : ℕ → Index n → Polynomial ℂ
  roots : (ν : ℕ) → Fin (FewInflection.polynomialWronskian (polynomial ν)).natDegree → ℂ
  separatingRadius : ℕ → ℝ
  replacement : PolynomialReplacementData f (fun ν => r (subseq ν))
    (fun ν => characteristic f (r (subseq ν))) C A L gauge polynomial roots separatingRadius
  coefficient : Fin n → ℂ → ℂ
  coefficient_analytic : ∀ i, AnalyticOnNhd ℂ (coefficient i) univ
  coefficient_limit : ∀ i, LocalMeasureConvergence univ
    (fun ν z => ((r (subseq ν) / characteristic f (r (subseq ν)) : ℝ) : ℂ) ^ (n + 1 - i.val) *
      canonicalCoefficient n f.coord i.castSucc ((r (subseq ν) : ℂ) * z)) (coefficient i)
  coefficient_monomial : ∀ i, IsWeightedMonomial ((n + 1 - i.val : ℕ) * (ρ - 1)) (coefficient i)
  coefficient_bound : ∀ ε : ℝ, 0 < ε → ε < ρ → ∃ K : ℝ, 0 < K ∧
    ∀ R : ℝ, 0 < R → ∀ i : Fin n, ∀ z ∈ closedBall (0 : ℂ) R,
      ‖coefficient i z‖ ≤ K * max (R ^ ((n + 1 - i.val : ℕ) * (ρ - 1 - ε)))
        (R ^ ((n + 1 - i.val : ℕ) * (ρ - 1 + ε)))
  u : Index n → ℂ → EReal
  v : Index n → ℂ → ℝ
  coordinate_subharmonic : ∀ j, IsSubharmonicOn (ball (0 : ℂ) 4) (u j)
  coordinate_nontrivial : ∀ j, ∃ z ∈ ball (0 : ℂ) 4, u j z ≠ ⊥
  coordinate_representative : ∀ j,
    u j =ᵐ[volume.restrict (ball (0 : ℂ) 4)] (fun z => (v j z : EReal))
  coordinate_limit : ∀ j, LocalERealLpConvergence 1 (ball (0 : ℂ) 4)
    (fun ν => normalizedExtendedLog (characteristic f (r (subseq ν)))
      (rescaledRepresentation f (r (subseq ν)) (gauge ν) j)) (v j)
  coordinate_sum_nonneg : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 4), 0 ≤ ∑ j, v j z
  U : ℂ → EReal
  V : ℂ → ℝ
  maximum : ∀ z, U z = Finset.univ.sup (fun j => u j z)
  real_maximum : ∀ z, V z = Finset.univ.sup' Finset.univ_nonempty (fun j => v j z)
  subharmonic : IsSubharmonicOn (ball (0 : ℂ) 4) U
  representative : U =ᵐ[volume.restrict (ball (0 : ℂ) 4)] (fun z => (V z : EReal))
  nonneg : ∀ z ∈ ball (0 : ℂ) 4, 0 ≤ U z
  norm_limit : LocalLpConvergence 1 (ball (0 : ℂ) 4)
    (fun ν z => (characteristic f (r (subseq ν)))⁻¹ * Real.log (euclideanNorm
      (fun j => rescaledRepresentation f (r (subseq ν)) (gauge ν) j z))) V
  polynomial_norm_limit : LocalLpConvergence 1 (ball (0 : ℂ) 4)
    (fun ν z => (characteristic f (r (subseq ν)))⁻¹ *
      Real.log (euclideanNorm (fun j => (polynomial ν j).eval z))) V
  mean_error : ℕ → ℝ
  mean_error_zero : Tendsto mean_error atTop (𝓝 0)
  radial_mean : ∀ᶠ ν in atTop, ∀ R : ℝ, 0 < R → R < 64 →
    Real.circleAverage (fun z => (characteristic f (r (subseq ν)))⁻¹ * Real.log (euclideanNorm
      (fun j => rescaledRepresentation f (r (subseq ν)) (gauge ν) j z))) 0 R =
        characteristic f (R * r (subseq ν)) / characteristic f (r (subseq ν)) + mean_error ν
  origin_zero : U 0 = 0
  origin_bound : ∀ ε : ℝ, 0 < ε → ε < ρ → ∃ C : ℝ, 0 < C ∧
    ∀ z ∈ ball (0 : ℂ) (1 / 4), 0 ≤ U z ∧ U z ≤ ((C * ‖z‖ ^ (ρ - ε) : ℝ) : EReal)
  good_centers : GoodCenterData (fun ν => characteristic f (r (subseq ν))) polynomial roots

end ModifiedCartan
#print axioms ModifiedCartan.GoodCenterData.limsup_lt_top
