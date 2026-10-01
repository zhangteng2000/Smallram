import ModifiedCartan.ScalarFinitePeakTargets
import ModifiedCartan.ScalarSectorCover

open scoped Topology
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan

/-- Actual finite sector geometry, crosses and targets on one subsequence.
These fields are constructed below; the type does not assert across-scale
asymptotic values or the deficiency formula. -/
structure ScalarSectorSubsequenceData {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ}
    (d : ArbitraryRadiusLimitData f r ρ) where
  count : ℕ
  count_ge_two : 2 ≤ count
  order_eq : ρ = (count : ℝ) / 2
  center : ℂ
  center_norm : ‖center‖ = 1
  subseq : ℕ → ℕ
  strictMono : StrictMono subseq
  target : Fin count → WithTop ℂ
  selection : (j : Fin count) → ScalarHorizontalSelection f (fun ν => r (d.subseq (subseq ν)))
    (fun ν => characteristic f (r (d.subseq (subseq ν))))
    (scalarFullSector (scalarSectorCenter center count j) ρ)
  central_root : (((Real.pi / 2 : ℝ) : ℂ)) ^ 2 = d.scalarQuadratic center
  sector_root : ∀ j, (((Real.pi / 2 : ℝ) : ℂ)) ^ 2 =
    d.scalarQuadratic (scalarSectorCenter center count j)
  sector_open : ∀ j, IsOpen (scalarFullSector (scalarSectorCenter center count j) ρ)
  sector_connected : ∀ j, IsConnected (scalarFullSector (scalarSectorCenter center count j) ρ)
  sector_disjoint : ∀ i j, i ≠ j →
    Disjoint (scalarFullSector (scalarSectorCenter center count i) ρ)
      (scalarFullSector (scalarSectorCenter center count j) ρ)
  positive_cover : ∀ z : ℂ, (z ∈ ball (0 : ℂ) 2 ∧ 0 < (d.U z).toReal) ↔
    ∃ j, z ∈ scalarFullSector (scalarSectorCenter center count j) ρ
  crosses : ∀ j, HasSmallRectangleCrosses f (fun ν => r (d.subseq (subseq ν)))
    (fun ν => characteristic f (r (d.subseq (subseq ν))))
    (scalarFullSector (scalarSectorCenter center count j) ρ)
  anchor_limit : ∀ j (R : {R : ComplexRect // R.closed ⊆
      scalarFullSector (scalarSectorCenter center count j) ρ}),
    Tendsto ((selection j).anchor R) atTop (𝓝 (scalarSphereValue (target j)))

/-- Original curve hypotheses construct the entire finite sector subsequence
data, including exact positive-region coverage and actual physical targets.
Auxiliary to LaTeX thm:A (b), not the completed deficiency theorem. -/
theorem ArbitraryRadiusLimitData.scalar_exists_sector_subsequence_data
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} (d : ArbitraryRadiusLimitData f r ρ)
    (hlin : f.linearlyNonDegenerate) (htrans : f.Transcendental)
    (hsmall : SmallRamification f) (hρ : 1 ≤ ρ)
    (hl : strongLowerIndex (characteristic f) = (ρ : EReal))
    (hu : strongUpperIndex (characteristic f) = (ρ : EReal))
    (hr : Tendsto r atTop atTop) : Nonempty (ScalarSectorSubsequenceData d) := by
  obtain ⟨k, c, hc, hdegree, hcoeff⟩ := d.scalar_coefficient_monomial_nonzero hρ hr
  obtain ⟨a, ha1, _, hbase⟩ := d.scalar_exists_unit_peak_root hρ hr
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hm : k + 2 ≠ 0 := by omega
  have hdegree' : ρ = ((k + 2 : ℕ) : ℝ) / 2 := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hdegree
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (by rw [ha1]; norm_num)
  have hinj := scalarSectorCenter_injective ha0 hm
  have hn (j : Fin (k + 2)) : ‖scalarSectorCenter a (k + 2) j‖ = 1 := scalarSectorCenter_norm ha1 _ j
  have hne (j : Fin (k + 2)) : scalarSectorCenter a (k + 2) j ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [hn j]; norm_num)
  have hroot (j : Fin (k + 2)) :
      (((Real.pi / 2 : ℝ) : ℂ)) ^ 2 = d.scalarQuadratic (scalarSectorCenter a (k + 2) j) :=
    hbase.trans (d.scalar_quadratic_mul_root (a := a) hcoeff (scalarSectorRotation_pow hm j.val)).symm
  obtain ⟨ns, hns, β, q, ht⟩ := d.scalar_finite_peak_targets hlin htrans hsmall hρ hl hu hr
    (scalarSectorCenter a (k + 2)) hn hroot
  refine ⟨{
    count := k + 2
    count_ge_two := by omega
    order_eq := hdegree'
    center := a
    center_norm := ha1
    subseq := ns
    strictMono := hns
    target := β
    selection := q
    central_root := hbase
    sector_root := hroot
    sector_open := fun j => scalarFullSector_isOpen (hne j) hρpos
    sector_connected := fun j => scalarFullSector_isConnected (hne j) (by rw [hn j]; norm_num) hρpos
    sector_disjoint := fun i j hij => d.scalarFullSector_disjoint hρpos
      (Complex.ofReal_ne_zero.mpr (half_pos Real.pi_pos).ne') (hroot i) (hroot j) (fun he => hij (hinj he))
    positive_cover := ?_
    crosses := fun j => (ht j).1
    anchor_limit := fun j R => ((ht j).2 R).1
  }⟩
  intro z
  constructor
  · rintro ⟨hz, hp⟩
    exact d.scalar_positive_sector_cover hρ hc hcoeff hdegree' ha1 hbase hz hp
  · rintro ⟨j, hj⟩
    exact ⟨scalarFullSector_subset (hne j) hρpos hj,
      d.scalarFullSector_pos hρ (hne j) (half_pos Real.pi_pos) (hroot j) z hj⟩

theorem ScalarSectorSubsequenceData.horizontal_line_limit
    {f : Curve 1} {r : ℕ → ℝ} {ρ : ℝ} {d : ArbitraryRadiusLimitData f r ρ}
    (e : ScalarSectorSubsequenceData d) (hr : Tendsto r atTop atTop)
    (j : Fin e.count)
    (R : {R : ComplexRect // R.closed ⊆ scalarFullSector (scalarSectorCenter e.center e.count j) ρ}) :
    ∀ ε > 0, ∀ᶠ ν in atTop, ∀ t ∈ Icc R.val.left R.val.right,
      ‖scalarCurveSphere f ((r (d.subseq (e.subseq ν)) : ℂ) * (⟨t, (e.selection j).height R ν⟩ : ℂ)) -
        scalarSphereValue (e.target j)‖ < ε :=
  (e.selection j).horizontal_line_limit
    ((hr.comp d.strictMono.tendsto_atTop).comp e.strictMono.tendsto_atTop)
    (d.scale_tendsto.comp e.strictMono.tendsto_atTop) R (e.anchor_limit j R)

end ModifiedCartan
#print axioms ModifiedCartan.ArbitraryRadiusLimitData.scalar_exists_sector_subsequence_data
#print axioms ModifiedCartan.ScalarSectorSubsequenceData.horizontal_line_limit
