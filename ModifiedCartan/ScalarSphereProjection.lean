import ModifiedCartan.ScalarRamificationBridge
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue

open scoped Topology ComplexConjugate
open Filter Set
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

/-- Squared Euclidean length of a reduced pair; auxiliary to LaTeX `thm:A` (b). -/
def scalarPairEnergy (q p : ℂ) : ℝ := ‖q‖ ^ 2 + ‖p‖ ^ 2

theorem scalarPairEnergy_nonneg (q p : ℂ) : 0 ≤ scalarPairEnergy q p := by
  unfold scalarPairEnergy
  positivity

theorem scalarPairEnergy_pos {q p : ℂ} (h : q ≠ 0 ∨ p ≠ 0) :
    0 < scalarPairEnergy q p := by
  rcases h with h | h
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr h)) (sq_nonneg ‖p‖)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg ‖q‖) (sq_pos_of_pos (norm_pos_iff.mpr h))

theorem scalarPairEnergy_complex (q p : ℂ) :
    (scalarPairEnergy q p : ℂ) = q * conj q + p * conj p := by
  simp only [scalarPairEnergy, Complex.ofReal_add, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem scalarPairEnergy_complex_ne_zero {q p : ℂ} (h : q ≠ 0 ∨ p ≠ 0) :
    q * conj q + p * conj p ≠ 0 := by
  rw [← scalarPairEnergy_complex]
  exact Complex.ofReal_ne_zero.mpr (scalarPairEnergy_pos h).ne'

/-- Explicit projective coordinate in Complex x Complex, defined also at poles.
Used for spherical path control in LaTeX `thm:A` (b). -/
def scalarSphereProjection (q p : ℂ) : ℂ × ℂ :=
  (q * conj p / (q * conj q + p * conj p),
   q * conj q / (q * conj q + p * conj p))

theorem scalarSphereProjection_mul {c : ℂ} (hc : c ≠ 0) (q p : ℂ) :
    scalarSphereProjection (c * q) (c * p) = scalarSphereProjection q p := by
  have hc' : c * conj c ≠ 0 := mul_ne_zero hc ((map_ne_zero (starRingEnd ℂ)).mpr hc)
  have he : c * q * conj (c * q) + c * p * conj (c * p) =
      (c * conj c) * (q * conj q + p * conj p) := by
    simp only [map_mul]
    ring
  have hn (u v : ℂ) : c * u * conj (c * v) = (c * conj c) * (u * conj v) := by
    simp only [map_mul]
    ring
  unfold scalarSphereProjection
  rw [he, hn, hn, mul_div_mul_left _ _ hc', mul_div_mul_left _ _ hc']

def scalarSphereProjectionDerivative (q p W : ℂ) : ℂ × ℂ :=
  ((conj W * q ^ 2 - W * (conj p) ^ 2) / (q * conj q + p * conj p) ^ 2,
   -(W * conj p * conj q + conj W * p * q) / (q * conj q + p * conj p) ^ 2)

theorem scalarSphereProjection_hasDerivAt {q p : ℝ → ℂ} {q' p' : ℂ} {t : ℝ}
    (hq : HasDerivAt q q' t) (hp : HasDerivAt p p' t)
    (hne : q t ≠ 0 ∨ p t ≠ 0) :
    HasDerivAt (fun x => scalarSphereProjection (q x) (p x))
      (scalarSphereProjectionDerivative (q t) (p t) (q t * p' - p t * q')) t := by
  have hqc : HasDerivAt (fun x => conj (q x)) (conj q') t := hq.star
  have hpc : HasDerivAt (fun x => conj (p x)) (conj p') t := hp.star
  have hd := (hq.mul hqc).add (hp.mul hpc)
  have hn := scalarPairEnergy_complex_ne_zero hne
  have hh := ((hq.mul hpc).div hd hn).prodMk ((hq.mul hqc).div hd hn)
  convert hh using 1
  · rfl
  · apply Prod.ext <;> dsimp only [scalarSphereProjectionDerivative, Prod.fst, Prod.snd]
    all_goals
      simp only [map_sub, map_mul, Pi.mul_apply, Pi.add_apply]
      ring

theorem scalarSphereProjectionDerivative_norm_le (q p W : ℂ) :
    ‖scalarSphereProjectionDerivative q p W‖ ≤ ‖W‖ / scalarPairEnergy q p := by
  by_cases hn : q = 0 ∧ p = 0
  · rcases hn with ⟨rfl, rfl⟩
    simp [scalarSphereProjectionDerivative, scalarPairEnergy]
  have hne : q ≠ 0 ∨ p ≠ 0 := by tauto
  have hS := scalarPairEnergy_pos hne
  have hD : ‖q * conj q + p * conj p‖ = scalarPairEnergy q p := by
    rw [← scalarPairEnergy_complex, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hS]
  unfold scalarSphereProjectionDerivative
  rw [Prod.norm_mk, max_le_iff]
  constructor
  · rw [norm_div, norm_pow, hD]
    apply (div_le_iff₀ (sq_pos_of_pos hS)).mpr
    calc
      ‖conj W * q ^ 2 - W * conj p ^ 2‖ ≤ ‖W‖ * scalarPairEnergy q p := by
        calc
          _ ≤ ‖conj W * q ^ 2‖ + ‖W * conj p ^ 2‖ := norm_sub_le _ _
          _ = _ := by simp only [norm_mul, norm_pow, Complex.norm_conj, scalarPairEnergy, mul_add]
      _ = ‖W‖ / scalarPairEnergy q p * scalarPairEnergy q p ^ 2 := by
        field_simp
  · rw [norm_div, norm_neg, norm_pow, hD]
    apply (div_le_iff₀ (sq_pos_of_pos hS)).mpr
    calc
      ‖W * conj p * conj q + conj W * p * q‖ ≤
          ‖W‖ * ‖p‖ * ‖q‖ + ‖W‖ * ‖p‖ * ‖q‖ := by
        simpa only [norm_mul, Complex.norm_conj] using
          norm_add_le (W * conj p * conj q) (conj W * p * q)
      _ ≤ ‖W‖ * scalarPairEnergy q p := by
        have he : 2 * ‖p‖ * ‖q‖ ≤ scalarPairEnergy q p := by
          unfold scalarPairEnergy
          nlinarith [sq_nonneg (‖q‖ - ‖p‖)]
        nlinarith [mul_le_mul_of_nonneg_left he (norm_nonneg W)]
      _ = ‖W‖ / scalarPairEnergy q p * scalarPairEnergy q p ^ 2 := by
        field_simp

theorem scalarSphereProjection_path_bound {q p q' p' : ℝ → ℂ} {a b C : ℝ}
    (hab : a ≤ b)
    (hq : ∀ x ∈ Icc a b, HasDerivAt q (q' x) x)
    (hp : ∀ x ∈ Icc a b, HasDerivAt p (p' x) x)
    (hne : ∀ x ∈ Icc a b, q x ≠ 0 ∨ p x ≠ 0)
    (hbound : ∀ x ∈ Ico a b,
      ‖q x * p' x - p x * q' x‖ / scalarPairEnergy (q x) (p x) ≤ C) :
    ‖scalarSphereProjection (q b) (p b) - scalarSphereProjection (q a) (p a)‖
      ≤ C * (b - a) := by
  apply norm_image_sub_le_of_norm_deriv_le_segment'
    (fun x hx => (scalarSphereProjection_hasDerivAt (hq x hx) (hp x hx) (hne x hx)).hasDerivWithinAt)
    (fun x hx => (scalarSphereProjectionDerivative_norm_le _ _ _).trans (hbound x hx))
    b (right_mem_Icc.mpr hab)

end
end ModifiedCartan
#print axioms ModifiedCartan.scalarSphereProjection_path_bound



