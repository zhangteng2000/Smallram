import ModifiedCartan.UnitaryNorm
import ModifiedCartan.ExponentialJetApproximation

open scoped Topology BigOperators
open Filter Set Metric
set_option autoImplicit false
namespace ModifiedCartan
noncomputable section

def scaledJetLength (n : ℕ) (s : ℝ) (f : ℂ → ℂ) (a : ℂ) : ℝ :=
  euclideanNorm (fun i : Index n => ((s : ℂ)⁻¹) ^ i.val * iteratedDeriv i.val f a)

def jetCauchyConstant (n : ℕ) (r : ℝ) : ℝ :=
  Real.sqrt (n + 1) * ((∑ i : Index n, (i.val.factorial : ℝ) / r ^ i.val) + 1)

theorem jetCauchyConstant_pos (n : ℕ) {r : ℝ} (hr : 0 < r) : 0 < jetCauchyConstant n r := by
  unfold jetCauchyConstant
  positivity

theorem norm_scaled_jet_entry {s : ℝ} (hs : 0 < s) (f : ℂ → ℂ) (a : ℂ) (k : ℕ) :
    ‖((s : ℂ)⁻¹) ^ k * iteratedDeriv k f a‖ = ‖iteratedDeriv k f a‖ / s ^ k := by
  rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs.le,
    inv_pow, div_eq_mul_inv, mul_comm]

/-- Cauchy's estimate for the complete scaled initial jet, with a
constant independent of the scale and the holomorphic function. -/
theorem scaledJetLength_le_of_sphere_bound {n : ℕ} {s r M : ℝ} {f : ℂ → ℂ} {a : ℂ}
    (hs : 1 ≤ s) (hr : 0 < r) (hM0 : 0 ≤ M)
    (hf : DiffContOnCl ℂ f (ball a r)) (hM : ∀ z ∈ sphere a r, ‖f z‖ ≤ M) :
    scaledJetLength n s f a ≤ jetCauchyConstant n r * M := by
  have hspos : 0 < s := zero_lt_one.trans_le hs
  let B : ℝ := (∑ i : Index n, (i.val.factorial : ℝ) / r ^ i.val) + 1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hentry (i : Index n) :
      ‖((s : ℂ)⁻¹) ^ i.val * iteratedDeriv i.val f a‖ ≤ B * M := by
    have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le i.val hr hf hM
    have hcoef : (i.val.factorial : ℝ) / r ^ i.val ≤ B := by
      have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Index n)))
        (f := fun k => (k.val.factorial : ℝ) / r ^ k.val)
        (fun k _ => by positivity) (Finset.mem_univ i)
      dsimp only [B]
      linarith
    calc
      _ = ‖iteratedDeriv i.val f a‖ / s ^ i.val := norm_scaled_jet_entry hspos f a i.val
      _ ≤ ‖iteratedDeriv i.val f a‖ := div_le_self (norm_nonneg _) (one_le_pow₀ hs)
      _ ≤ (i.val.factorial : ℝ) * M / r ^ i.val := hc
      _ = ((i.val.factorial : ℝ) / r ^ i.val) * M := by ring
      _ ≤ B * M := mul_le_mul_of_nonneg_right hcoef hM0
  calc
    _ ≤ Real.sqrt (n + 1) * ‖(fun i : Index n => ((s : ℂ)⁻¹) ^ i.val * iteratedDeriv i.val f a)‖ :=
      euclideanNorm_le _
    _ ≤ Real.sqrt (n + 1) * (B * M) := mul_le_mul_of_nonneg_left
      ((pi_norm_le_iff_of_nonneg (mul_nonneg hB hM0)).mpr hentry) (Real.sqrt_nonneg _)
    _ = jetCauchyConstant n r * M := by dsimp only [jetCauchyConstant, B]; ring

theorem derivative_norm_le_scaledJetLength {n : ℕ} {s : ℝ} (hs : 0 < s)
    (f : ℂ → ℂ) (a : ℂ) (i : Index n) :
    ‖iteratedDeriv i.val f a‖ ≤ s ^ i.val * scaledJetLength n s f a := by
  have hh := (norm_le_pi_norm
    (fun k : Index n => ((s : ℂ)⁻¹) ^ k.val * iteratedDeriv k.val f a) i).trans
      (norm_le_euclideanNorm _)
  rw [norm_scaled_jet_entry hs] at hh
  simpa only [scaledJetLength, mul_comm] using (div_le_iff₀ (pow_pos hs i.val)).mp hh

end
end ModifiedCartan
#print axioms ModifiedCartan.scaledJetLength_le_of_sphere_bound
#print axioms ModifiedCartan.derivative_norm_le_scaledJetLength
