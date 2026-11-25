import QuantumNLS.TerraMultiRound49TaylorPath

/-! A uniform integrable majorant for the normalized positive-degree
correlation Taylor remainder along finite paths. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Asymptotics
namespace QuantumNLS.TerraMultiRound49TaylorBound
open QuantumNLS.TranslatedCorrelation QuantumNLS.Sobolev QuantumNLS.CorrelationTaylor
open QuantumNLS.TerraMultiRound48Leading QuantumNLS.TerraMultiRound49TaylorPath

variable {L : ℝ} [Fact (0 < L)]

def remainder {n m k : ℕ} (f : Fin (m + 2) → Hk L k) (d : ℕ)
    (paths : Fin (m + 2) → Finset (Fin n)) (z : ℝ) (t : Fin n → ℝ) : ℂ :=
  (z ^ (d + 1))⁻¹ • (Cfun f (scaledShift paths z t) -
    taylorPoly (Cfun f) (d + 1) (scaledShift paths z t))

def majorantConstant {m k : ℕ} (f : Fin (m + 2) → Hk L k) (d : ℕ) : ℝ :=
  (2 * (((m + 2 : ℕ) : ℝ) ^ (2 * k) * Bfull f)) * ((m + 2 : ℕ) : ℝ) ^ (d + 1)

theorem remainder_pointwise_tendsto {n m k d : ℕ} (hk : 1 ≤ k)
    (f : Fin (m + 2) → Hk L k) (hd : d + 1 ≤ 2 * k)
    (paths : Fin (m + 2) → Finset (Fin n)) (t : Fin n → ℝ) :
    Tendsto (fun z => remainder f d paths z t) (𝓝 0) (𝓝 0) := by
  exact (taylor_remainder_path_littleO hk f hd paths t).tendsto_inv_smul_nhds_zero

theorem remainder_bound {n m k d : ℕ} (hk : 1 ≤ k)
    (f : Fin (m + 2) → Hk L k) (hd : d + 1 ≤ 2 * k)
    (paths : Fin (m + 2) → Finset (Fin n)) (z : ℝ) (t : Fin n → ℝ) :
    ‖remainder f d paths z t‖ ≤ majorantConstant f d * (∑ i, |t i|) ^ (d + 1) := by
  let A : ℝ := 2 * (((m + 2 : ℕ) : ℝ) ^ (2 * k) * Bfull f)
  let Q : ℝ := ((m + 2 : ℕ) : ℝ)
  let T : ℝ := ∑ i, |t i|
  have hA : 0 ≤ A := by
    dsimp [A]
    have hB := Bfull_nonneg hk f
    positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hT : 0 ≤ T := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hC : 0 ≤ A * Q ^ (d + 1) * T ^ (d + 1) := by positivity
  by_cases hz : z = 0
  · subst z
    simpa [remainder, majorantConstant, A, Q, T] using hC
  · have hz' : 0 < |z| ^ (d + 1) := pow_pos (abs_pos.mpr hz) _
    have he := eucl_scaledShift_le paths z t
    have hpow := pow_le_pow_left₀ (Real.sqrt_nonneg _) he (d + 1)
    have hb := taylor_remainder_bound hk f hd (scaledShift paths z t)
    have hnum : ‖Cfun f (scaledShift paths z t) -
        taylorPoly (Cfun f) (d + 1) (scaledShift paths z t)‖ ≤
        (A * Q ^ (d + 1) * T ^ (d + 1)) * |z| ^ (d + 1) := by
      calc
        _ ≤ A * eucl (scaledShift paths z t) ^ (d + 1) := hb
        _ ≤ A * (Q * (|z| * T)) ^ (d + 1) := mul_le_mul_of_nonneg_left hpow hA
        _ = _ := by rw [mul_pow, mul_pow]; ring
    have hdiv := (div_le_iff₀ hz').2 hnum
    simpa only [remainder, majorantConstant, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_pow, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, A, Q, T] using hdiv

#print axioms remainder_pointwise_tendsto
#print axioms remainder_bound
end QuantumNLS.TerraMultiRound49TaylorBound
