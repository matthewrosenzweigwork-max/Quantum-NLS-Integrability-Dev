import QuantumNLS.TerraMultiRound48PathBound
import QuantumNLS.CorrelationTaylor

/-! Geometric bounds and pointwise little-oh for Taylor remainders along
finite tree paths. This is not yet the integrated tree expansion. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Asymptotics
namespace QuantumNLS.TerraMultiRound49TaylorPath
open QuantumNLS.TranslatedCorrelation QuantumNLS.Sobolev
open QuantumNLS.CorrelationTaylor QuantumNLS.TerraMultiRound48Leading
open QuantumNLS.TerraMultiRound48PathBound

/-- Euclidean size is bounded by the sum of coordinate magnitudes. -/
theorem eucl_le_sum_abs {q : ℕ} (h : Fin q → ℝ) : eucl h ≤ ∑ j, |h j| := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  · calc
      ∑ j, h j ^ 2 = ∑ j, |h j| ^ 2 := by simp
      _ ≤ (∑ j, |h j|) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => abs_nonneg _)

/-- The Euclidean size of a finite path shift has the required linear
bound in the scale and the sum of absolute times. -/
theorem eucl_scaledShift_le {n q : ℕ} (paths : Fin q → Finset (Fin n))
    (z : ℝ) (t : Fin n → ℝ) :
    eucl (scaledShift paths z t) ≤ (q : ℝ) * (|z| * ∑ i, |t i|) := by
  calc
    _ ≤ ∑ j, |scaledShift paths z t j| := eucl_le_sum_abs _
    _ ≤ ∑ _j : Fin q, (|z| * ∑ i, |t i|) :=
      Finset.sum_le_sum (fun j _ => scaled_path_abs_le paths z t j)
    _ = _ := by simp

theorem eucl_smul {q : ℕ} (z : ℝ) (h : Fin q → ℝ) : eucl (z • h) = |z| * eucl h := by
  unfold eucl
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg z), Real.sqrt_sq_eq_abs]

theorem shift_eq_smul {n q : ℕ} (paths : Fin q → Finset (Fin n)) (z : ℝ)
    (t : Fin n → ℝ) : scaledShift paths z t = z • scaledShift paths 1 t := by
  ext j
  simp [scaledShift, mul_comm]

/-- Every positive-degree REG-006 Taylor remainder is little-oh along a
fixed path when measured against the scale power. -/
theorem taylor_remainder_path_littleO {L : ℝ} [Fact (0 < L)] {n m k d : ℕ}
    (hk : 1 ≤ k) (f : Fin (m + 2) → Hk L k) (hd : d + 1 ≤ 2 * k)
    (paths : Fin (m + 2) → Finset (Fin n)) (t : Fin n → ℝ) :
    (fun z : ℝ => Cfun f (scaledShift paths z t) -
      taylorPoly (Cfun f) (d + 1) (scaledShift paths z t)) =o[𝓝 0]
      (fun z : ℝ => z ^ (d + 1)) := by
  have h := (taylor_remainder_isLittleO hk f hd).comp_tendsto
    (scaledShift_tendsto_zero paths t)
  apply h.trans_isBigO
  apply IsBigO.of_bound (eucl (scaledShift paths 1 t) ^ (d + 1))
  filter_upwards with z
  dsimp only [Function.comp_apply]
  rw [shift_eq_smul, eucl_smul, mul_pow]
  rw [norm_mul, norm_pow, norm_pow, Real.norm_eq_abs, abs_abs,
    Real.norm_of_nonneg (show 0 ≤ eucl (scaledShift paths 1 t) from Real.sqrt_nonneg _), norm_pow, Real.norm_eq_abs]
  ring_nf
  exact le_rfl

#print axioms eucl_le_sum_abs
#print axioms eucl_scaledShift_le
#print axioms eucl_smul
#print axioms shift_eq_smul
#print axioms taylor_remainder_path_littleO
end QuantumNLS.TerraMultiRound49TaylorPath
