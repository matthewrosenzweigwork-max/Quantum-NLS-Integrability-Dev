import QuantumNLS.Local005MajorantB
import Mathlib.MeasureTheory.Integral.CircleIntegral

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators ENNReal
open Complex
namespace QuantumNLS.Local005
open QuantumNLS.ResetFreeResolventLOCAL001
open QuantumNLS.LocalSpectral

/-- `projection` is S; `moment` is K, whose extra factor cancels one endpoint pole. -/
inductive WordKind | projection | moment
  deriving DecidableEq

def endpointOrder : WordKind → ℕ
  | .projection => 2
  | .moment => 1

def endpointBound (r : ℝ) : WordKind → ℝ
  | .projection => r⁻¹
  | .moment => 1

/-- Exact scalar contour integral for a compressed degree-k Neumann path.
The two endpoint resolvents supply w^-2 for S, and w^-1 for K. -/
def contourScalar (L r : ℝ) (kind : WordKind) {k : ℕ} (n : ℤ)
    (q : Fin (k - 1) → ℤ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ • ∮ z in C((pm L n : ℂ), r),
    (z - (pm L n : ℂ))⁻¹ ^ endpointOrder kind *
      ∏ i, (z - (pm L (sourceMode n (q i)) : ℂ))⁻¹

/-- The norm of the exact integrated path coefficient, before summing paths.
All k inputs are independent; conjugated slots may be supplied independently. -/
def contourAbsTerm (L r κ : ℝ) (kind : WordKind) {k : ℕ}
    (u : Fin k → ℤ → ℂ) (n : ℤ) (q : Fin (k - 1) → ℤ) : ℝ :=
  (2 * Real.sqrt (κ / L)) ^ k * amplitude u n q * ‖contourScalar L r kind n q‖

/-- The absolute Fourier-coefficient majorant of the integrated S or K word. -/
def contourMajorant (L r κ : ℝ) (kind : WordKind) (k : ℕ)
    (u : Fin k → ℤ → ℂ) (n : ℤ) : ℝ :=
  ∑' q : Fin (k - 1) → ℤ, contourAbsTerm L r κ kind u n q

theorem multiplier_le_gapWeight {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) {n : ℤ} {z : ℂ}
    (hz : OnGamma L r n z) (m : ℤ) :
    ‖(z - (pm L (sourceMode n m) : ℂ))⁻¹‖ ≤ gapWeight L r m := by
  have hb := freeResolventMultiplier_sq_le_majorant hL hr hsmall hz m
  change ‖(z - (pm L (sourceMode n m) : ℂ))⁻¹‖ ^ 2 ≤ _ at hb
  have he : gapWeight L r m ^ 2 = denominatorMajorant L r m :=
    Real.sq_sqrt (sq_nonneg _)
  have hnon : 0 ≤ gapWeight L r m := Real.sqrt_nonneg _
  nlinarith [norm_nonneg ((z - (pm L (sourceMode n m) : ℂ))⁻¹)]

/-- No pole lies on the contour, so the displayed integral is an actual integrable contour word. -/
theorem contour_integrable {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (kind : WordKind) {k : ℕ} (n : ℤ)
    (q : Fin (k - 1) → ℤ) :
    CircleIntegrable (fun z =>
      (z - (pm L n : ℂ))⁻¹ ^ endpointOrder kind *
        ∏ i, (z - (pm L (sourceMode n (q i)) : ℂ))⁻¹) (pm L n : ℂ) r := by
  apply ContinuousOn.circleIntegrable hr.le
  apply ContinuousOn.mul
  · apply ContinuousOn.pow
    apply (continuousOn_id.sub continuousOn_const).inv₀
    intro z hz
    have hg : OnGamma L r n z := mem_sphere_iff_norm.mp hz
    exact norm_pos_iff.mp (show 0 < ‖z - (pm L n : ℂ)‖ by rw [hg]; exact hr)
  · apply continuousOn_finsetProd
    intro i _
    apply (continuousOn_id.sub continuousOn_const).inv₀
    intro z hz
    have hg : OnGamma L r n z := mem_sphere_iff_norm.mp hz
    exact norm_pos_iff.mp (lt_of_lt_of_le hr
      (contour_denominator_lower hL hsmall hg (sourceMode_parity n (q i))))

theorem contourScalar_bound {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (kind : WordKind) {k : ℕ} (n : ℤ)
    (q : Fin (k - 1) → ℤ) :
    ‖contourScalar L r kind n q‖ ≤ endpointBound r kind * pathWeight L r q := by
  have hb : ∀ z ∈ Metric.sphere (pm L n : ℂ) r,
      ‖(z - (pm L n : ℂ))⁻¹ ^ endpointOrder kind *
        ∏ i, (z - (pm L (sourceMode n (q i)) : ℂ))⁻¹‖ ≤
        r⁻¹ ^ endpointOrder kind * pathWeight L r q := by
    intro z hz
    have hg : OnGamma L r n z := mem_sphere_iff_norm.mp hz
    rw [norm_mul, norm_pow, norm_inv, hg]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [norm_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun i _ => multiplier_le_gapWeight hL hr hsmall hg (q i))
  have hi := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr.le hb
  change ‖contourScalar L r kind n q‖ ≤ _ at hi
  convert hi using 1
  cases kind <;> simp only [endpointOrder, endpointBound] <;> field_simp <;> ring

theorem contourAbsTerm_nonneg (L r κ : ℝ) (kind : WordKind) {k : ℕ}
    (u : Fin k → ℤ → ℂ) (n : ℤ) (q : Fin (k - 1) → ℤ) :
    0 ≤ contourAbsTerm L r κ kind u n q :=
  mul_nonneg (mul_nonneg (pow_nonneg (by positivity) _) (amplitude_nonneg u n q))
    (norm_nonneg _)

theorem contour_majorant_data {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (κ : ℝ) (kind : WordKind) {k : ℕ}
    (u : Fin k → ℤ → ℂ) (hu : ∀ j, Summable fun m => ‖u j m‖ ^ 2) (n : ℤ) :
    Summable (contourAbsTerm L r κ kind u n) ∧
      0 ≤ contourMajorant L r κ kind k u n ∧
      contourMajorant L r κ kind k u n ≤ endpointBound r kind * envelope L r κ k u n := by
  have hs := (envelope_row hL hr hsmall κ u hu n).1
  have hbound : ∀ q : Fin (k - 1) → ℤ,
      contourAbsTerm L r κ kind u n q ≤
        endpointBound r kind * (2 * Real.sqrt (κ / L)) ^ k *
          (amplitude u n q * pathWeight L r q) := by
    intro q
    have hh := mul_le_mul_of_nonneg_left (contourScalar_bound hL hr hsmall kind n q)
      (mul_nonneg (pow_nonneg (show 0 ≤ 2 * Real.sqrt (κ / L) by positivity) k) (amplitude_nonneg u n q))
    simpa only [contourAbsTerm, mul_assoc, mul_left_comm, mul_comm] using hh
  have hsum : Summable (contourAbsTerm L r κ kind u n) :=
    Summable.of_nonneg_of_le (contourAbsTerm_nonneg L r κ kind u n) hbound
      (hs.mul_left (endpointBound r kind * (2 * Real.sqrt (κ / L)) ^ k))
  refine ⟨hsum, tsum_nonneg (contourAbsTerm_nonneg L r κ kind u n), ?_⟩
  calc
    _ ≤ ∑' q, endpointBound r kind * (2 * Real.sqrt (κ / L)) ^ k *
        (amplitude u n q * pathWeight L r q) :=
      hsum.tsum_le_tsum hbound (hs.mul_left _)
    _ = _ := by rw [tsum_mul_left]; exact mul_assoc _ _ _

#print axioms contour_integrable
#print axioms contourScalar_bound
#print axioms contour_majorant_data
end QuantumNLS.Local005
