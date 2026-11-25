import QuantumNLS.F07Round6
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Integrate the F02 pointwise bound along the square-root coupling coordinate. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace QuantumNLS.F07ContinuityR6
open BetheSmooth F07Round6

def curve {N : ℕ} (L : ℝ) (b : Fin N → ℝ) (t : ℝ) : EuclideanSpace ℝ (Fin N) :=
  (EuclideanSpace.equiv (Fin N) ℝ).symm (root L b (t^2 / N))

def velocity {N : ℕ} (L : ℝ) (b : Fin N → ℝ) (t : ℝ) : EuclideanSpace ℝ (Fin N) :=
  (EuclideanSpace.equiv (Fin N) ℝ).symm ((2*t/N) • deriv (root L b) (t^2/N))

theorem curve_derivative {N : ℕ} (hN : 0 < N) {L t : ℝ} (hL : 0 < L)
    (ht : 0 < t) (b : Fin N → ℝ) : HasDerivAt (curve L b) (velocity L b t) t := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 < t^2 / N := div_pos (sq_pos_of_pos ht) hNr
  have hparam : HasDerivAt (fun s : ℝ => s^2 / N) (2*t/N) t := by
    convert ((hasDerivAt_id t).pow 2).div_const (N : ℝ) using 1 <;> simp <;> ring
  have hroot := (root_hasDerivAt hL hc b).scomp t hparam
  exact (EuclideanSpace.equiv (Fin N) ℝ).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hroot

theorem velocity_bound {N : ℕ} (hN : 0 < N) {L t : ℝ} (hL : 0 < L)
    (ht : 0 < t) (b : Fin N → ℝ) : ‖velocity L b t‖ ≤ Real.sqrt (N / L) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h := coupling_response_bound hN hL (sq_pos_of_pos ht) b
  have hnorm : ‖velocity L b t‖^2 ≤ (N : ℝ) / L := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ i, ((2*t/N) * deriv (root L b) (t^2/N) i)^2) ≤ (N : ℝ) / L
    have he (i : Fin N) : (2*t/N) * deriv (root L b) (t^2/N) i =
        (2/t) * ((t^2/N) * deriv (root L b) (t^2/N) i) := by
      field_simp
    calc
      _ = (2/t)^2 * ∑ i, ((t^2/N) * deriv (root L b) (t^2/N) i)^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [he, mul_pow]
      _ ≤ (2/t)^2 * (t^2 * N / (4*L)) :=
        mul_le_mul_of_nonneg_left h (sq_nonneg (2/t))
      _ = (N : ℝ)/L := by field_simp; norm_num
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (div_nonneg hNr.le hL.le)]
  exact hnorm

/-- F07 coupling continuity, expressed in the Euclidean norm of the actual roots. -/
theorem coupling_continuity {N : ℕ} (hN : 0 < N) {L K₀ K₁ : ℝ} (hL : 0 < L)
    (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) (b : Fin N → ℝ) :
    ‖(EuclideanSpace.equiv (Fin N) ℝ).symm
      (root L b (K₁/N) - root L b (K₀/N))‖ / Real.sqrt N ≤
        |Real.sqrt K₁ - Real.sqrt K₀| / Real.sqrt L := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs0 : 0 < Real.sqrt K₀ := Real.sqrt_pos.2 hK₀
  have hs1 : 0 < Real.sqrt K₁ := Real.sqrt_pos.2 hK₁
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.Ioi 0) (f := curve L b) (f' := velocity L b)
    (fun t ht => (curve_derivative hN hL ht b).hasDerivWithinAt)
    (fun t ht => velocity_bound hN hL ht b) (convex_Ioi 0) hs0 hs1
  have hb : ‖(EuclideanSpace.equiv (Fin N) ℝ).symm
      (root L b (K₁/N) - root L b (K₀/N))‖ ≤
      Real.sqrt (N / L) * |Real.sqrt K₁ - Real.sqrt K₀| := by
    simpa [curve, Real.sq_sqrt hK₀.le, Real.sq_sqrt hK₁.le, Real.norm_eq_abs, map_sub] using hm
  apply (div_le_iff₀ (Real.sqrt_pos.2 hNr)).2
  calc
    _ ≤ Real.sqrt (N / L) * |Real.sqrt K₁ - Real.sqrt K₀| := hb
    _ = (|Real.sqrt K₁ - Real.sqrt K₀| / Real.sqrt L) * Real.sqrt N := by
      rw [Real.sqrt_div hNr.le]
      ring
end QuantumNLS.F07ContinuityR6
#print axioms QuantumNLS.F07ContinuityR6.curve_derivative
#print axioms QuantumNLS.F07ContinuityR6.velocity_bound
#print axioms QuantumNLS.F07ContinuityR6.coupling_continuity


/-! Fixed-label intensive response at coupling K/N, in finite-sum form. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace QuantumNLS.F07EnergyR6
open BetheRoots BetheSmooth

def intensiveEnergy {N : ℕ} (L : ℝ) (b : Fin N → ℝ) (K : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * energy L b (K / N)

/-- Fixed-force response and its bounds, with the actual inverse Gaudin map. -/
theorem intensive_response {N : ℕ} (hN : 0 < N) {L K : ℝ}
    (hL : 0 < L) (hK : 0 < K) (b : Fin N → ℝ) :
    let q := root L b (K/N)
    let B := gaudin L (K/N) q
    K * deriv (intensiveEnergy L b) K = 2 * intensiveEnergy L b K -
      2 * L * ((N : ℝ)⁻¹ * ∑ i, q i * B.inverse q i) ∧
    0 ≤ K * deriv (intensiveEnergy L b) K ∧
    K * deriv (intensiveEnergy L b) K ≤ 2 * intensiveEnergy L b K := by
  dsimp only
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 < K / N := div_pos hK hNr
  have hparam : HasDerivAt (fun t : ℝ => t / N) (1 / N) K := by
    simpa using (hasDerivAt_id K).div_const (N : ℝ)
  have hchain := (((energy_hasDerivAt hL hc b).differentiableAt.hasDerivAt).comp K hparam).const_mul ((N : ℝ)⁻¹)
  have hd : deriv (intensiveEnergy L b) K =
      (N : ℝ)⁻¹ * (deriv (energy L b) (K/N) * (1/N)) := hchain.deriv
  have hscale : K * deriv (intensiveEnergy L b) K =
      (N : ℝ)⁻¹ * ((K/N) * deriv (energy L b) (K/N)) := by
    rw [hd]
    ring
  have he := energy_scaled_deriv_eq hL hc b
  have hb := energy_scaled_deriv_bounds hL hc b
  have hi : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr hNr.le
  have hb0 := mul_nonneg hi hb.1
  have hb1 := mul_le_mul_of_nonneg_left hb.2 hi
  rw [hscale]
  dsimp [intensiveEnergy]
  constructor
  · rw [he]
    ring
  constructor <;> nlinarith
end QuantumNLS.F07EnergyR6
#print axioms QuantumNLS.F07EnergyR6.intensive_response
