import QuantumNLS.IndexedInverseSeriesR28b

/-! Uniform inverse-series estimates on the literal open contour tubes.
The zero coefficient and all scalar majorants are proved from the inverse. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
noncomputable section
open Complex Set Metric Filter Topology
open scoped BigOperators
namespace QuantumNLS.IndexedInverseBoundsR29b
open PhysicalTensor KernelDefinition KernelConvergence LocalPlacement
  IndexedInverseR28b IndexedTransferR28b IndexedInverseSeriesR28b
variable {L κ : ℝ} [Fact (0 < L)]

theorem coeff_zero (hκ : 0 < κ) (n : ℤ) {z : ℂ} (hz : z ∈ tube L n) :
    coeff (L := L) κ z 0 = 0 := by
  rw [coeff,(series_represents hκ n hz).coeff_zero]
  simpa only [centered,add_zero] using inverse_center hκ n hz

theorem norm_centered_le (hκ : 0 < κ) (n : ℤ) {z x : ℂ}
    (hz : z ∈ tube L n) (hx : ‖x‖ < rstar) :
    ‖centered (L := L) κ z x‖ ≤ W κ := by
  exact (mem_ball_zero_iff.mp
    (inverse_disk hκ n hz (y := Ext025A7.spectralMap κ L z 0+x)
      (by simpa only [add_sub_cancel_left] using hx)).1).le

/-- One uniform majorant for every label and every point in its tube. -/
theorem norm_coeff_le_uniform (hκ : 0 < κ) (n : ℤ) {z : ℂ}
    (hz : z ∈ tube L n) (k : ℕ) :
    ‖coeff (L := L) κ z k‖ ≤ W κ*(rstar/2)⁻¹^k := by
  have hb : ∀ θ : ℝ, ‖centered (L := L) κ z (circleMap 0 (rstar/2) θ)‖ ≤ W κ := by
    intro θ
    apply norm_centered_le hκ n hz
    rw [norm_circleMap_zero,abs_of_pos (by norm_num [rstar] : 0 < rstar/2)]
    norm_num [rstar]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := 2*Real.pi)
    (f := fun θ => ‖centered (L := L) κ z (circleMap 0 (rstar/2) θ)‖)
    (fun θ _ => by simpa only [Real.norm_eq_abs,abs_norm] using hb θ)
  have hi' : (∫ θ : ℝ in 0..2*Real.pi,
      ‖centered (L := L) κ z (circleMap 0 (rstar/2) θ)‖) ≤ W κ*(2*Real.pi) := by
    have hp : |2*Real.pi-0| = 2*Real.pi := by
      rw [sub_zero,abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    have hh := (le_abs_self _).trans hi
    simpa only [hp] using hh
  calc
    _ ≤ ‖series (L := L) κ z k‖ := norm_coeff_le κ z k
    _ ≤ ((2*Real.pi)⁻¹ * ∫ θ : ℝ in 0..2*Real.pi,
        ‖centered (L := L) κ z (circleMap 0 (rstar/2) θ)‖)*(rstar/2)⁻¹^k := by
      simpa only [series,abs_of_pos (by norm_num [rstar] : 0 < rstar/2)] using
        norm_cauchyPowerSeries_le (centered (L := L) κ z) 0 (rstar/2) k
    _ ≤ ((2*Real.pi)⁻¹*(W κ*(2*Real.pi)))*(rstar/2)⁻¹^k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi' (by positivity))
        (by norm_num [rstar])
    _ = _ := by field_simp

def q (κ L : ℝ) : ℝ := (256*(κ*L))/(rstar/2)

theorem q_bounds (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000) :
    0 ≤ q κ L ∧ q κ L < 1/500000 := by
  have hL : 0 < L := Fact.out
  constructor
  · unfold q rstar; positivity
  · unfold q rstar; norm_num at *; linarith

theorem majorant_summable (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    (n : ℤ) {z : ℂ} (hz : z ∈ tube L n) :
    Summable (fun k => ‖coeff (L := L) κ z k‖*(256*(κ*L))^k) := by
  apply Local013PowerSeries.summable_majorant _ _ (coefficient_summable hκ n hz)
  · have hL : 0 < L := Fact.out; positivity
  · norm_num [rstar] at *; linarith

/-- A quantitative bound uniform in both N and z, with no constant term. -/
theorem radius_bound_inverse (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    (n : ℤ) {z : ℂ} (hz : z ∈ tube L n) (N : ℕ) :
    RadiusBound.radiusBound 8 (inverseKernels (L := L) κ z N) ≤
      W κ*(q κ L)/(1-q κ L) := by
  have hq := q_bounds hκ hs
  have hq1 : q κ L < 1 := by linarith
  have hgeo : Summable (fun k : ℕ => W κ*(q κ L)^k) :=
    (summable_geometric_of_lt_one hq.1 hq1).mul_left _
  calc
    _ ≤ ∑' k, ‖coeff (L := L) κ z k‖*(256*(κ*L))^k :=
      Local013PowerSeries.radiusBound_psList_le (by norm_num)
        (radius_bound hκ hs n hz) (majorant_summable hκ hs n hz) N
    _ = ∑' j : ℕ, ‖coeff (L := L) κ z (j+1)‖*(256*(κ*L))^(j+1) := by
      rw [(majorant_summable hκ hs n hz).tsum_eq_zero_add]
      rw [coeff_zero hκ n hz,norm_zero,zero_mul,zero_add]
    _ ≤ ∑' j : ℕ, W κ*(q κ L)^(j+1) := by
      apply Summable.tsum_le_tsum _
        ((majorant_summable hκ hs n hz).comp_injective (fun a b h => Nat.add_right_cancel h))
        (hgeo.comp_injective (fun a b h => Nat.add_right_cancel h))
      intro j
      simp only [Function.comp_apply]
      calc
        _ ≤ (W κ*(rstar/2)⁻¹^(j+1))*(256*(κ*L))^(j+1) := by
          exact mul_le_mul_of_nonneg_right (norm_coeff_le_uniform hκ n hz _)
            (by have hL : 0 < L := Fact.out; positivity)
        _ = _ := by
          rw [mul_assoc,← mul_pow]
          congr 2
          unfold q
          ring
    _ = W κ*(q κ L)/(1-q κ L) := by
      have he : (fun j : ℕ => W κ*(q κ L)^(j+1)) =
          fun j => (W κ*q κ L)*(q κ L)^j := by funext j; rw [pow_succ]; ring
      rw [he,tsum_mul_left,tsum_geometric_of_lt_one hq.1 hq1]
      ring

theorem scaled_radius_small (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    (n : ℤ) {z : ℂ} (hz : z ∈ tube L n) (N : ℕ) :
    κ*RadiusBound.radiusBound 8 (inverseKernels (L := L) κ z N) < 1/100000000 := by
  have hq := q_bounds hκ hs
  have hd : 0 < 1-q κ L := by linarith
  calc
    _ ≤ κ*(W κ*q κ L/(1-q κ L)) :=
      mul_le_mul_of_nonneg_left (radius_bound_inverse hκ hs n hz N) hκ.le
    _ = (1/1000)*q κ L/(1-q κ L) := by rw [← mul_div_assoc,← mul_assoc,W_small hκ]
    _ < _ := by apply (div_lt_iff₀ hd).mpr; nlinarith

end QuantumNLS.IndexedInverseBoundsR29b
#print axioms QuantumNLS.IndexedInverseBoundsR29b.norm_coeff_le_uniform
#print axioms QuantumNLS.IndexedInverseBoundsR29b.radius_bound_inverse
#print axioms QuantumNLS.IndexedInverseBoundsR29b.scaled_radius_small
