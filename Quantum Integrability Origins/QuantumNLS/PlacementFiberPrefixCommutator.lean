/-
QuantumNLS.PlacementFiberPrefixCommutator — explicit positive-overlap
commutator kernels for LOCAL-011.

This extension builds on the frozen aligned product expansion and reads
DEF-050 (RadiusBound) and DEF-042 (KernelConvergence) without modifying them.
-/
import QuantumNLS.PlacementFiberPrefixAlignedTransport
import QuantumNLS.KernelConvergence

set_option maxHeartbeats 5000000

open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements
  QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion
  QuantumNLS.PlacementOverlap QuantumNLS.PlacementProduct
  QuantumNLS.PlacementFiberPrefixAlignedTransport
  QuantumNLS.RadiusBound QuantumNLS.KernelConvergence
  QuantumNLS.OverlapMoments

noncomputable section

namespace QuantumNLS.PlacementFiberPrefixCommutator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem unionSize_comm (p q s : ℕ) (hsp : s ≤ p) (hsq : s ≤ q) :
    unionSize q p s = unionSize p q s := by
  dsimp [unionSize]
  omega

private theorem norm_castKernel {m n : ℕ} (h : m = n)
    (K : BoundedSymmetricKernel H m) : ‖h ▸ K‖ = ‖K‖ := by
  cases h
  rfl

/-- The explicit kernel for one positive-overlap commutator degree.  The
second product kernel is transported across the canonical equality of the
two union sizes before subtraction. -/
def overlapCommutatorKernel {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    BoundedSymmetricKernel H (unionSize p q s) :=
  averagedOverlapKernel hsp hsq A Bop -
    (unionSize_comm p q s hsp hsq ▸ averagedOverlapKernel hsq hsp Bop A)

/-- The positive-overlap commutator kernel has the source's factor-two
product norm bound. -/
theorem norm_overlapCommutatorKernel_le {p q s : ℕ}
    (hsp : s ≤ p) (hsq : s ≤ q)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    ‖overlapCommutatorKernel hsp hsq A Bop‖ ≤ 2 * (‖A‖ * ‖Bop‖) := by
  have hAB := norm_averagedOverlapKernel_le hsp hsq A Bop
  have hBA := norm_averagedOverlapKernel_le hsq hsp Bop A
  have hcast :
      ‖(unionSize_comm p q s hsp hsq ▸ averagedOverlapKernel hsq hsp Bop A)‖ =
        ‖averagedOverlapKernel hsq hsp Bop A‖ :=
    norm_castKernel _ _
  rw [overlapCommutatorKernel]
  calc
    _ ≤ ‖averagedOverlapKernel hsp hsq A Bop‖ +
        ‖(unionSize_comm p q s hsp hsq ▸ averagedOverlapKernel hsq hsp Bop A)‖ :=
      norm_sub_le (averagedOverlapKernel hsp hsq A Bop)
        (unionSize_comm p q s hsp hsq ▸ averagedOverlapKernel hsq hsp Bop A)
    _ = ‖averagedOverlapKernel hsp hsq A Bop‖ +
        ‖averagedOverlapKernel hsq hsp Bop A‖ := by rw [hcast]
    _ ≤ ‖A‖ * ‖Bop‖ + ‖Bop‖ * ‖A‖ := add_le_add hAB hBA
    _ = 2 * (‖A‖ * ‖Bop‖) := by ring

/-- Multiplication by the source's factor `i` leaves the local kernel norm
unchanged. -/
theorem norm_i_smul_overlapCommutatorKernel_le {p q s : ℕ}
    (hsp : s ≤ p) (hsq : s ≤ q)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    ‖(Complex.I : ℂ) • overlapCommutatorKernel hsp hsq A Bop‖ ≤
      2 * (‖A‖ * ‖Bop‖) := by
  have hnorm :
      ‖(Complex.I : ℂ) • overlapCommutatorKernel hsp hsq A Bop‖ =
        ‖overlapCommutatorKernel hsp hsq A Bop‖ := by
    calc
      _ = ‖(Complex.I : ℂ)‖ * ‖overlapCommutatorKernel hsp hsq A Bop‖ :=
        RadiusBound.norm_smul_kernel (Complex.I : ℂ)
          (overlapCommutatorKernel hsp hsq A Bop)
      _ = _ := by simp
  rw [hnorm]
  exact norm_overlapCommutatorKernel_le hsp hsq A Bop

/-- One fixed-degree positive-overlap commutator sum obeys the radius
majorant obtained from the first overlap moment.  This is the kernel-level
coefficient estimate used in the series radius-loss argument. -/
theorem positiveOverlap_commutatorKernel_radius_majorant
    {N p q : ℕ} {r : ℝ} (hp : p ≤ N) (hq : q ≤ N) (hr : 1 ≤ r)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    (∑ s ∈ (Finset.range (q + 1)).filter (fun s => 1 ≤ s),
      if hs : s ≤ min p q then
        (N : ℝ) * overlapCoefficient N p q s *
          (r ^ unionSize p q s *
            ‖(Complex.I : ℂ) • overlapCommutatorKernel
              (le_trans hs (min_le_left _ _))
              (le_trans hs (min_le_right _ _)) A Bop‖)
      else 0) ≤
      2 * (p * q : ℝ) * r ^ (p + q - 1) * ‖A‖ * ‖Bop‖ := by
  classical
  let S := (Finset.range (q + 1)).filter (fun s => 1 ≤ s)
  by_cases hN : 1 ≤ N
  · have hterm (s : ℕ) (hs : s ∈ S) :
        (if hs' : s ≤ min p q then
          (N : ℝ) * overlapCoefficient N p q s *
            (r ^ unionSize p q s *
              ‖(Complex.I : ℂ) • overlapCommutatorKernel
                (le_trans hs' (min_le_left _ _))
                (le_trans hs' (min_le_right _ _)) A Bop‖)
        else 0) ≤
          (N : ℝ) * overlapCoefficient N p q s *
            (r ^ (p + q - 1) * (2 * (‖A‖ * ‖Bop‖))) := by
      rcases Finset.mem_filter.mp hs with ⟨hsq', hspos⟩
      by_cases hsmin : s ≤ min p q
      · have hsle : unionSize p q s ≤ p + q - 1 := by
          dsimp [unionSize]
          omega
        have hr0 : 0 ≤ r := le_trans (by norm_num) hr
        have hpow : r ^ unionSize p q s ≤ r ^ (p + q - 1) :=
          pow_le_pow_right₀ hr hsle
        have hcomm := norm_i_smul_overlapCommutatorKernel_le
          (le_trans hsmin (min_le_left _ _))
          (le_trans hsmin (min_le_right _ _)) A Bop
        have hc : 0 ≤ (N : ℝ) * overlapCoefficient N p q s := by
          exact mul_nonneg (Nat.cast_nonneg _) (overlapCoefficient_nonneg N p q s)
        have hkernel :
            r ^ unionSize p q s *
                ‖(Complex.I : ℂ) • overlapCommutatorKernel
                  (le_trans hsmin (min_le_left _ _))
                  (le_trans hsmin (min_le_right _ _)) A Bop‖ ≤
              r ^ (p + q - 1) * (2 * (‖A‖ * ‖Bop‖)) := by
          calc
            _ ≤ r ^ (p + q - 1) *
                ‖(Complex.I : ℂ) • overlapCommutatorKernel
                  (le_trans hsmin (min_le_left _ _))
                  (le_trans hsmin (min_le_right _ _)) A Bop‖ :=
              mul_le_mul_of_nonneg_right hpow
                (norm_nonneg ((Complex.I : ℂ) • overlapCommutatorKernel
                  (le_trans hsmin (min_le_left _ _))
                  (le_trans hsmin (min_le_right _ _)) A Bop))
            _ ≤ _ := mul_le_mul_of_nonneg_left hcomm (pow_nonneg hr0 _)
        rw [dite_eq_left hsmin]
        calc
          (N : ℝ) * overlapCoefficient N p q s *
              (r ^ unionSize p q s *
                ‖(Complex.I : ℂ) • overlapCommutatorKernel
                  (le_trans hsmin (min_le_left _ _))
                  (le_trans hsmin (min_le_right _ _)) A Bop‖)
              ≤ (N : ℝ) * overlapCoefficient N p q s *
                  (r ^ (p + q - 1) * (2 * (‖A‖ * ‖Bop‖))) := by
                exact mul_le_mul_of_nonneg_left hkernel hc
          _ = _ := rfl
      · rw [dite_eq_right hsmin]
        have hc : 0 ≤ (N : ℝ) * overlapCoefficient N p q s := by
          exact mul_nonneg (Nat.cast_nonneg _) (overlapCoefficient_nonneg N p q s)
        positivity
    calc
      _ ≤ ∑ s ∈ S,
          (N : ℝ) * overlapCoefficient N p q s *
            (r ^ (p + q - 1) * (2 * (‖A‖ * ‖Bop‖))) := by
          apply Finset.sum_le_sum
          intro s hs
          exact hterm s hs
      _ = ((N : ℝ) *
          (∑ s ∈ S, overlapCoefficient N p q s)) *
            (r ^ (p + q - 1) * (2 * (‖A‖ * ‖Bop‖))) := by
          calc
            _ = (∑ s ∈ S,
                ((N : ℝ) * overlapCoefficient N p q s) *
                  (r ^ (p + q - 1) * (2 * (‖A‖ * ‖Bop‖)))) := by rfl
            _ = ((∑ s ∈ S,
                (N : ℝ) * overlapCoefficient N p q s) *
                  (r ^ (p + q - 1) * (2 * (‖A‖ * ‖Bop‖)))) := by
                  rw [Finset.sum_mul]
            _ = _ := by rw [Finset.mul_sum]
      _ ≤ ((N : ℝ) * ((p * q : ℝ) / N)) *
            (r ^ (p + q - 1) * (2 * (‖A‖ * ‖Bop‖))) := by
          have hprob := prob_intersect_le hp hq hN
          have hsum :
              (N : ℝ) * (∑ s ∈ S, overlapCoefficient N p q s) ≤
                (N : ℝ) * ((p * q : ℝ) / N) :=
            mul_le_mul_of_nonneg_left hprob (by positivity)
          exact mul_le_mul_of_nonneg_right hsum (by positivity)
      _ = 2 * (p * q : ℝ) * r ^ (p + q - 1) * ‖A‖ * ‖Bop‖ := by
          have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hN))
          field_simp [hNr]
  · have hN0 : N = 0 := by omega
    subst N
    have hp0 : p = 0 := by omega
    have hq0 : q = 0 := by omega
    subst p
    subst q
    simp

/-- Bernoulli's estimate for one radius ratio, stated in the form needed
to absorb the second degree in the commutator estimate. -/
private theorem degree_radius_loss_weight {R r : ℝ} (hr : 1 ≤ r) (hR : r < R)
    (q : ℕ) :
    (q : ℝ) * r ^ (q - 1) ≤ R ^ q / (R - r) := by
  by_cases hq : q = 0
  · subst q
    simp
    exact hR.le
  have hqpos : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hdpos : 0 < R - r := sub_pos.mpr hR
  have hx : 0 ≤ (R - r) / r := div_nonneg (sub_nonneg.mpr hR.le) hrpos.le
  have hBernoulli (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
      (n : ℝ) * x ≤ (1 + x) ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
        have hbase : 1 ≤ 1 + x := by linarith
        have hpow : 1 ≤ (1 + x) ^ n := one_le_pow₀ hbase
        calc
          ((n + 1 : ℕ) : ℝ) * x = (n : ℝ) * x + x := by push_cast; ring
          _ ≤ (1 + x) ^ n + x := add_le_add ih le_rfl
          _ ≤ (1 + x) ^ n + (1 + x) ^ n * x :=
            by
              simpa [one_mul] using
                (add_le_add_left (mul_le_mul_of_nonneg_right hpow hx)
                  ((1 + x) ^ n))
          _ = (1 + x) ^ (n + 1) := by rw [pow_succ]; ring
  have hrel : 1 + (R - r) / r = R / r := by field_simp [hrpos.ne']; ring
  have hB := hBernoulli q ((R - r) / r) hx
  rw [hrel] at hB
  have hpowmul := mul_le_mul_of_nonneg_right hB (pow_nonneg hrpos.le q)
  have hprod : (q : ℝ) * (R - r) * r ^ (q - 1) ≤ R ^ q := by
    have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel hqpos
    have hpowmul' := hpowmul
    rw [← hqsub, pow_succ] at hpowmul'
    field_simp [hrpos.ne'] at hpowmul'
    rw [hqsub] at hpowmul'
    have hmul' := mul_le_mul_of_nonneg_right hpowmul'
      (pow_nonneg hrpos.le (q - 1))
    calc
      (q : ℝ) * (R - r) * r ^ (q - 1) ≤
          r * (R / r) ^ q * r ^ (q - 1) := by
            exact hmul'
      _ = (R / r) ^ q * r ^ q := by
            calc
              _ = (R / r) ^ q * (r ^ (q - 1) * r) := by ring
              _ = (R / r) ^ q * r ^ q := by
                rw [← pow_succ, hqsub]
      _ = R ^ q := by rw [div_pow]; field_simp [hrpos.ne']
  rw [le_div_iff₀ hdpos]
  calc
    (q : ℝ) * r ^ (q - 1) * (R - r) =
        (q : ℝ) * (R - r) * r ^ (q - 1) := by ring
    _ ≤ R ^ q := hprod

/-- Sum of the explicit positive-overlap kernel commutator contributions
over arbitrary chosen kernel lists. This proves the source's radius-loss
coefficient estimate before equal output degrees are combined into one
`KernelList`; it does not claim that this candidate list represents the
operator commutator. No compatibility premise is supplied. -/
theorem positiveOverlap_commutatorSeries_radius_majorant
    {N : ℕ} {r R : ℝ} (hr : 1 ≤ r) (hR : r < R)
    (A B : QuantumNLS.LocalPlacement.KernelList (H := H) N) :
    (∑ p : Fin (N + 1), ∑ q : Fin (N + 1),
      ∑ s ∈ (Finset.range (q.1 + 1)).filter (fun s => 1 ≤ s),
        if hs : s ≤ min p.1 q.1 then
          (N : ℝ) * overlapCoefficient N p.1 q.1 s *
            (r ^ unionSize p.1 q.1 s *
              ‖(Complex.I : ℂ) • overlapCommutatorKernel
                (le_trans hs (min_le_left _ _))
                (le_trans hs (min_le_right _ _)) (A p) (B q)‖)
        else 0) ≤
      (2 / (R - r)) *
        (∑ p : Fin (N + 1), (p.1 : ℝ) * r ^ p.1 * ‖A p‖) *
        radiusBound R B := by
  classical
  calc
    _ ≤ ∑ p : Fin (N + 1), ∑ q : Fin (N + 1),
        2 * (p.1 * q.1 : ℝ) * r ^ (p.1 + q.1 - 1) * ‖A p‖ * ‖B q‖ := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      exact positiveOverlap_commutatorKernel_radius_majorant
        (Nat.lt_succ_iff.mp p.2) (Nat.lt_succ_iff.mp q.2) hr (A p) (B q)
    _ ≤ ∑ p : Fin (N + 1), ∑ q : Fin (N + 1),
        (2 / (R - r)) *
          ((p.1 : ℝ) * r ^ p.1 * ‖A p‖) *
          (R ^ q.1 * ‖B q‖) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      by_cases hq0 : q.1 = 0
      · simp [hq0]
        positivity
      have hexp : p.1 + q.1 - 1 = p.1 + (q.1 - 1) := by omega
      have hqbound := degree_radius_loss_weight hr hR q.1
      have hfactor : 0 ≤
          2 * ((p.1 : ℝ) * r ^ p.1 * ‖A p‖) * ‖B q‖ := by positivity
      have hmul := mul_le_mul_of_nonneg_left hqbound hfactor
      calc
        2 * (p.1 * q.1 : ℝ) * r ^ (p.1 + q.1 - 1) * ‖A p‖ * ‖B q‖ =
            (2 * ((p.1 : ℝ) * r ^ p.1 * ‖A p‖) * ‖B q‖) *
              ((q.1 : ℝ) * r ^ (q.1 - 1)) := by
                rw [hexp, pow_add]
                ring
        _ ≤ (2 * ((p.1 : ℝ) * r ^ p.1 * ‖A p‖) * ‖B q‖) *
              (R ^ q.1 / (R - r)) := hmul
        _ = (2 / (R - r)) *
              ((p.1 : ℝ) * r ^ p.1 * ‖A p‖) *
              (R ^ q.1 * ‖B q‖) := by field_simp
    _ = (2 / (R - r)) *
        (∑ p : Fin (N + 1), (p.1 : ℝ) * r ^ p.1 * ‖A p‖) *
        radiusBound R B := by
      have hrad : radiusBound R B =
          ∑ q : Fin (N + 1), R ^ q.1 * ‖B q‖ := rfl
      rw [hrad]
      calc
        _ = ∑ p : Fin (N + 1),
            (2 / (R - r)) *
              ((p.1 : ℝ) * r ^ p.1 * ‖A p‖) *
              (∑ q : Fin (N + 1), R ^ q.1 * ‖B q‖) := by
                apply Finset.sum_congr rfl
                intro p hp
                rw [← Finset.mul_sum]
        _ = (∑ p : Fin (N + 1),
              (2 / (R - r)) * ((p.1 : ℝ) * r ^ p.1 * ‖A p‖)) *
              (∑ q : Fin (N + 1), R ^ q.1 * ‖B q‖) := by
                symm
                exact Finset.sum_mul Finset.univ
                  (fun p : Fin (N + 1) =>
                    (2 / (R - r)) * ((p.1 : ℝ) * r ^ p.1 * ‖A p‖))
                  (∑ q : Fin (N + 1), R ^ q.1 * ‖B q‖)
        _ = (2 / (R - r) *
              (∑ p : Fin (N + 1), (p.1 : ℝ) * r ^ p.1 * ‖A p‖)) *
              (∑ q : Fin (N + 1), R ^ q.1 * ‖B q‖) := by
                congr 1
                exact (Finset.mul_sum Finset.univ
                  (fun p : Fin (N + 1) => (p.1 : ℝ) * r ^ p.1 * ‖A p‖)
                  (2 / (R - r))).symm

#print axioms degree_radius_loss_weight
#print axioms positiveOverlap_commutatorSeries_radius_majorant

#print axioms norm_overlapCommutatorKernel_le
#print axioms norm_i_smul_overlapCommutatorKernel_le
#print axioms positiveOverlap_commutatorKernel_radius_majorant

end QuantumNLS.PlacementFiberPrefixCommutator

end
