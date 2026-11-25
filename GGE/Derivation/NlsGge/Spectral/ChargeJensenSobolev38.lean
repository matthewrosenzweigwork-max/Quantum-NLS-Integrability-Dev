import NlsGge.Spectral.PlaneMomentInequality38V1
import NlsGge.Hierarchy.RiccatiSmoothDenseSobolev38
import NlsGge.Hierarchy.RiccatiLocalRemainderPaperForm38
import NlsGge.Hierarchy.RiccatiDerivativeParseval38
import NlsGge.Hierarchy.A01Spectral38
import Mathlib.Tactic

/-! F07 part 1 (`C:lem:massmoment`, `C:eq:momentineq`, paper/v2.tex lines 787-796):
`Q_{2m-2}(u) ≥ Q_0(u)^m` for every `u ∈ H^{m-1}`, `m ≥ 2`.

`Q_{2j}` on `H^{m-1}` (`j ≤ m`) is the continuous extension
`chargeSobolev38 m j y = Σ_n (2πn)^{2j} |y_n|² + R_j(y)`, where `R_j` is the realized
normalized remainder of the `j`-th charge on `H^{m-1}` (the F03 continuous polynomial,
the `j`-th summand of `localRemainderSobolev38`). On Sobolev elements of smooth
period-one fields it equals the local charge, hence the spectral charge (E02/E06).

Route: finite planes (trigonometric polynomials) satisfy `Q_{2j} ≥ Q_0^{j+1}`
(`planeMoment_mass38`, Jensen on the spectral measure through the trace formula plus
`Q_2 ≥ Q_0^2`); Fourier truncations converge in `H^{m-1}` and both sides are continuous. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Pilot NlsGge.Sobolev38
open MeasureTheory Filter Topology
open scoped ContDiff

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

/-- The Fourier quadratic part `Σ_n (2πn)^{2j} |y_n|²` on `H^r`. -/
def chargeQuad38 (r : ℝ) (j : ℕ) (y : SobolevHilbert r) : ℝ :=
  ∑' n : ℤ, (2 * Real.pi * (n : ℝ)) ^ (2 * j) *
    ‖(show WeightedHilbert (sobolevModeWeight r) from y) n‖ ^ 2

/-- The continuous extension of the `2j`-th charge `Q_{2j}` to `H^{m-1}`. -/
def chargeSobolev38 (m j : ℕ) (y : SobolevHilbert ((m - 1 : ℕ) : ℝ)) : ℝ :=
  chargeQuad38 _ j y +
    ∑ q ∈ (normalizedRemainder38 j).support,
      localRemainderMonomialValue38 m j q (toCarrier38 _ y)

theorem sobolevModeWeight_nat38 (k : ℕ) (n : ℤ) :
    sobolevModeWeight (k : ℝ) n = (1 + (n : ℝ) ^ 2) ^ k := by
  unfold sobolevModeWeight japaneseBracket
  show Real.sqrt (1 + (n : ℝ) ^ 2) ^ (2 * (k : ℝ)) = _
  rw [show (2 * (k : ℝ)) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, pow_mul,
    Real.sq_sqrt (by positivity)]

theorem chargeQuad_weight_le38 (k j : ℕ) (hj : j ≤ k) (n : ℤ) :
    1 + (2 * Real.pi * (n : ℝ)) ^ (2 * j) ≤
      (1 + (2 * Real.pi) ^ (2 * j)) * sobolevModeWeight (k : ℝ) n := by
  rw [sobolevModeWeight_nat38]
  have h1 : (1 : ℝ) ≤ (1 + (n : ℝ) ^ 2) ^ k := one_le_pow₀ (by nlinarith [sq_nonneg (n : ℝ)])
  have h2 : (2 * Real.pi * (n : ℝ)) ^ (2 * j) ≤ (2 * Real.pi) ^ (2 * j) * (1 + (n : ℝ) ^ 2) ^ k := by
    rw [mul_pow, pow_mul (n : ℝ), mul_comm 2 j, pow_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ((n : ℝ) ^ 2) ^ j ≤ (1 + (n : ℝ) ^ 2) ^ j :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
      _ ≤ (1 + (n : ℝ) ^ 2) ^ k := pow_le_pow_right₀ (by nlinarith [sq_nonneg (n : ℝ)]) hj
  nlinarith

theorem continuous_chargeQuad38 (k j : ℕ) (hj : j ≤ k) :
    Continuous (chargeQuad38 (k : ℝ) j) := by
  set w := sobolevModeWeight (k : ℝ) with hw
  set v : ℤ → ℝ := fun n => 1 + (2 * Real.pi * (n : ℝ)) ^ (2 * j) with hv
  have hvpos : ∀ n : ℤ, 0 < v n := fun n => by
    have : 0 ≤ (2 * Real.pi * (n : ℝ)) ^ (2 * j) := by
      rw [pow_mul]; positivity
    simp only [hv]; linarith
  have : Fact (∀ n : ℤ, 0 < v n) := ⟨hvpos⟩
  set u : ℤ → ℝ := fun _ => 1 with hu
  have : Fact (∀ n : ℤ, 0 < u n) := ⟨fun _ => one_pos⟩
  have hC : 0 ≤ 1 + (2 * Real.pi) ^ (2 * j) := by positivity
  let Lv := weightedRealComparisonContinuous w v _ hC (chargeQuad_weight_le38 k j hj)
  have hu1 : ∀ n : ℤ, u n ≤ 1 * w n := fun n => by
    simp only [hu, hw, sobolevModeWeight_nat38, one_mul]
    exact one_le_pow₀ (by nlinarith [sq_nonneg (n : ℝ)])
  let Lu := weightedRealComparisonContinuous w u 1 zero_le_one hu1
  have heq : chargeQuad38 (k : ℝ) j = fun y => ‖Lv y‖ ^ 2 - ‖Lu y‖ ^ 2 := by
    funext y
    have h1 := weightedHilbert_hasSum v (show WeightedHilbert v from Lv y)
    have h2 := weightedHilbert_hasSum u (show WeightedHilbert u from Lu y)
    have h3 := h1.sub h2
    refine (h3.tsum_eq).symm ▸ ?_
    unfold chargeQuad38
    refine tsum_congr (fun n => ?_)
    show _ = v n * ‖(show WeightedHilbert w from y) n‖ ^ 2 - u n * ‖(show WeightedHilbert w from y) n‖ ^ 2
    simp only [hv, hu]; ring
  rw [heq]
  exact (Lv.continuous.norm.pow 2).sub (Lu.continuous.norm.pow 2)

theorem continuous_chargeSobolev38 (m j : ℕ) (hj : j ≤ m - 1) :
    Continuous (chargeSobolev38 m j) := by
  unfold chargeSobolev38
  refine (continuous_chargeQuad38 (m - 1) j hj).add ?_
  exact continuous_finsetSum _ (fun q _ =>
    (continuous_localRemainderMonomialValue38 m j q).comp (continuous_toCarrier38 _))

/-- On the Sobolev element of a smooth period-one field the extension is the local charge. -/
theorem chargeSobolev38_smooth (m j : ℕ) (hm : 2 ≤ m) (hjm : j ≤ m)
    (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1)
    (x : SobolevHilbert ((m - 1 : ℕ) : ℝ))
    (hsource : ∀ n : ℤ,
      (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from x) n =
        physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First u hu.continuous hper)) n) :
    chargeSobolev38 m j x = localCharge38 u j := by
  have h1 := formalChargeIntegrand_integral_quadratic_plus_uniformRemainderNativeRecovery29Fourth
    j u hu hper
  have h2 := formalChargeQuadraticMainTerm_integral_eq38 j u hu hper
  have hR := localRemainderCharge38_smooth m j hm hjm u hu hper x hsource
  have hP := (smoothDerivative_parseval38 j u hu hper).2
  unfold chargeSobolev38 localCharge38
  rw [h1, h2, intervalIntegral.integral_ofReal, Complex.add_re, Complex.ofReal_re, ← hR, hP]
  congr 1
  unfold chargeQuad38
  refine tsum_congr (fun n => ?_)
  rw [hsource n, two_pi_abs_pow_even38]

/-- Identification with the paper's spectral charge on smooth fields. -/
theorem chargeSobolev38_smooth_spectral (m j : ℕ) (hm : 2 ≤ m) (hjm : j ≤ m)
    (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1)
    (x : SobolevHilbert ((m - 1 : ℕ) : ℝ))
    (hsource : ∀ n : ℤ,
      (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from x) n =
        physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First u hu.continuous hper)) n) :
    chargeSobolev38 m j x = spectralCharge38 u hu hper j := by
  rw [chargeSobolev38_smooth m j hm hjm u hu hper x hsource]
  exact localCharge_eq_spectralCharge38 u hu hper j

/-- On the truncation (a finite plane) the extension is the plane local charge. -/
theorem chargeSobolev38_trunc (m j : ℕ) (hm : 2 ≤ m) (hjm : j ≤ m) (N : ℕ)
    (x : SobolevHilbert ((m - 1 : ℕ) : ℝ)) :
    chargeSobolev38 m j (truncSobolev38 _ N x) =
      localCharge38 (planeReal N (fun i => (show WeightedHilbert
        (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from x) (modeIndex N i))) j :=
  chargeSobolev38_smooth m j hm hjm (truncField38 _ N x) (contDiff_truncField38 _ N x)
    (periodic_truncField38 _ N x) _ (truncSobolev38_link _ N x)

/-- F07 part 1 (`C:eq:momentineq`): `Q_{2m-2}(u) ≥ Q_0(u)^m` for `u ∈ H^{m-1}`, `m ≥ 2`,
with `Q_{2j}` the continuous extension `chargeSobolev38 m j`. -/
theorem chargeMoment_mass_sobolev38 (m : ℕ) (hm : 2 ≤ m)
    (x : SobolevHilbert ((m - 1 : ℕ) : ℝ)) :
    (chargeSobolev38 m 0 x) ^ m ≤ chargeSobolev38 m (m - 1) x := by
  have hc0 : Continuous (fun y => (chargeSobolev38 m 0 y) ^ m) :=
    (continuous_chargeSobolev38 m 0 (Nat.zero_le _)).pow m
  have hc1 := continuous_chargeSobolev38 m (m - 1) le_rfl
  refine le_of_tendsto_of_tendsto' (hc0.continuousAt.tendsto.comp (tendsto_truncSobolev38 _ x))
    (hc1.continuousAt.tendsto.comp (tendsto_truncSobolev38 _ x)) (fun N => ?_)
  simp only [Function.comp]
  rw [chargeSobolev38_trunc m 0 hm (Nat.zero_le _), chargeSobolev38_trunc m (m - 1) hm (by omega)]
  have := planeMoment_mass38 N (fun i => (show WeightedHilbert
        (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from x) (modeIndex N i)) (m - 1) (by omega)
  rwa [show m - 1 + 1 = m by omega] at this

end NlsGge.HierarchyRiccati.Core

end
