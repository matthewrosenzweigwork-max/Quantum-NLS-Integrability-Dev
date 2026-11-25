import Mathlib
import QuantumNLS.RiccatiExpansionV
import QuantumNLS.RiccatiClassical
import QuantumNLS.RiccatiIndependentV
import QuantumNLS.RiccatiJBound
import QuantumNLS.RiccatiFloquet

/-!
# R-3FEAD88B stage (a): independent-`v` exponential identity (`RiccatiExpV`)

Frozen inputs (imported, not edited): `RiccatiExpansionV` (`norm_modeCoef_le`, `logV_expansion`),
`RiccatiClassical` (`cxDisc_fieldMap_riccati`), `RiccatiIndependentV` (`psiV_at_L`, `exp_log_cx`, `JV`),
`RiccatiJBound` (`sector_smallness`), `RiccatiFloquet` (`tail_exp_bound`), `RiccatiExpansions`
(`logS`, `logR`, `logB`, `modeCoef`, `physRep_norm_le`, `physK_nonneg`), `RiccatiPointwiseDisc`
(`physRep_continuous`).

Proved here (`exp_logS_eq_cxDisc_and_bound`, one theorem, three conjuncts):
1. `exp(logS L κ z J_v[r]) = exp(i z L / 2) · cxDisc κ (fieldMap (lowT u)) (fieldMap (lowT v)) z`, where
   `J_v[r] = modeCoef L a (lowT v) r = JV (physRep (lowT v)) (physRep r) L` (definitional), `r` a fixed point
   of `riccatiT (κ/L) (lowT u) (lowT v)`, and `κ > 0` is the physical coupling.
   Assembly: `cxDisc_fieldMap_riccati` gives `cxDisc = m + m⁻¹` with `m = psiV κ (physRep v) (physRep r) z L`;
   `psiV_at_L` gives `m = exp(L(-iz/2) + κ J_v)`; `exp_log_cx` (under `‖exp(izL - 2κJ_v)‖ < 1`) closes the identity.
   The route avoids `logS_eq_cxDisc`, whose hypotheses need pointwise-continuous `L2T` profiles and a pointwise
   ODE, which the fieldMap profiles do not supply; the algebra is the same.
2. The log bound of `logV_expansion`: `‖logS L κ z J_v − κ · (i Σ I_n z⁻ⁿ)‖ ≤ logC · |z|^{-(M+1)}`.
3. The smallness `‖exp(izL − 2κJ_v)‖ ≤ 1/2` (the hypothesis of `exp_log_cx`), from the same sector
   hypotheses as `logV_expansion`.

No `sorry`, `admit`, or custom axioms.
-/

open Set Filter Topology MeasureTheory
open QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.RiccatiSobolevE1
open QuantumNLS.RiccatiSobolevE2
open QuantumNLS.RiccatiSobolevE2b
open QuantumNLS.RiccatiSobolevE2bYoung
open QuantumNLS.RiccatiChargeLevels
open QuantumNLS.RiccatiPicardBall
open QuantumNLS.RiccatiPointwise
open QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.RiccatiPointwiseCoef
open QuantumNLS.RiccatiRemainder
open QuantumNLS.RiccatiMonodromy
open QuantumNLS.RiccatiFloquet
open QuantumNLS.RiccatiJBound
open QuantumNLS.RiccatiExpansions
open QuantumNLS.RiccatiExpansionV
open QuantumNLS.RiccatiChargeIdent
open QuantumNLS.ComplexifiedSobolevField

namespace QuantumNLS.RiccatiExpV

/-- **Stage (a): independent-`v` exponential identity.** With physical `κ > 0`, the Riccati fixed point
`r` of `riccatiT (κ/L) (lowT u) (lowT v)`, and the hypotheses of `logV_expansion`:
(1) `exp(logS L κ z J_v[r]) = exp(izL/2) · cxDisc κ (fieldMap (lowT u)) (fieldMap (lowT v)) z`;
(2) the log bound of `logV_expansion`;
(3) `‖exp(izL − 2κ J_v[r])‖ ≤ 1/2`. -/
theorem exp_logS_eq_cxDisc_and_bound {a S : ℝ} {M : ℕ} (L : ℝ) [Fact (0 < L)] (hL : 0 < L)
    (ha : 1 / 2 < a) (haS : a + (M : ℝ) + 1 ≤ S) (hM : 1 ≤ M) (κ : ℝ) (hκ : 0 < κ)
    (u v : Ell2) (β : ℝ) (hβ : 0 < β) (hu : ‖u‖ ≤ β) (hv : ‖v‖ ≤ β)
    (D : Ell2 →ₗ[ℂ] Ell2) (hD : ∀ y : dDom L, D (y : Ell2) = dmulEll L y)
    (δ : ℝ) (hδ : 0 < δ) (z : ℂ) (hz : 0 < z.im) (hsec : δ * ‖z‖ ≤ z.im)
    (hR : logR L a S M κ β δ ≤ ‖z‖)
    (r : Ell2) (hr : riccatiT hL ha hz (κ / L) (lowT L a S u) (lowT L a S v) r = r)
    (hrn : ‖r‖ ≤ 2 * β / z.im) :
    Complex.exp (logS L κ z (modeCoef L a (lowT L a S v) r))
        = Complex.exp (Complex.I * z * (L : ℂ) / 2)
          * QuantumNLS.ComplexifiedDiscriminant.cxDisc κ
              (fieldMap L a (by linarith : (0 : ℝ) ≤ a) (lowT L a S u))
              (fieldMap L a (by linarith : (0 : ℝ) ≤ a) (lowT L a S v)) z
    ∧ ‖logS L κ z (modeCoef L a (lowT L a S v) r)
          - (κ : ℂ) * (Complex.I * ∑ n ∈ Finset.Icc 1 M,
              modeCoef L a (lowT L a S v) (Wc S hL ha κ u v D n) * (z⁻¹) ^ n)‖
        ≤ logC L a S M κ β δ * (‖z‖ ^ (M + 1))⁻¹
    ∧ ‖Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * modeCoef L a (lowT L a S v) r)‖ ≤ 1 / 2 := by
  have ha0 : (0 : ℝ) ≤ a := by linarith
  -- smallness of the exponential tail (as in `logV_expansion`)
  have hR' := hR
  unfold logR at hR'
  have hz1 : 1 ≤ ‖z‖ := (le_max_of_le_right (le_max_left _ _)).trans hR'
  have hsm : (2 * |κ| * logB L a β δ + Real.log 2) / (δ * L) ≤ ‖z‖ :=
    (le_max_of_le_right (le_max_right _ _)).trans hR'
  have hlv : ‖lowT L a S v‖ ≤ β := (norm_lowT_le L a S v).trans hv
  have hδim : δ ≤ z.im := by nlinarith
  have hdiv : 2 * β / z.im ≤ 2 * β / δ := div_le_div_of_nonneg_left (by linarith) hδ hδim
  have hF : ∀ s : ℝ, ‖physRep L a (lowT L a S v) s‖ ≤ physK L a * β := fun s =>
    (physRep_norm_le hL ha _ s).trans (mul_le_mul_of_nonneg_left hlv (physK_nonneg ha0))
  have hRb : ∀ s : ℝ, ‖physRep L a r s‖ ≤ physK L a * (2 * β / δ) := fun s =>
    (physRep_norm_le hL ha r s).trans
      (mul_le_mul_of_nonneg_left (hrn.trans hdiv) (physK_nonneg ha0))
  have hJB : ‖modeCoef L a (lowT L a S v) r‖ ≤ logB L a β δ := by
    unfold modeCoef logB
    have h := norm_modeCoef_le hL.le (f := physRep L a (lowT L a S v)) (g := physRep L a r)
      (mul_nonneg (physK_nonneg ha0) hβ.le) (fun x _ => hF x) (fun x _ => hRb x)
    exact h.trans (le_of_eq (by ring))
  have hsmall : Real.exp (2 * |κ| * logB L a β δ) * Real.exp (-(z.im * L)) ≤ 1 / 2 :=
    sector_smallness (L := L) (δ := δ) (Kb := |κ|) (B := logB L a β δ)
      (R := (2 * |κ| * logB L a β δ + Real.log 2) / (δ * L)) (z := z) hL hδ le_rfl hsm hsec
  have hw : ‖Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * modeCoef L a (lowT L a S v) r)‖
      ≤ 1 / 2 :=
    (tail_exp_bound L κ z _ _ hJB).trans hsmall
  have hw1 : ‖Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * modeCoef L a (lowT L a S v) r)‖
      < 1 := lt_of_le_of_lt hw (by norm_num)
  -- (1) the identity, through the independent-`v` Floquet integral
  have hcx := QuantumNLS.RiccatiClassical.cxDisc_fieldMap_riccati hL ha ha0 hz κ hκ
    (lowT L a S u) (lowT L a S v) r hr
  have hpsi := QuantumNLS.RiccatiIndependentV.psiV_at_L κ z L
    (physRep_continuous L ha (lowT L a S v)) (physRep_continuous L ha r)
  have hJV : QuantumNLS.RiccatiIndependentV.JV (physRep L a (lowT L a S v)) (physRep L a r) L
      = modeCoef L a (lowT L a S v) r := rfl
  have hid : Complex.exp (logS L κ z (modeCoef L a (lowT L a S v) r))
      = Complex.exp (Complex.I * z * (L : ℂ) / 2)
        * QuantumNLS.ComplexifiedDiscriminant.cxDisc κ
            (fieldMap L a ha0 (lowT L a S u)) (fieldMap L a ha0 (lowT L a S v)) z := by
    rw [hcx, hpsi, hJV]
    unfold logS
    exact QuantumNLS.RiccatiIndependentV.exp_log_cx L κ z _ hw1
  -- (2) the log bound, from `logV_expansion`
  have hbound := logV_expansion L hL ha haS hM κ u v β hβ hu hv D hD δ hδ z hz hsec hR r hr hrn
  exact ⟨hid, hbound, hw⟩

end QuantumNLS.RiccatiExpV

#print axioms QuantumNLS.RiccatiExpV.exp_logS_eq_cxDisc_and_bound
