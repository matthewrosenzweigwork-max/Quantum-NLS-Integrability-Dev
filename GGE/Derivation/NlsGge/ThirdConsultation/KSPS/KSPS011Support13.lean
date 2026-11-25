import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS011Support5
import NlsGge.ThirdConsultation.KSPS.KSPS011Support11
import NlsGge.ThirdConsultation.KSPS.KSPS011Support12

/- KSPS-011 SUPPORT13 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS011Support13.lean. (1) comp_formula: component idx_b of
   forcingLeading + forcingFirstCorrection at x = 1 equals kappa_b * O_mu(F) + (2 lam)^-1 (q1 O_mu(F) - O_mu(qF)),
   mu = sigma_b lam, for any PotPair f representing sourceForcingVector (from Support10a). (2) endpoint_pointwise_bound: the pure
   real/complex inequality used for |n| >= N0. (3) 1/|n| is real-square-summable. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open NlsGge.Pilot NlsGge.GK38 NlsGge.ThirdConsultation.KSPSVolterra

namespace NlsGge.ThirdConsultation.KSPSWKB

theorem comp_formula {N : ℕ} (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N) (φ' : SobolevC 1)
    (b : Bool) (lam : {z : ℂ // z ≠ 0}) (f : PotPair)
    (hf : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ![potRepFst38 f t, potRepSnd38 f t] = sourceForcingVector φ b lam t) :
    (forcingLeading φ' lam.1 f 1 + forcingFirstCorrection φ' lam.1 f 1) (if b then 0 else 1) =
      (if b then -Complex.I else Complex.I) *
          endpointOsc ((if b then (-1 : ℂ) else 1) * lam.1)
            (NlsGge.ThirdConsultation.KSPSRiccati.forcing φ b lam.1) +
        (2 * lam.1)⁻¹ * (integratedQuadratic φ' 1 0 0 *
            endpointOsc ((if b then (-1 : ℂ) else 1) * lam.1)
              (NlsGge.ThirdConsultation.KSPSRiccati.forcing φ b lam.1) -
          endpointOsc ((if b then (-1 : ℂ) else 1) * lam.1)
            (fun t => integratedQuadratic φ' t 0 0 * NlsGge.ThirdConsultation.KSPSRiccati.forcing φ b lam.1 t)) := by
  cases b
  · have h := lower_component φ' lam.1 f (NlsGge.ThirdConsultation.KSPSRiccati.forcing φ false lam.1) (by
      refine hf.mono (fun t ht => ?_)
      rw [ht]
      simp [sourceForcingVector])
    simpa using h
  · have h := upper_component φ' lam.1 f (NlsGge.ThirdConsultation.KSPSRiccati.forcing φ true lam.1) (by
      refine hf.mono (fun t ht => ?_)
      rw [ht]
      simp [sourceForcingVector])
    simpa using h

theorem norm_add6_le (a b c d e f : ℂ) :
    ‖a + b + c + d + e + f‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
  have h1 := norm_add_le (a + b + c + d + e) f
  have h2 := norm_add_le (a + b + c + d) e
  have h3 := norm_add_le (a + b + c) d
  have h4 := norm_add_le (a + b) c
  have h5 := norm_add_le a b
  linarith

theorem endpoint_pointwise_bound (w Λ m C8 B1 M2 M3 Q : ℝ) (hw : 0 ≤ w) (hΛ : 0 < Λ) (hm : 1 ≤ m)
    (hmΛ : m ≤ Λ) (hwm : w ≤ 2 * m)
    (hC8 : 0 ≤ C8) (hB1 : 0 ≤ B1) (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3) (hQ : 0 ≤ Q)
    (lam κ ε1 k1 Pc ρ Oa Oc Oqc E1 U q1 dOf dOq : ℂ)
    (hlam : ‖lam‖ = Λ) (hκ : ‖κ‖ = 1) (hε1 : ‖ε1‖ = 1) (hk1 : ‖k1‖ ≤ 1 / (2 * Λ))
    (hU : ‖U‖ ≤ C8 / Λ ^ 2) (hE1 : ‖E1‖ ≤ B1 / Λ ^ 2) (hq1 : ‖q1‖ ≤ Q)
    (hdOf : ‖dOf‖ ≤ M2 / Λ) (hdOq : ‖dOq‖ ≤ M3 / Λ) :
    w * ‖U + κ * (k1 * Oa) + κ * E1 + κ * (Pc + ε1 * ρ) + (2 * lam)⁻¹ * (q1 * Oc - Oqc) +
        (2 * lam)⁻¹ * (q1 * dOf - dOq)‖ ≤
      (2 * C8 + 2 * B1 + (Q * M2 + M3)) / m + w * ‖Pc‖ + w * ‖ρ‖ + ‖Oa‖ + Q * ‖Oc‖ + ‖Oqc‖ := by
  have hm0 : 0 < m := by linarith
  have hn2 : ‖(2 * lam)⁻¹‖ = 1 / (2 * Λ) := by
    rw [norm_inv, norm_mul, hlam]; simp
  have hs : w * (1 / (2 * Λ)) ≤ 1 := by
    rw [mul_one_div, div_le_one (by positivity)]; linarith
  have hu : w * (1 / Λ ^ 2) ≤ 2 / m := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) hm0]
    nlinarith
  have hv : w * (1 / (2 * Λ)) * (1 / Λ) ≤ 1 / m := by
    have h1 : 1 / Λ ≤ 1 / m := one_div_le_one_div_of_le hm0 hmΛ
    calc w * (1 / (2 * Λ)) * (1 / Λ) ≤ 1 * (1 / Λ) := by gcongr
      _ ≤ 1 / m := by linarith
  have e6 := norm_add6_le U (κ * (k1 * Oa)) (κ * E1) (κ * (Pc + ε1 * ρ))
    ((2 * lam)⁻¹ * (q1 * Oc - Oqc)) ((2 * lam)⁻¹ * (q1 * dOf - dOq))
  have t1 : w * ‖U‖ ≤ C8 * (2 / m) := by
    calc w * ‖U‖ ≤ w * (C8 / Λ ^ 2) := by gcongr
      _ = C8 * (w * (1 / Λ ^ 2)) := by ring
      _ ≤ C8 * (2 / m) := by gcongr
  have t2 : w * ‖κ * (k1 * Oa)‖ ≤ ‖Oa‖ := by
    rw [norm_mul, norm_mul, hκ, one_mul]
    calc w * (‖k1‖ * ‖Oa‖) ≤ w * (1 / (2 * Λ) * ‖Oa‖) := by gcongr
      _ = (w * (1 / (2 * Λ))) * ‖Oa‖ := by ring
      _ ≤ 1 * ‖Oa‖ := by gcongr
      _ = ‖Oa‖ := one_mul _
  have t3 : w * ‖κ * E1‖ ≤ B1 * (2 / m) := by
    rw [norm_mul, hκ, one_mul]
    calc w * ‖E1‖ ≤ w * (B1 / Λ ^ 2) := by gcongr
      _ = B1 * (w * (1 / Λ ^ 2)) := by ring
      _ ≤ B1 * (2 / m) := by gcongr
  have t4 : w * ‖κ * (Pc + ε1 * ρ)‖ ≤ w * ‖Pc‖ + w * ‖ρ‖ := by
    rw [norm_mul, hκ, one_mul]
    have : ‖Pc + ε1 * ρ‖ ≤ ‖Pc‖ + ‖ρ‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, hε1, one_mul]
    nlinarith
  have t5 : w * ‖(2 * lam)⁻¹ * (q1 * Oc - Oqc)‖ ≤ Q * ‖Oc‖ + ‖Oqc‖ := by
    rw [norm_mul, hn2]
    have : ‖q1 * Oc - Oqc‖ ≤ Q * ‖Oc‖ + ‖Oqc‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul]
      gcongr
    calc w * (1 / (2 * Λ) * ‖q1 * Oc - Oqc‖) = (w * (1 / (2 * Λ))) * ‖q1 * Oc - Oqc‖ := by ring
      _ ≤ 1 * (Q * ‖Oc‖ + ‖Oqc‖) := by gcongr
      _ = _ := one_mul _
  have t6 : w * ‖(2 * lam)⁻¹ * (q1 * dOf - dOq)‖ ≤ (Q * M2 + M3) / m := by
    rw [norm_mul, hn2]
    have : ‖q1 * dOf - dOq‖ ≤ (Q * M2 + M3) / Λ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul]
      calc ‖q1‖ * ‖dOf‖ + ‖dOq‖ ≤ Q * (M2 / Λ) + M3 / Λ := by gcongr
        _ = (Q * M2 + M3) / Λ := by ring
    calc w * (1 / (2 * Λ) * ‖q1 * dOf - dOq‖) ≤ w * (1 / (2 * Λ) * ((Q * M2 + M3) / Λ)) := by gcongr
      _ = (Q * M2 + M3) * (w * (1 / (2 * Λ)) * (1 / Λ)) := by ring
      _ ≤ (Q * M2 + M3) * (1 / m) := by gcongr
      _ = _ := by ring
  have hsum := mul_le_mul_of_nonneg_left e6 hw
  have : (2 * C8 + 2 * B1 + (Q * M2 + M3)) / m = C8 * (2 / m) + B1 * (2 / m) + (Q * M2 + M3) / m := by
    field_simp
  rw [this]
  nlinarith [hsum, t1, t2, t3, t4, t5, t6]

theorem realSqSummable_inv_abs : RealSqSummable (fun n : ℤ => 1 / |(n : ℝ)|) := by
  unfold RealSqSummable
  have h := (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
  refine h.congr (fun n => ?_)
  rw [div_pow, one_pow, sq_abs]

end NlsGge.ThirdConsultation.KSPSWKB
