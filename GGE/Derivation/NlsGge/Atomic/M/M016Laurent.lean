import Mathlib
import NlsGge.Atomic.M.M016ChartFinalHead
import NlsGge.Atomic.M.M016HalfNodeHead
import NlsGge.Atomic.M.M016DiscIdentity
import NlsGge.Atomic.M.M016FirstCoeff
import NlsGge.Atomic.M.M016MassAssembly
import NlsGge.Atomic.M.M053
import NlsGge.ThirdConsultation.KSPS.KSPS031SharpLaurent
import NlsGge.ThirdConsultation.M.M016Host

/- M016 LAURENT PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Proposed target
   NlsGge/Atomic/M/M016Laurent.lean. Needs ROOT MAIN PROBE, and needs proof development's host
   NlsGge/ThirdConsultation/M/M016Host.lean (`PrimitiveLaurentCoefficients`, M016HOST_PRODUCTION01) to land first.
   M-016 complex head `finitegap_primitive_laurent`, VERBATIM from followup13 STATEMENTS/M.md L541-548 (Pro r15 Q5 /
   r16 Q1 retain it). Route = Pro R16 Q1 / §4 / §5:
   * chart: `finitegap_pair_primitive_meromorphic_infinity` (same F for every conjunct);
   * N = 0: `discriminant_imaginary_bilinear_mass` + `primitive_discriminant_identity` on the chart +
     `M016ChartAux.first_coeff_generic` (Mathlib, lane-checked); H₁ = ∫uv from M053K1 `integralRiccatiCoefficient_one`
     and `WKB_hierarchy_coefficients_complex_one`;
   * N ≥ 1: `exterior_primitive_halfNode_eq` + h774's `KSPS031SL.sharp_littleO_along_halfNodes` (which uses h808's
     `nonresonant_WKB_coefficients_sharp`) + M053 `WKB_hierarchy_coefficients_complex` signs + `laurent_regroup`. -/

set_option autoImplicit false
open Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M

theorem finitegap_primitive_laurent
    (N : ℕ) (φ : KSPS.SobolevC N)
    (hW : KSPS.toPotPair φ ∈ gkW)
    (hfg : finiteGapPair (KSPS.toPotPair φ)) :
    ∃ R : ℝ, ∃ F : ℂ → ℂ,
      ExteriorPrimitiveRepresentative (KSPS.toPotPair φ) R F ∧
      MPrimitive.ExteriorHolomorphic F ∧
      PrimitiveLaurentCoefficients N φ F := by
  obtain ⟨R, F, hrep, hhol, hinf, hzero⟩ :=
    finitegap_pair_primitive_meromorphic_infinity (KSPS.toPotPair φ) hW hfg
  refine ⟨R, F, hrep, hhol, ?_⟩
  have hcosh : ∀ z : ℂ, R < ‖z‖ →
      2 * Complex.cosh (F z) = NlsGge.GK38.discrim (KSPS.toPotPair φ) z := by
    intro z hz
    obtain ⟨hz', e⟩ := hrep.2 z hz
    rw [e]
    exact primitive_discriminant_identity _ hz'.1 z hz'.2
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    intro K hK1 hK
    obtain rfl : K = 1 := le_antisymm hK hK1
    obtain ⟨C, R', hC, hR', hb⟩ := M016ChartAux.first_coeff_generic F
      (NlsGge.GK38.discrim (KSPS.toPotPair φ)) R _ hinf hcosh
      (discriminant_imaginary_bilinear_mass (KSPS.toPotPair φ))
    refine ⟨C, R', hC, hR', fun z hz => ?_⟩
    have hH : hierarchyCharge φ ⟨1, le_rfl, Nat.succ_le_succ (Nat.zero_le 0)⟩ =
        ∫ x in (0 : ℝ)..1, coverRep38 (KSPS.toPotPair φ).1 x * coverRep38 (KSPS.toPotPair φ).2 x := by
      have h1 := WKB_hierarchy_coefficients_complex_one 0 φ le_rfl (Nat.succ_le_succ (Nat.zero_le 0))
      rw [integralRiccatiCoefficient_one] at h1
      exact (neg_inj.1 h1).symm
    rw [Finset.Icc_eq_empty (by norm_num), Finset.sum_empty, sub_zero, hH]
    exact hb z hz
  · intro K hK1 hK
    obtain ⟨C, R', hC, hR', hb⟩ := KSPS031SL.sharp_littleO_along_halfNodes N hN φ F hinf
      (exterior_primitive_halfNode_eq N φ R F hrep hzero) K hK
    refine ⟨C, R', hC, hR', fun z hz => ?_⟩
    have h1 : KSPS.integralRiccatiLeft φ 1 =
        -hierarchyCharge φ ⟨1, le_rfl, Nat.succ_le_succ (Nat.zero_le N)⟩ := by
      have h := WKB_hierarchy_coefficients_complex N φ 1 le_rfl (Nat.succ_le_succ (Nat.zero_le N))
      rw [if_pos rfl] at h
      exact h
    have hk : ∀ (k : ℕ) (hk : 1 ≤ k ∧ k ≤ N + 1), 2 ≤ k →
        KSPS.integralRiccatiLeft φ k = hierarchyCharge φ ⟨k, hk.1, hk.2⟩ := by
      intro k hk hk2
      have h := WKB_hierarchy_coefficients_complex N φ k hk.1 hk.2
      rw [if_neg (by omega)] at h
      exact h
    have e := M016ChartAux.laurent_regroup N K hK1 hK (KSPS.integralRiccatiLeft φ)
      (fun k hk => hierarchyCharge φ ⟨k, hk.1, hk.2⟩) (2 * Complex.I * z) (F z + Complex.I * z) h1 hk
    have hbz := hb z hz
    rw [e] at hbz
    exact hbz

end NlsGge.ThirdConsultation.M
