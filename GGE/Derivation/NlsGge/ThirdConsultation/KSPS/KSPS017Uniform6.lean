import Mathlib
import NlsGge.Atomic.KSPS.KSPS013
import NlsGge.Atomic.KSPS.KSPS014
import NlsGge.ThirdConsultation.KSPS.KSPS011Quant2
import NlsGge.ThirdConsultation.KSPS.KSPS011Quant4
import NlsGge.ThirdConsultation.KSPS.KSPS011Quant5
import NlsGge.ThirdConsultation.KSPS.KSPSAntitraceUniform
import NlsGge.ThirdConsultation.KSPS.KSPSUniformU1
import NlsGge.ThirdConsultation.KSPS.KSPSUniformU3
import NlsGge.ThirdConsultation.KSPS.KSPS017Uniform3
import NlsGge.ThirdConsultation.KSPS.KSPS017Uniform4
import NlsGge.ThirdConsultation.KSPS.KSPS017Uniform5
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform11

/- KSPS017U6 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). GLUE (root main probe: the joint
   closure is above the worker-lane memory cap). Target NlsGge/ThirdConsultation/KSPS/KSPS017Uniform6.lean.
   Pro round-15 SUPPORT (never a packet), chain B.
   * deriv_tail_uniform: ball-uniform tail KSPS-017 at every admissible ξ (‖ξ_n − nπ‖ ≤ a/w_n), = KSPS017U4.deriv_tail_of
     with every hypothesis discharged by a proved theorem: KSPS-013 integrated_riccati_vanishing, KSPS-014
     WKB_monodromy_entries (B = B₀), KSPSU3.integralRiccatiLeft_uniform, NlsGge.ThirdConsultation.KSPSWKB.endpoint_remainder_tail_U,
     KSPSUG.diag_lower/upper_tail_U (exactly as in KSPSUG.boundary_characteristics_WKB_tail_U), KSPS017U5.diag_tail_*_of
     (from KSPSUG.diag_approx_*_U at strip width a+1), KSPS017U5.off_tail_of (from KSPS017U3.off_approx_U_of with the
     producers sourceRemainder_endpoint_expansion_U, KSPSQ2.forcing_osc_U, KSPSQ2.a1_osc_U), g = KSPS017W.Rfun
     (Rfun_differentiableAt), φ' = KSPSU1.toOne.
   * h17U: the exact h17U binder of KSPS025U11.h24_of17 (ξ = criticalEigenvalue φ, KSPSU1.crit_localization_uniform).
   * h24_uniform: KSPS025U11.h24_of17 applied to h17U (the h24 binder of KSPS025U15.midpoint_spectral_expansion_uniform_of24).
   No hypothesis added. -/
set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators Topology

namespace NlsGge.ThirdConsultation.KSPS017U6
noncomputable section
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation.KSPS

theorem deriv_tail_uniform (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) (a : ℝ) (ha : 0 ≤ a) :
    ∃ (M : ℕ) (C : ℝ), ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n) →
      ∀ F : Finset ℤ, (∀ n ∈ F, (M : ℤ) ≤ |n|) →
        ∑ n ∈ F, (indexWeight n ^ (N + 1) *
          ‖deriv (discriminant φ) (xi n) -
            NlsGge.ThirdConsultation.KSPSWKB.discriminantDerivativeMain N φ xi n‖) ^ 2 ≤ C := by
  have hKB : (0 : ℝ) ≤ 2 * B₀ := by positivity
  have ha1 : (0 : ℝ) ≤ a + 1 := by linarith
  have hball : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ‖φ.1‖ + ‖φ.2‖ ≤ 2 * B₀ := fun φ hφ =>
    (NlsGge.ThirdConsultation.KSPS017U5.norm_pair_le φ).trans (by linarith)
  have hone1 : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      sobolevNorm 1 (NlsGge.ThirdConsultation.KSPSU1.toOne hN φ) ≤ B₀ := fun φ hφ =>
    (NlsGge.ThirdConsultation.KSPSU1.sobolevNorm_toOne_le hN φ).trans hφ
  have hone : ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ∃ φ' : SobolevC 1, sobolevNorm 1 φ' ≤ B₀ ∧
      NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = toPotPair φ := fun φ hφ =>
    ⟨NlsGge.ThirdConsultation.KSPSU1.toOne hN φ, hone1 φ hφ,
      NlsGge.ThirdConsultation.KSPSU1.toPotPair_toOne hN φ⟩
  -- KSPS-011 / KSPS-012 tails (as in KSPSUG.boundary_characteristics_WKB_tail_U)
  obtain ⟨NL, CL, -, hL⟩ :=
    NlsGge.ThirdConsultation.KSPSWKB.endpoint_remainder_tail_U hN (2 * B₀) B₀ hKB hB₀ false a ha
  obtain ⟨NU, CU, -, hU⟩ :=
    NlsGge.ThirdConsultation.KSPSWKB.endpoint_remainder_tail_U hN (2 * B₀) B₀ hKB hB₀ true a ha
  obtain ⟨N1, C1, -, h1⟩ := NlsGge.ThirdConsultation.KSPSUG.diag_lower_tail_U hN (2 * B₀) B₀ hKB hB₀ a ha
  obtain ⟨N2, C2, -, h2⟩ := NlsGge.ThirdConsultation.KSPSUG.diag_upper_tail_U hN (2 * B₀) B₀ hKB hB₀ a ha
  -- Riccati integral
  obtain ⟨CI, -, hCI⟩ := NlsGge.ThirdConsultation.KSPSU3.integralRiccatiLeft_uniform N hN B₀ hB₀
  -- differentiated diagonal remainders
  obtain ⟨Cf, Lf, hCf, hLf, hapf⟩ :=
    NlsGge.ThirdConsultation.KSPSUG.diag_approx_false_U hN (2 * B₀) B₀ hKB hB₀ (a + 1) ha1
  obtain ⟨Ct, Lt, hCt, hLt, hapt⟩ :=
    NlsGge.ThirdConsultation.KSPSUG.diag_approx_true_U hN (2 * B₀) B₀ hKB hB₀ (a + 1) ha1
  obtain ⟨ND1, CD1, hD1⟩ :=
    NlsGge.ThirdConsultation.KSPS017U5.diag_tail_false_of hN B₀ hB₀ a ha hone Cf Lf hCf hLf hapf
  obtain ⟨ND2, CD2, hD2⟩ :=
    NlsGge.ThirdConsultation.KSPS017U5.diag_tail_true_of hN B₀ hB₀ a ha hone Ct Lt hCt hLt hapt
  -- differentiated off-diagonal remainders
  obtain ⟨D, hD0, hD⟩ := NlsGge.ThirdConsultation.KSPS017U5.coef_top_le hN B₀ hB₀
  obtain ⟨C8, L8, hC8, hL8, h8⟩ :=
    NlsGge.ThirdConsultation.KSPSWKB.sourceRemainder_endpoint_expansion_U hN (2 * B₀) B₀ hKB hB₀ (a + 1) ha1
  obtain ⟨Kt, hKt0, hKt⟩ := NlsGge.ThirdConsultation.KSPSQ2.forcing_osc_U hN (2 * B₀) hKB true (a + 1) L8 hL8
  obtain ⟨Kf, hKf0, hKf⟩ := NlsGge.ThirdConsultation.KSPSQ2.forcing_osc_U hN (2 * B₀) hKB false (a + 1) L8 hL8
  obtain ⟨Mt, hMt0, hMt⟩ := NlsGge.ThirdConsultation.KSPSQ2.a1_osc_U hN (2 * B₀) hKB true (a + 1)
  obtain ⟨Mf, hMf0, hMf⟩ := NlsGge.ThirdConsultation.KSPSQ2.a1_osc_U hN (2 * B₀) hKB false (a + 1)
  obtain ⟨Cot, Lot, hCot, hLot, hot⟩ := NlsGge.ThirdConsultation.KSPS017U3.off_approx_U_of hN (2 * B₀) B₀ hKB hB₀
    true (a + 1) ha1 C8 L8 hC8 hL8 h8 Kt hKt0 hKt Mt hMt0 hMt
  obtain ⟨Cof, Lof, hCof, hLof, hof⟩ := NlsGge.ThirdConsultation.KSPS017U3.off_approx_U_of hN (2 * B₀) B₀ hKB hB₀
    false (a + 1) ha1 C8 L8 hC8 hL8 h8 Kf hKf0 hKf Mf hMf0 hMf
  obtain ⟨NO1, CO1, hO1⟩ := NlsGge.ThirdConsultation.KSPS017U5.off_tail_of B₀ true a ha hone D hD0
    (fun φ hφ => hD φ hφ true) Cot Lot hCot hLot hot
  obtain ⟨NO2, CO2, hO2⟩ := NlsGge.ThirdConsultation.KSPS017U5.off_tail_of B₀ false a ha hone D hD0
    (fun φ hφ => hD φ hφ false) Cof Lof hCof hLof hof
  exact NlsGge.ThirdConsultation.KSPS017U4.deriv_tail_of N hN B₀ hB₀ a ha
    (fun φ _ k hk => integrated_riccati_vanishing N k φ hk)
    (fun φ hφ lam hlam => (WKB_monodromy_entries N B₀ φ lam hφ hlam).2)
    CI (fun φ hφ => hCI φ hφ (N + 1) (by omega) le_rfl)
    NL CL (fun φ hφ xi hxi F hF => hL φ (hball φ hφ) (NlsGge.ThirdConsultation.KSPSU1.toOne hN φ)
      (hone1 φ hφ) (NlsGge.ThirdConsultation.KSPSU1.toPotPair_toOne hN φ) xi hxi F hF)
    NU CU (fun φ hφ xi hxi F hF => hU φ (hball φ hφ) (NlsGge.ThirdConsultation.KSPSU1.toOne hN φ)
      (hone1 φ hφ) (NlsGge.ThirdConsultation.KSPSU1.toPotPair_toOne hN φ) xi hxi F hF)
    N1 C1 (fun φ hφ xi hxi F hF => h1 φ (hball φ hφ) (NlsGge.ThirdConsultation.KSPSU1.toOne hN φ)
      (hone1 φ hφ) (NlsGge.ThirdConsultation.KSPSU1.toPotPair_toOne hN φ) xi hxi F hF)
    N2 C2 (fun φ hφ xi hxi F hF => h2 φ (hball φ hφ) (NlsGge.ThirdConsultation.KSPSU1.toOne hN φ)
      (hone1 φ hφ) (NlsGge.ThirdConsultation.KSPSU1.toPotPair_toOne hN φ) xi hxi F hF)
    ND1 CD1 (fun φ hφ xi hxi F hF => hD1 φ hφ (NlsGge.ThirdConsultation.KSPS017W.Rfun φ false 0)
      (fun z hz => NlsGge.ThirdConsultation.KSPS017W.Rfun_differentiableAt φ false 0 hz)
      (fun z hz => by unfold NlsGge.ThirdConsultation.KSPS017W.Rfun; rw [dif_neg hz]) xi hxi F hF)
    ND2 CD2 (fun φ hφ xi hxi F hF => hD2 φ hφ (NlsGge.ThirdConsultation.KSPS017W.Rfun φ true 1)
      (fun z hz => NlsGge.ThirdConsultation.KSPS017W.Rfun_differentiableAt φ true 1 hz)
      (fun z hz => by unfold NlsGge.ThirdConsultation.KSPS017W.Rfun; rw [dif_neg hz]) xi hxi F hF)
    NO1 CO1 (fun φ hφ xi hxi F hF => hO1 φ hφ (NlsGge.ThirdConsultation.KSPS017W.Rfun φ true 0)
      (fun z hz => NlsGge.ThirdConsultation.KSPS017W.Rfun_differentiableAt φ true 0 hz)
      (fun z hz => by simp [NlsGge.ThirdConsultation.KSPS017W.Rfun, hz]) xi hxi F hF)
    NO2 CO2 (fun φ hφ xi hxi F hF => hO2 φ hφ (NlsGge.ThirdConsultation.KSPS017W.Rfun φ false 1)
      (fun z hz => NlsGge.ThirdConsultation.KSPS017W.Rfun_differentiableAt φ false 1 hz)
      (fun z hz => by simp [NlsGge.ThirdConsultation.KSPS017W.Rfun, hz]) xi hxi F hF)

/-- h17U: the exact h17U binder of KSPS025U11.h24_of17. -/
theorem h17U (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) :
    ∃ (M : ℕ) (C : ℝ), ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ F : Finset ℤ, (∀ n ∈ F, (M : ℤ) ≤ |n|) →
        ∑ n ∈ F, (indexWeight n ^ (N + 1) *
          ‖deriv (discriminant φ) (criticalEigenvalue φ n) -
            NlsGge.ThirdConsultation.KSPSWKB.discriminantDerivativeMain N φ (criticalEigenvalue φ) n‖) ^ 2 ≤ C := by
  obtain ⟨a, ha, hloc⟩ := NlsGge.ThirdConsultation.KSPSU1.crit_localization_uniform N hN B₀ hB₀
  obtain ⟨M, C, h⟩ := deriv_tail_uniform N hN B₀ hB₀ a ha
  exact ⟨M, C, fun φ hφ F hF => h φ hφ (criticalEigenvalue φ) (hloc φ hφ) F hF⟩

/-- h24 (the binder of KSPS025U15.midpoint_spectral_expansion_uniform_of24), now unconditional. -/
theorem h24_uniform (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) :
    ∃ (M : ℕ) (C : ℝ), ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ F : Finset ℤ, (∀ n ∈ F, (M : ℤ) ≤ |n|) →
        ∑ n ∈ F, (indexWeight n ^ (N + 1) * ‖criticalEigenvalue φ n - spectralPolynomial φ n‖) ^ 2 ≤ C :=
  NlsGge.ThirdConsultation.KSPS025U11.h24_of17 N hN B₀ hB₀ (h17U N hN B₀ hB₀)

end
end NlsGge.ThirdConsultation.KSPS017U6
