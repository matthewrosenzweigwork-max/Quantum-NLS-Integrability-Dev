import Mathlib
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G3.G3003Host
import Armstrong.Work.RawBetaSum
import Armstrong.Work.RawBetaSumSpectralMass
import Armstrong.Work.RawBetaMagnitudeInverseProof

/- G3_011 PRODUCTION01 (proof development, AUTHOR; not semantically reviewed by its author).
   Target NlsGge/Atomic/G3/G3011.lean, namespace NlsGge.GKDefinitionDesign.
   Head VERBATIM from followup8 STATEMENTS/G3.md (the G3-011 block, identical in followup7 = round 9); checked by script.
   Route (root Decision 11 and 8/8c): instantiate Armstrong.Work.RawBetaMagnitudeInverseProof.gk151_inverseDistance_bound_working38
   (X-006 closure line 68, sha f1517319...) at the X-006 sourceFamily fields (W_open, W_real, W_gk, F_analytic, F_zero, F_inverse,
   F_period, F_real).  That theorem bounds gkSourceBeta38 on the subtype {chi // chi in W} for m != n by
   C * (||lamPlus-lamMinus|| + ||muSeq-tauN||) * Lib.c3w n m.  offDiagonalBeta = gk151BetaAmbient38 agrees with gkSourceBeta38 for
   m != n (gk151BetaAmbient_eq_source38, RawBetaSum.lean), and the diagonal m = n is zero (gk151BetaAmbient_diag38).
   The numerator ||gk151BetaMass38 phi m|| is rewritten by norm_gk151BetaMass38 (RawBetaSumSpectralMass.lean, closure line 86).
   No endpointDistance and no hypothesis beyond the head.  Not imported: Armstrong/Frozen/RawBetaMagnitude/*, NlsGge/GK38/RawBetaMagnitude.lean. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G3_011 :
  ∃ Winverse : Set PotPair,
    IsOpen Winverse ∧ range realSlice ⊆ Winverse ∧ Winverse ⊆ sourceW ∧
    ∀ φ0 ∈ Winverse, ∃ V : Set PotPair, ∃ C : ℝ,
      IsOpen V ∧ φ0 ∈ V ∧ V ⊆ Winverse ∧ 0 < C ∧
      ∀ φ ∈ V, ∀ n m : ℤ,
        ‖offDiagonalBeta n m φ‖ ≤ C * ‖gk151BetaMass38 φ m‖ * Lib.c3w n m := by
  obtain ⟨Wi, hWiO, hWiR, hWiW, hloc⟩ :=
    gk151_inverseDistance_bound_working38 sourceW sourceFamily.W_open
      sourceFamily.W_real sourceFamily.W_gk sourceF sourceFamily.F_analytic
      sourceFamily.F_zero sourceFamily.F_inverse sourceFamily.F_period
      sourceFamily.F_real
  refine ⟨Wi, hWiO, hWiR, hWiW, fun φ0 hφ0 => ?_⟩
  obtain ⟨V, C, hVo, hφV, hVW, hC, hb⟩ := hloc φ0 hφ0
  refine ⟨V, C, hVo, hφV, hVW, hC, fun φ hφ n m => ?_⟩
  by_cases hmn : m = n
  · have hdiag := congrFun (gk151BetaAmbient_diag38 sourceW sourceFamily.W_open
      sourceFamily.W_real sourceFamily.W_gk sourceF sourceFamily.F_analytic
      sourceFamily.F_zero sourceFamily.F_period n) φ
    have hz : offDiagonalBeta n m φ = 0 := by
      rw [hmn]
      exact hdiag
    rw [hz, norm_zero]
    exact mul_nonneg (mul_nonneg hC.le (norm_nonneg _)) (Lib.c3w_nonneg n m)
  · have hφW : φ ∈ sourceW := hWiW (hVW hφ)
    have h := hb ⟨φ, hφW⟩ hφ n m hmn
    have heq := gk151BetaAmbient_eq_source38 sourceW sourceFamily.W_open
      sourceFamily.W_real sourceFamily.W_gk sourceF sourceFamily.F_analytic
      sourceFamily.F_zero sourceFamily.F_period n m hmn ⟨φ, hφW⟩
    have e : offDiagonalBeta n m φ =
        gkSourceBeta38 sourceW sourceFamily.W_open sourceFamily.W_real
          sourceFamily.W_gk sourceF sourceFamily.F_analytic sourceFamily.F_zero
          sourceFamily.F_period n m hmn ⟨φ, hφW⟩ := heq
    rw [e, norm_gk151BetaMass38]
    exact h

end
end NlsGge.GKDefinitionDesign
