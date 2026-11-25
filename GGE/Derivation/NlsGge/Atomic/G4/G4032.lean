import Mathlib
import NlsGge.GK38.TauGamma
import NlsGge.Atomic.G4.G4017
import NlsGge.Atomic.G4.G4031

/- G4-032 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G4/G4032.lean.
   Head `G4032`: design STATEMENTS/G4.md G4-032 section, verbatim (byte-identical in followup1..10 STATEMENTS except where the file
   differs only outside this section; no Pro round entry or BINDING_INDEX touches G4-032; no lexical repair).
   Route: G4-031 uniform bound on a neighbourhood V of psi gives ||z|| <= C (sqrt||gamma2|| + ||mu - tau||) (since gamma2 = (lamPlus-lamMinus)^2);
   the right side is continuous at psi (gamma2, muSeq, tauN analytic on gkW) and vanishes there, so z psi = 0 and z -> 0 = z psi (squeeze).
   The sheet sign a is never used beyond G4-031. No analytic anchor; no Armstrong import. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G4032 (n a : ℤ) (ha : a = 1 ∨ a = -1)
    (ψ : PotPair) (hψ : ψ ∈ sourceBetaW)
    (hgap : gamma2 ψ n = 0) (hμ : muSeq ψ n = tauN ψ n) :
  cartesianZExtended n a ψ = 0 ∧ ContinuousAt (cartesianZExtended n a) ψ := by
  obtain ⟨V, hVn, hVS, C, hC, hbd⟩ := G4031 ψ hψ
  have hgkψ : ψ ∈ gkW := G4017Aux.sourceBetaW_gkW hψ
  have hnorm : ∀ φ ∈ V, ‖lamPlus φ n - lamMinus φ n‖ = Real.sqrt ‖gamma2 φ n‖ := by
    intro φ hφ
    have hgk : φ ∈ gkW := G4017Aux.sourceBetaW_gkW (hVS hφ)
    rw [gamma2_value38 φ hgk n, norm_pow, Real.sqrt_sq (norm_nonneg _)]
  have hγc : ContinuousAt (fun φ : PotPair => gamma2 φ n) ψ :=
    (gamma2_analytic n ψ hgkψ).continuousAt
  have hτc : ContinuousAt (fun φ : PotPair => tauN φ n) ψ :=
    (tauN_analytic n ψ hgkψ).continuousAt
  have hμc : ContinuousAt (fun φ : PotPair => muSeq φ n) ψ :=
    (analyticOnNhd_muSeq_complex38 n ψ hgkψ).continuousAt
  have hgc : ContinuousAt
      (fun φ : PotPair => C * (Real.sqrt ‖gamma2 φ n‖ + ‖muSeq φ n - tauN φ n‖)) ψ :=
    continuousAt_const.mul
      ((Real.continuous_sqrt.continuousAt.comp hγc.norm).add (hμc.sub hτc).norm)
  have hg0 : C * (Real.sqrt ‖gamma2 ψ n‖ + ‖muSeq ψ n - tauN ψ n‖) = 0 := by
    simp [hgap, hμ]
  have hle : ∀ φ ∈ V, ‖cartesianZExtended n a φ‖ ≤
      C * (Real.sqrt ‖gamma2 φ n‖ + ‖muSeq φ n - tauN φ n‖) := by
    intro φ hφ
    have := hbd φ hφ n a ha
    rwa [hnorm φ hφ] at this
  have hz0 : cartesianZExtended n a ψ = 0 :=
    norm_le_zero_iff.mp ((hle ψ (mem_of_mem_nhds hVn)).trans hg0.le)
  refine ⟨hz0, ?_⟩
  rw [ContinuousAt, hz0]
  refine squeeze_zero_norm' (Filter.mem_of_superset hVn fun φ hφ => hle φ hφ) ?_
  have := hgc.tendsto
  rwa [hg0] at this

end
end NlsGge.GKDefinitionDesign
