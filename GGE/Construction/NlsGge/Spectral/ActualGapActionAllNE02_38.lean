import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38
import NlsGge.Spectral.ActualQuasimomentumMonotoneE02_38
set_option autoImplicit false
noncomputable section
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-! # NEW-E01 (v2 eq. F:eq:gapaction) for EVERY labelled gap, unconditional (campaign 38) -/

/-- `p = Re k(· + i0)` is nondecreasing, gaps are labelled by `p = nπ`, and for every rough
`u` and every `n ∈ ℤ`: `v ≥ √((x-λ_n^-)(λ_n^+-x))` on `g_n`. -/
theorem actualGapHeight_ge_semicircle_all_E02_38 (u : PhysicalL2) (n : ℤ) :
    ∀ x ∈ Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
      gapSemicircle (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) x ≤
        actualGapHeightE02_38 u x :=
  actualGapHeight_ge_semicircle_all_of_E02_38 u (monotone_actualQuasimomentumRealPartE02_38 u)
    (exists_const_near_gap_E02_38 u) (halfTrace_sq_ne_one_eventually_E02_38 u) n

/-- NEW-E01: `I_n ≥ |g_n|²/4` for every labelled gap `n ∈ ℤ`, closed gaps included, with the
exact `2/π` normalization `I_n = (2/π)∫_{g_n} v`. -/
theorem actualGapAction_ge_sq_div_four_all_E02_38 (u : PhysicalL2) (n : ℤ) :
    (actualGapUpperAllE02_38 u n - actualGapLowerAllE02_38 u n)^2 / 4 ≤
      actualGapActionAllE02_38 u n :=
  actualGapAction_ge_sq_div_four_all_of_E02_38 u (monotone_actualQuasimomentumRealPartE02_38 u)
    (exists_const_near_gap_E02_38 u) (halfTrace_sq_ne_one_eventually_E02_38 u) n

theorem actualGapLevelSet_eq_Icc_E02_38 (u : PhysicalL2) (n : ℤ) :
    (actualGapLevelSetE02_38 u n).Nonempty ∧
    actualGapLevelSetE02_38 u n =
      Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) :=
  actualGapLevelSet_eq_Icc_of_monotone_E02_38 u (monotone_actualQuasimomentumRealPartE02_38 u) n

theorem actualGapEndpoint_halfTrace_all_E02_38 (u : PhysicalL2) (n : ℤ) :
    actualPhysicalUnitHalfTrace32 u (actualGapLowerAllE02_38 u n : ℂ) =
        (Real.cos ((n:ℝ)*Real.pi) : ℂ) ∧
    actualPhysicalUnitHalfTrace32 u (actualGapUpperAllE02_38 u n : ℂ) =
        (Real.cos ((n:ℝ)*Real.pi) : ℂ) :=
  actualGapEndpoint_halfTrace_all_of_E02_38 u (monotone_actualQuasimomentumRealPartE02_38 u)
    (exists_const_near_gap_E02_38 u) n

/-- `-λ_n^±` (v2 labels of `L_u`) are sector-`n` eigenvalues of the reflected Dirac operator
`𝖫_u = -L_{-u}` (v2 F:eq:Dirac), realized as `actualSourcePerturbedDiracPMapAfterAE`. -/
theorem source_eigenvalue_neg_gapEndpoint_all_E02_38 (u : PhysicalL2) (n : ℤ) :
    (∃ X : TransportBridgeV4.recoveredActualSourceFreeWeightedDomain n, X.val ≠ 0 ∧
      actualSourcePerturbedDiracPMapAfterAE n u (star u) X =
        (-(actualGapLowerAllE02_38 u n : ℂ)) • X.val) ∧
    (∃ X : TransportBridgeV4.recoveredActualSourceFreeWeightedDomain n, X.val ≠ 0 ∧
      actualSourcePerturbedDiracPMapAfterAE n u (star u) X =
        (-(actualGapUpperAllE02_38 u n : ℂ)) • X.val) :=
  source_eigenvalue_neg_gapEndpoint_E02_38 u (monotone_actualQuasimomentumRealPartE02_38 u)
    (exists_const_near_gap_E02_38 u) n

end NlsGge.SpectralFoundations
end
