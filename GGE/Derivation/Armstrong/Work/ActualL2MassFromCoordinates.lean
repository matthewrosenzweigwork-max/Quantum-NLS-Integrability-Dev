import NlsGge.Spectral.ActualActionSumE02_38

/-!
# Conditional physical L2 mass from continuous Hilbert coordinates

SPECULATIVE_CONDITIONAL_HELPER: parent 696a52be, support sources pinned to
21a9b7c7. Actual Phi continuity and the pointwise actual action identity are
explicit future inputs. This module constructs neither input and closes no
actual mass, properness, inverse, or higher-level source node.

The genuine lp2 norm HasSum identifies norms on actual H1 Fourier truncations.
Strong density and continuity then extend that norm identity to every physical
L2 field. No action series is interchanged with a limit.
-/
set_option autoImplicit false
open Filter Topology
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem actualGapAction_hasSum_of_continuous_hilbert_coordinates38
    (Phi : PhysicalL2 → lp (fun _ : ℤ => ℂ) 2)
    (hPhi : Continuous Phi)
    (hAction : ∀ (u : PhysicalL2) (n : ℤ),
      ‖Phi u n‖ ^ 2 = actualGapActionAllE02_38 u n)
    (u : PhysicalL2) :
    HasSum (fun n : ℤ => actualGapActionAllE02_38 u n) (‖u‖ ^ 2) := by
  have hCoords (v : PhysicalL2) :
      HasSum (fun n : ℤ => actualGapActionAllE02_38 v n) (‖Phi v‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, hAction] using
      (lp.hasSum_norm (p := (2 : ENNReal)) (by norm_num) (Phi v))
  have hTruncNorm (N : ℕ) :
      ‖Phi (truncL2E02_38 u N)‖ ^ 2 = ‖truncL2E02_38 u N‖ ^ 2 :=
    (hCoords (truncL2E02_38 u N)).unique
      (actualGapAction_hasSum_E02_38 (truncL2E02_38 u N)
        (truncL2_sobolev_E02_38 u N))
  have hTrunc : Tendsto (fun N : ℕ => truncL2E02_38 u N) atTop (𝓝 u) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (tendsto_truncL2_E02_38 u)
  have hPhiNorm :
      Tendsto (fun N : ℕ => ‖Phi (truncL2E02_38 u N)‖ ^ 2) atTop
        (𝓝 (‖Phi u‖ ^ 2)) :=
    (((hPhi.tendsto u).comp hTrunc).norm).pow 2
  have hPhysicalNorm :
      Tendsto (fun N : ℕ => ‖Phi (truncL2E02_38 u N)‖ ^ 2) atTop
        (𝓝 (‖u‖ ^ 2)) := by
    simpa only [hTruncNorm] using hTrunc.norm.pow 2
  have hMassNorm : ‖Phi u‖ ^ 2 = ‖u‖ ^ 2 :=
    tendsto_nhds_unique hPhiNorm hPhysicalNorm
  simpa only [hMassNorm] using hCoords u

end
end NlsGge.GK38
