import Mathlib
import NlsGge.ThirdConsultation.M.MRound11Host
import NlsGge.ThirdConsultation.M.MRound11Elim
import NlsGge.Atomic.KST.KST012
import NlsGge.Atomic.KST.KST013

/-!
# M-024: native small-square equivalence of the proper-domain eigenproblem and the 2x2 determinant
(proof development, AUTHOR; not self-reviewed)

Head: Pro round 11 (`PRO_DEFINITION_RESPONSE_FP80_11.md` section 5.2, commit c7aa9978), printed verbatim.
Route (Pro 5.3, Molnar Lemma 7): elimination `u = P f`, `g = V f`, `v = D g`, `g = (1-T)^{-1} V u` under the
ambient small-square hypothesis, reconstruction `f = u + D (1-T)^{-1} V u` in the actual proper domain of
`KST013.dirac` with parity-`n` Fourier support, and kernel of the frame matrix = determinant zero.
No M-025 / equal-diagonal hypothesis; no N0 cutoff.

VISIBILITY DEPENDENCY: the four landed lemmas below are `private` in KST012/KST013 and must be made
public (visibility only; statements and proofs unchanged) before this file compiles:
  NlsGge.Atomic.KST013.stage13AC_actual_proper_operator_graph_iff
  NlsGge.Atomic.KST013.stage13G_projection_zero_forces_zero
  NlsGge.Atomic.KST013.stage13K_actual_forward_reduced_formula
  NlsGge.Atomic.KST012.stageD_reconstructed_actual_bridges
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M

theorem eigenvalue_iff_schur_det_zero
    (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hsmall :
      ‖NlsGge.ThirdConsultation.MTwoMode.ambientT φ n lam hlam ^ 2‖ ≤
        (1 / 2 : ℝ)) :
    NlsGge.ThirdConsultation.MTwoMode.PeriodicEigenvalue φ n lam ↔
      Matrix.det
        (NlsGge.ThirdConsultation.MTwoMode.schurMatrix φ n lam hlam) = 0 :=
  NlsGge.ThirdConsultation.MTwoModeSupp.periodicEigenvalue_iff_det_core
    NlsGge.Atomic.KST013.stage13AC_actual_proper_operator_graph_iff
    NlsGge.Atomic.KST013.stage13G_projection_zero_forces_zero
    NlsGge.Atomic.KST013.stage13K_actual_forward_reduced_formula
    NlsGge.Atomic.KST012.stageD_reconstructed_actual_bridges
    φ n lam hlam hsmall

end NlsGge.ThirdConsultation.M

end
