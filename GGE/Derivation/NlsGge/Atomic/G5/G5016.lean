import Mathlib
import NlsGge.Atomic.G5.G5012Host
import NlsGge.Atomic.LIB.LIB075

/- G5-016 PRODUCTION02 (proof development; PRODUCTION01 used ContinuousLinearEquiv.restrictScalars, which is endomorphism-only in pinned Mathlib; the real equivalence is now built explicitly, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G5/G5016.lean.
   Head `G5016` verbatim from STATEMENTS/G5.md (followup12, "## G5-016"; round 14 retains the head). No lexical edits.
   Route (GK-17.3 p. 95, G5016_ROUTE.md): ContinuousLinearMap.IsInvertible f is by definition `∃ A : _ ≃L _, ↑A = f`.
   jacobianConjugate u = (reflectedFourierL2.symm, a continuous real-linear equivalence) o d_u Phi, so it is invertible iff
   d_u Phi is (Mathlib isInvertible_equiv_comp); jacobianAdjoint u is its adjoint, invertible iff it is (landed LIB-075
   adjoint_isInvertible_iff). The source's (d_0 Omega)^{-1} is hard-coded as reflectedFourierL2.symm in the approved
   jacobianConjugate body, so the G5-011 identification is not needed for this equivalence. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g5016_conjugate_eq (u : PhysicalL2) :
    jacobianConjugate u =
      (((({ toLinearEquiv := reflectedFourierL2.symm.toLinearEquiv.restrictScalars ℝ,
            continuous_toFun := reflectedFourierL2.symm.continuous,
            continuous_invFun := reflectedFourierL2.continuous } :
          Lib.L2Z ≃L[ℝ] PhysicalL2)) : Lib.L2Z →L[ℝ] PhysicalL2)).comp
        (fderiv ℝ physicalBirkhoff u) :=
  ContinuousLinearMap.ext fun _ => rfl

theorem g5016_isInvertible_iff (u : PhysicalL2) :
    (fderiv ℝ physicalBirkhoff u).IsInvertible ↔ (jacobianAdjoint u).IsInvertible := by
  have h1 : (jacobianAdjoint u).IsInvertible ↔ (jacobianConjugate u).IsInvertible :=
    NlsGge.Atomic.LIB.adjoint_isInvertible_iff (jacobianConjugate u)
  have h2 : (jacobianConjugate u).IsInvertible ↔ (fderiv ℝ physicalBirkhoff u).IsInvertible := by
    rw [g5016_conjugate_eq]
    exact ContinuousLinearMap.isInvertible_equiv_comp
  exact h2.symm.trans h1.symm

theorem G5016 (u : PhysicalL2) :
  (∃ e : PhysicalL2 ≃L[ℝ] Lib.L2Z,
    e.toContinuousLinearMap = fderiv ℝ physicalBirkhoff u) ↔
  (∃ e : PhysicalL2 ≃L[ℝ] PhysicalL2,
    e.toContinuousLinearMap = jacobianAdjoint u) :=
  g5016_isInvertible_iff u

end
end NlsGge.GKDefinitionDesign
