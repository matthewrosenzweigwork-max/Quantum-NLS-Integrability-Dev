import Mathlib
import NlsGge.Atomic.AL.AL077
import NlsGge.Atomic.AL.AL078
import NlsGge.Atomic.F.F010Host
import NlsGge.Atomic.F.F014
import NlsGge.Atomic.F.F015
import NlsGge.Atomic.X.X009Generic
import NlsGge.Atomic.X.X009Bridge

/- AL-079 production candidate by codex_luna03; not independently reviewed or accepted.
   Target: NlsGge/Atomic/AL/AL079.lean.
   Head is verbatim from followup13 STATEMENTS/AL.md §AL-079.
   Route: specialize L06_08b_38 at the same concrete PDE Birkhoff/smoothing pair;
   reuse X009Aux.finiteNormalizer_eq_ZM and finiteGapLaw_eq_muM to identify F's
   finite hierarchy objects. The generic conditional theorem remains in X009Generic. -/
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Atomic.Common
open NlsGge.AblowitzLadik NlsGge.HierarchyRiccati.Core

namespace NlsGge.ThirdConsultation.AL

theorem al079
    {β₀ β₁ β₂ : ℝ} (h0 : 0 < β₀) (h1 : 0 < β₁) (h2 : 0 < β₂) (s : ℝ) :
    (((gammaM38 2 (alQ4Beta38 β₀ β₁ β₂)).map reflect38).map
        (seqRealization38 (sobolevModeWeight s)) =
      (gammaM38 2 (alQ4Beta38 β₀ β₁ β₂)).map
        (seqRealization38 (sobolevModeWeight s))) ∧
    (∀ u : Hm1 2, Vm38 2 (alQ4Beta38 β₀ β₁ β₂) u =
      alV2_38 β₁ β₂ (reSob38 ((2 - 1 : ℕ) : ℝ) 1 u)) ∧
    NlsGge.ThirdConsultation.F.finiteNormalizer 2 (alQ4Beta38 β₀ β₁ β₂) = alQ4Z2_38 β₀ β₁ β₂ ∧
    (NlsGge.ThirdConsultation.F.finiteGapLaw 2 (alQ4Beta38 β₀ β₁ β₂)).map
        (reSob38 ((2 - 1 : ℕ) : ℝ) s) = alQ4Rho38 s β₀ β₁ β₂ := by
  obtain ⟨hReflect, hPotential, hZM, hLaw⟩ :=
    NlsGge.Birkhoff.L06_08b_38
      NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38
      NlsGge.ThirdConsultation.PDE.actualOneSmoothingInput38 h0 h1 h2 s
  refine ⟨hReflect, hPotential,
    (NlsGge.Atomic.X009.X009Aux.finiteNormalizer_eq_ZM h0 h1 h2).trans hZM, ?_⟩
  rw [NlsGge.Atomic.X009.X009Aux.finiteGapLaw_eq_muM h0 h1 h2]
  exact hLaw

end NlsGge.ThirdConsultation.AL
