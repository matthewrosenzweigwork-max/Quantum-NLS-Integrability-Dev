import Mathlib
import NlsGge.Atomic.PDE.PDE025
import NlsGge.NLS38.SolutionNotion38a
import NlsGge.NLS38.Persistence38a
import Mathlib.Analysis.InnerProductSpace.LinearMap

/- PDE round-4 host (proof development, AUTHOR; not reviewed). Bodies verbatim from PRO_DEFINITION_RESPONSE_FP80_04.md
   (PDE-027: HamiltonianCore38, hamiltonianBase, hamiltonianGradient0, hamiltonianDifferential, quartH1, quarticDifferential;
   PDE-032: massH1/hamH1 are ALREADY landed in NlsGge.Atomic.PDE.PDE025 with identical bodies, so imported not redefined;
   PDE-020: interaction, interactionDeriv). Target NlsGge/ThirdConsultation/PDE/Round4.lean.
   NOTE: `interaction` here is the PDE one; S host has its own, in namespace NlsGge.ThirdConsultation.S; never open both. -/
set_option autoImplicit false

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38
open Set Filter
open scoped InnerProductSpace ComplexConjugate BigOperators Topology

namespace NlsGge.ThirdConsultation.PDE
noncomputable section

abbrev HamiltonianCore38 : Type :=
  SobolevCarrier38 (((1 : ℕ) : ℝ) + 2)

def hamiltonianBase
    (x : HamiltonianCore38) : H1C38 :=
  carrierIncl38
    (show ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 2 by norm_num) x

def hamiltonianGradient0
    (x : HamiltonianCore38) : H0C38 :=
  incl01
    (J38 ((1 : ℕ) : ℝ) (lam ((1 : ℕ) : ℝ) x) +
      nonlinC 1 (show 1 ≤ (1 : ℕ) from le_rfl) (hamiltonianBase x))

def hamiltonianDifferential
    (x : HamiltonianCore38) : H1C38 →L[ℝ] ℝ :=
  (2 : ℝ) • ((innerSL ℝ (hamiltonianGradient0 x)).comp incl01)

def quartH1 (x : H1C38) : ℝ :=
  quart (carrierCoe38 ((1 : ℕ) : ℝ) x)

def quarticDifferential (x : H1C38) : H1C38 →L[ℝ] ℝ :=
  (4 : ℝ) • ((innerSL ℝ (convC38 x x)).comp (convC38 x))

def interaction
    (R : ℝ) (u : ℝ → ℤ → ℂ) (hu : IsCutSol R u)
    (t : ℝ) : H1C38 :=
  phaseC ((1 : ℕ) : ℝ) (-t)
    (carrierMk38 ((1 : ℕ) : ℝ) (u t) (hu.mem t))

def interactionDeriv
    (R : ℝ) (u : ℝ → ℤ → ℂ) (hu : IsCutSol R u)
    (t : ℝ) : H1C38 :=
  Gc 1 (show 1 ≤ (1 : ℕ) from le_rfl) R t (interaction R u hu t)

end
end NlsGge.ThirdConsultation.PDE
