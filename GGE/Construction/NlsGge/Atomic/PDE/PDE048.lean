import Mathlib
import NlsGge.NLS38.PhaseGroup38
import NlsGge.Birkhoff.S01Translation38
import NlsGge.Atomic.G1.G1062

set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.NLS38 NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.PDE
noncomputable section
-- STATEMENTS/PDE.md:559 verbatim; reuse NlsGge.Birkhoff.fourierSeq38_translate38 (S01Translation38.lean:149)
theorem reflectedFourier_translation (u : PhysicalL2) (t : ℝ) : fourierSeq38 (translateL2_38 t u)=rotSeq38 (-(2*Real.pi*t)) (fourierSeq38 u) :=
  NlsGge.Birkhoff.fourierSeq38_translate38 t u

end
end NlsGge.ThirdConsultation.PDE

