import NlsGge.Hierarchy.ALMoments38
import NlsGge.Hierarchy.ALFullEnergy38

/-! Integrator bridge: the moment `alMomentK38` of `ALFullEnergy38` (L02a) and `alK38` of
`ALMoments38` (L01) are the same definition of `D:eq:Kj`. -/

namespace NlsGge.AblowitzLadik

theorem alMomentK38_eq_alK38 {L : ℕ} [NeZero L] (α : ZMod L → ℂ) (j : ℕ) :
    alMomentK38 α j = alK38 α j := rfl

end NlsGge.AblowitzLadik
