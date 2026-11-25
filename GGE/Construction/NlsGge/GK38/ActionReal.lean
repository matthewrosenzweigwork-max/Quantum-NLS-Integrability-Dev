import NlsGge.GK38.ActionRealBridge
import NlsGge.GK38.ActionRealScalar
import NlsGge.GK38.ActionPlaneReal

set_option autoImplicit false
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.AblowitzLadik
namespace NlsGge.GK38
noncomputable section

def ActionRealBridge38 : Prop :=
  ∀ (u : PhysicalL2) (n : ℤ),
    gkActionC38 (realSlice u) n = (actualGapActionAllE02_38 u n : ℂ)

def ActionNonnegative38 : Prop :=
  ∀ (u : PhysicalL2) (n : ℤ), 0 ≤ actualGapActionAllE02_38 u n

def ActionZeroIffClosed38 : Prop :=
  ∀ (u : PhysicalL2) (n : ℤ),
    actualGapActionAllE02_38 u n = 0 ↔
      actualGapLowerAllE02_38 u n = actualGapUpperAllE02_38 u n

def ActionPositiveIffOpen38 : Prop :=
  ∀ (u : PhysicalL2) (n : ℤ),
    0 < actualGapActionAllE02_38 u n ↔
      actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n

def PlaneWaveActionProbe38 : Prop :=
  ∀ (N : ℕ) (k : ℤ), k.natAbs ≤ N → ∀ (t : ℝ) (n : ℤ),
    actualGapActionAllE02_38 (planeL2 N (planeWaveCoeff38 N k t)) n =
      if n = -k then t ^ 2 else 0

def PlaneWaveContourProbe38 : Prop :=
  ∀ (N : ℕ) (k : ℤ), k.natAbs ≤ N → ∀ (t : ℝ) (n : ℤ),
    gkActionC38 (realSlice (planeL2 N (planeWaveCoeff38 N k t))) n =
      if n = -k then ((t ^ 2 : ℝ) : ℂ) else 0

def PlaneWaveOpenEndpoints38 : Prop :=
  ∀ (N : ℕ) (k : ℤ), k.natAbs ≤ N → ∀ t : ℝ,
    actualGapLowerAllE02_38 (planeL2 N (planeWaveCoeff38 N k t)) (-k) =
        -Real.pi * (k : ℝ) - |t| ∧
    actualGapUpperAllE02_38 (planeL2 N (planeWaveCoeff38 N k t)) (-k) =
        -Real.pi * (k : ℝ) + |t|

theorem action_real_bridge38 : ActionRealBridge38 := NlsGge.GK38.ActionRealBridge.action_real_bridge

theorem action_nonnegative38 : ActionNonnegative38 := NlsGge.GK38.actionNonnegative38

theorem action_zero_iff_closed38 : ActionZeroIffClosed38 := NlsGge.GK38.actionZeroIffClosed38

theorem action_positive_iff_open38 : ActionPositiveIffOpen38 := NlsGge.GK38.actionPositiveIffOpen38

theorem plane_wave_action_probe38 : PlaneWaveActionProbe38 := NlsGge.GK38.planeWaveActionProbe38

theorem plane_wave_contour_probe38 : PlaneWaveContourProbe38 := by
  intro N k hk t n
  rw [NlsGge.GK38.ActionRealBridge.action_real_bridge, NlsGge.GK38.planeWaveActionProbe38 N k hk t n]
  split_ifs <;> rfl

theorem plane_wave_open_endpoints38 : PlaneWaveOpenEndpoints38 := NlsGge.GK38.planeWaveOpenEndpoints38

end
end NlsGge.GK38
