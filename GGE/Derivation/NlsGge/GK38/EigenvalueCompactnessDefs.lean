import NlsGge.GK38.RealTypeSpectrum
import NlsGge.GK38.PairCompact
import NlsGge.Spectral.ActualPhysicalFloquetCurrentPrimitive33V3

/-! # S7: actual normalized real directions and clockwise phase data

GK I.7 Proposition 7.3. The phase candidate uses the existing actual flow.
-/
set_option autoImplicit false
open Filter Topology Set Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

abbrev Time38 := Icc (0 : ℝ) 1

def realInitial38 (a : ℂ) : Fin 2 → ℂ := ![a, star a]

def normalizedFirst38 (u : PhysicalL2) (x : ℝ) (a : ℂ) (t : Time38) : ℂ :=
  ((fundPair (realSlice u) (x : ℂ) t).mulVec (realInitial38 a) 0) / a

def periodicPhase38 (u : PhysicalL2) (x : ℝ) (a : ℂ) (s : ℝ) : ℝ := x * s -
  ∫ r in (0 : ℝ)..s, (e02Pot38 u r *
    (actualPhysicalFloquetState33 u (x : ℂ) (realInitial38 a) r 1 /
      actualPhysicalFloquetState33 u (x : ℂ) (realInitial38 a) r 0)).re

def EndpointAt38 (u : PhysicalL2) (n : ℤ) (x : ℝ) : Prop :=
  x = actualGapLowerAllE02_38 u n ∨ x = actualGapUpperAllE02_38 u n

def EigenDirectionAt38 (u : PhysicalL2) (x : ℝ) (n : ℤ) (a : ℂ) : Prop :=
  ‖a‖ = 1 ∧ (monodromyPair (realSlice u) (x : ℂ)).mulVec (realInitial38 a) =
    (Real.cos ((n : ℝ) * Real.pi) : ℂ) • realInitial38 a

def NormalizedPhase38 (g : Time38 → ℂ) (θ : Time38 → ℝ) : Prop :=
  Continuous g ∧ Continuous θ ∧ θ ⟨0, le_rfl, zero_le_one⟩ = 0 ∧
    ∀ t : Time38, g t ≠ 0 ∧ g t / (‖g t‖ : ℂ) = Complex.exp (-Complex.I * (θ t : ℂ))

end
end NlsGge.GK38
