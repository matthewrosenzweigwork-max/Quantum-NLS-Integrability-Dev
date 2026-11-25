import NlsGge.GK38.EigenvalueCompactnessDirections

/-! # S7: pointwise eigen-directions for both existing endpoint branches

These choices are never asserted to vary continuously.
-/
set_option autoImplicit false
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

def periodicEndpoint38 (u : PhysicalL2) (n : ℤ) (upper : Bool) : ℝ :=
  if upper then actualGapUpperAllE02_38 u n else actualGapLowerAllE02_38 u n

theorem periodicEndpoint_at38 (u : PhysicalL2) (n : ℤ) (upper : Bool) :
    EndpointAt38 u n (periodicEndpoint38 u n upper) := by
  cases upper
  · exact Or.inl rfl
  · exact Or.inr rfl

def periodicEndpointDirection38 (u : PhysicalL2) (n : ℤ) (upper : Bool) : ℂ :=
  Classical.choose (periodic_eigen_direction_exists38 u n (periodicEndpoint38 u n upper)
    (periodicEndpoint_at38 u n upper))

theorem periodicEndpointDirection_spec38 (u : PhysicalL2) (n : ℤ) (upper : Bool) :
    EigenDirectionAt38 u (periodicEndpoint38 u n upper) n (periodicEndpointDirection38 u n upper) :=
  Classical.choose_spec (periodic_eigen_direction_exists38 u n (periodicEndpoint38 u n upper)
    (periodicEndpoint_at38 u n upper))

def periodicEndpointPhase38 (u : PhysicalL2) (n : ℤ) (upper : Bool) : ℝ :=
  periodicPhase38 u (periodicEndpoint38 u n upper) (periodicEndpointDirection38 u n upper) 1

end
end NlsGge.GK38
