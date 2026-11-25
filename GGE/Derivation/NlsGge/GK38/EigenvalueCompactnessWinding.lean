import NlsGge.GK38.EigenvalueCompactnessHomotopyContinuity
import NlsGge.GK38.EigenvalueCompactnessPhaseConnected
import NlsGge.GK38.EigenvalueCompactnessPhaseActualProbe
import NlsGge.GK38.MolnarLocalizationProbe

/-! # S7: full integer winding at both actual endpoints

The selected direction need not be continuous: its singleton phase is continuous.
-/
set_option autoImplicit false
open Set Topology
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem periodicEndpoint_zero38 (n : ℤ) (upper : Bool) :
    periodicEndpoint38 0 n upper = (n : ℝ) * Real.pi := by
  cases upper
  · exact (gap_zero38 n).1
  · exact (gap_zero38 n).2

theorem periodicEndpointPhase_free38 (n : ℤ) (upper : Bool) :
    periodicEndpointPhase38 0 n upper = (n : ℝ) * Real.pi := by
  unfold periodicEndpointPhase38
  rw [periodicEndpoint_zero38]
  exact periodicPhase_free_one38 _ _ (periodicEndpointDirection_spec38 0 n upper).1

theorem periodicEndpointPhase_value38 (u : PhysicalL2) (n : ℤ) (upper : Bool) :
    periodicEndpointPhase38 u n upper = (n : ℝ) * Real.pi := by
  let : PreconnectedSpace Time38 := Subtype.preconnectedSpace isPreconnected_Icc
  have hz : ∀ t : Time38, ∃ m : ℤ,
      periodicEndpointPhase38 ((t : ℝ) • u) n upper = (m : ℝ) * Real.pi := by
    intro t
    obtain ⟨m, hm, _⟩ := periodicPhase_discrete38 _ _ n _
      (periodicEndpointDirection_spec38 ((t : ℝ) • u) n upper)
    exact ⟨m, hm⟩
  have he := continuous_halfturn_constant38 (univ : Set Time38) isPreconnected_univ
    (fun t : Time38 => periodicEndpointPhase38 ((t : ℝ) • u) n upper)
    (periodicEndpointPhase_path_continuous38 u n upper).continuousOn
    (fun t _ => hz t) (a := ⟨1, zero_le_one, le_rfl⟩) (b := ⟨0, le_rfl, zero_le_one⟩)
    (mem_univ _) (mem_univ _)
  simpa only [one_smul, zero_smul, periodicEndpointPhase_free38] using he

theorem periodicPhase_winding38 (u : PhysicalL2) (n : ℤ) (x : ℝ) (a : ℂ)
    (hx : EndpointAt38 u n x) (ha : EigenDirectionAt38 u x n a) :
    periodicPhase38 u x a 1 = (n : ℝ) * Real.pi := by
  rcases hx with hx | hx
  · subst x
    exact (periodicPhase_direction_independent38 u _ n a
      (periodicEndpointDirection38 u n false) ha (periodicEndpointDirection_spec38 u n false)).trans
      (periodicEndpointPhase_value38 u n false)
  · subst x
    exact (periodicPhase_direction_independent38 u _ n a
      (periodicEndpointDirection38 u n true) ha (periodicEndpointDirection_spec38 u n true)).trans
      (periodicEndpointPhase_value38 u n true)

end
end NlsGge.GK38
