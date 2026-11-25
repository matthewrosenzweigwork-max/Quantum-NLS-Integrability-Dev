import NlsGge.GK38.GradEigenRealPeriodicGradient
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.GradEigen38
noncomputable section

def RealPeriodicGradientTarget : Prop :=
  ∀ (u : PhysicalL2) (n : ℤ) (upper : Bool),
    actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n →
    ∃ a : PairVec38,
      a ≠ 0 ∧ a 1 = star (a 0) ∧
      Matrix.mulVec (monodromyPair (realSlice u) (endpoint u n upper : ℂ)) a = parity n • a ∧
      realSymmetric (state (realSlice u) (endpoint u n upper : ℂ) a) ∧
      0 < energy (state (realSlice u) (endpoint u n upper : ℂ) a) ∧
      HasFDerivAt (fun v : PhysicalL2 => endpoint v n upper)
        (realEnergyGradient (state (realSlice u) (endpoint u n upper : ℂ) a)) u ∧
      ∃ U : Set PhysicalL2, IsOpen U ∧ u ∈ U ∧
        AnalyticOnNhd ℝ (fun v : PhysicalL2 => endpoint v n upper) U ∧
        ∀ v ∈ U, actualGapLowerAllE02_38 v n < actualGapUpperAllE02_38 v n

theorem real_periodic_gradient_target : RealPeriodicGradientTarget := by
  intro u n upper hgap
  have htrace : monodromyPair (realSlice u) (endpoint u n upper : ℂ) 0 0+
      monodromyPair (realSlice u) (endpoint u n upper : ℂ) 1 1=2*parity n := by
    simpa only [discrim_eq] using endpoint_discrim_value u n upper
  have hex := periodic_eigenvector_exists _ (parity n) (parity_square n)
    (monodromy_det_scalar _ _) htrace
  obtain ⟨a,ha,hasym,he⟩ := real_symmetric_eigenvector_exists _ (parity n)
    (monodromyPair_real_entry_star38 u (endpoint u n upper)) (parity_star n) hex
  refine ⟨a,ha,hasym,he,real_state_symmetry u (endpoint u n upper) a hasym,
    state_energy_positive _ _ a ha,actual_endpoint_hasFDerivAt u n upper hgap a ha hasym he,?_
    ⟩
  let U : Set PhysicalL2 := {v | actualGapLowerAllE02_38 v n<actualGapUpperAllE02_38 v n}
  have hU : IsOpen U := isOpen_lt (gapEndpoints_L2_continuous38 n).1
    (gapEndpoints_L2_continuous38 n).2
  exact ⟨U,hU,hgap,fun v hv => analyticAt_endpoint v n upper hv,fun _ hv => hv⟩

end
end NlsGge.GK38.GradEigen38
