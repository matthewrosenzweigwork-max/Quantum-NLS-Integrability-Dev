import NlsGge.GK38.GradEigenClosedMonodromy
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.GradEigen38
noncomputable section

theorem probe_free_closed_characterizations (n : ℤ) :
    (0 : PhysicalL2) ∈ Z n ∧
    monodromyPair (realSlice 0) (gkMu 0 n : ℂ)=parity n • (1 : PairMat38) ∧
    closedEquations n 0=0 := by
  have hc : (0 : PhysicalL2) ∈ Z n := (gap_zero38 n).1.trans (gap_zero38 n).2.symm
  exact ⟨hc,(closed_monodromy_target 0 n).mp hc,(closed_zero_set_target 0 n).mp hc⟩

theorem probe_nonfree_negative_closed_characterizations :
    constL2 1 ∈ Z (-1) ∧
    monodromyPair (realSlice (constL2 1)) (gkMu (constL2 1) (-1) : ℂ)=
      -(1 : PairMat38) ∧ closedEquations (-1) (constL2 1)=0 := by
  have hc : constL2 1 ∈ Z (-1) :=
    realType_probe_nonfree_negative38.2.1.trans realType_probe_nonfree_negative38.2.2.1.symm
  refine ⟨hc,?_,(closed_zero_set_target _ _).mp hc⟩
  simpa [parity] using (closed_monodromy_target _ _).mp hc

theorem probe_phased_negative_closed_characterizations :
    constL2 Complex.I ∈ Z (-1) ∧
    monodromyPair (realSlice (constL2 Complex.I)) (gkMu (constL2 Complex.I) (-1) : ℂ)=
      -(1 : PairMat38) ∧ closedEquations (-1) (constL2 Complex.I)=0 := by
  have he := unit_constant_gap_endpoints Complex.I (by simp [Complex.I_sq]) (-1)
  have hc : constL2 Complex.I ∈ Z (-1) := he.1.trans
    (realType_probe_nonfree_negative38.2.1.trans (realType_probe_nonfree_negative38.2.2.1.symm.trans he.2.symm))
  refine ⟨hc,?_,(closed_zero_set_target _ _).mp hc⟩
  simpa [parity] using (closed_monodromy_target _ _).mp hc

theorem probe_nonfree_open_rejects_closed :
    constL2 1 ∉ Z 0 ∧
    monodromyPair (realSlice (constL2 1)) (gkMu (constL2 1) 0 : ℂ) 0 1 ≠ 0 ∧
    closedEquations 0 (constL2 1) ≠ 0 := by
  have hn : constL2 1 ∉ Z 0 := ne_of_lt realType_probe_nonfree_open_gap38
  exact ⟨hn,fun h => hn ((closed_offdiagonal_target _ _).mpr h),
    fun h => hn ((closed_zero_set_target _ _).mpr h)⟩

end
end NlsGge.GK38.GradEigen38
