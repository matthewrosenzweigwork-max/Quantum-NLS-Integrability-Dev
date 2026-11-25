import NlsGge.GK38.GradEigenClosedRank
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.GradEigen38
noncomputable section

theorem isClosed_Z (n : ℤ) : IsClosed (Z n) := by
  have hl : Continuous (fun u : PhysicalL2 => actualGapLowerAllE02_38 u n) := by
    simpa only [endpoint,Bool.false_eq_true,ite_false] using endpoint_continuous n false
  have hu : Continuous (fun u : PhysicalL2 => actualGapUpperAllE02_38 u n) := by
    simpa only [endpoint,ite_true] using endpoint_continuous n true
  exact isClosed_eq hl hu

theorem interior_Z_empty (n : ℤ) : interior (Z n)=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro u hu
  have hc : u ∈ Z n := interior_subset hu
  have hnhd : Z n ∈ 𝓝 u := mem_interior_iff_mem_nhds.mp hu
  have heq : closedEquations n =ᶠ[𝓝 u] fun _ : PhysicalL2 => (0 : Normal) := by
    filter_upwards [hnhd] with v hv
    exact (closed_zero_set_target v n).mp hv
  have hd : closedDerivative n u=0 := by
    change fderiv ℝ (closedEquations n) u=0
    rw [heq.fderiv_eq]
    simp
  have hs := closed_submersion_target u n hc
  rw [hd] at hs
  obtain ⟨v,hv⟩ := hs (1,0)
  have hz := congrArg Prod.fst hv
  norm_num at hz

def ClosedNowhereDenseTarget : Prop :=
  ∀ n : ℤ, IsClosed (Z n) ∧ interior (closure (Z n))=∅ ∧
    IsOpen ((Z n)ᶜ) ∧ Dense ((Z n)ᶜ)

theorem closed_nowhere_dense_target : ClosedNowhereDenseTarget := by
  intro n
  have hc := isClosed_Z n
  have hi := interior_Z_empty n
  refine ⟨hc,?_,hc.isOpen_compl,interior_eq_empty_iff_dense_compl.mp hi⟩
  rw [hc.closure_eq]
  exact hi

theorem all_gaps_open_eq_iInter :
    {u : PhysicalL2 | ∀ n : ℤ, actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n}=
      ⋂ n : ℤ, (Z n)ᶜ := by
  ext u
  simp only [mem_setOf_eq,mem_iInter,mem_compl_iff,Z]
  constructor
  · intro h n
    exact ne_of_lt (h n)
  · intro h n
    exact lt_of_le_of_ne (gap_endpoint_levels38 u n).1 (h n)

def AllGapsGenericTarget : Prop :=
  Dense {u : PhysicalL2 | ∀ n : ℤ,
    actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n}

theorem all_gaps_generic_target : AllGapsGenericTarget := by
  unfold AllGapsGenericTarget
  rw [all_gaps_open_eq_iInter]
  exact dense_iInter_of_isOpen (fun n => (closed_nowhere_dense_target n).2.2.1)
    (fun n => (closed_nowhere_dense_target n).2.2.2)

end
end NlsGge.GK38.GradEigen38
