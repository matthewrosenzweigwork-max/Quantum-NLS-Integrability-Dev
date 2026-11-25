import NlsGge.GK38.AbelianFixedGapCube

/-! Uncompiled source-Omega chart bridge. Near an actual closed-gap point,
real Fn zeros stay in actual closed gaps by SAME original-family persistence
and earned zero-gap placement. No local inverse or gap-branch oracle. -/
set_option autoImplicit false
open Set Filter Topology Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p5Near_real_zero_in_actual_gaps38 (n : ℤ) (u₀ : PhysicalL2)
    (t₀ : P3RealSpace38 n) (ht₀ : t₀ ∈ p5RealGapCube38 n u₀) :
    ∃ W : Set (PhysicalL2 × P3RealSpace38 n), W ∈ 𝓝 (u₀,t₀) ∧
      ∀ p ∈ W, p3RealFn38 n p.1 p.2=0 → p.2 ∈ p5RealGapCube38 n p.1 := by
  let C : ℤ → ℂ := discC (realSlice u₀)
  let R : ℤ → ℝ := discR (realSlice u₀)
  have hfam₀ : IsolatingFamily38 (realSlice u₀) C R :=
    isolating_family38 (realSlice u₀) (realSlice_mem_gkW u₀)
  obtain ⟨c,N,hg,hsp⟩ := hfam₀
  let A : P3RealSpace38 n → Lib.L2Seq :=
    fun t => p5CompleteInput38 n (C n) (p3RealInclude38 n t)
  have hA : Continuous A :=
    ((p2Extend38 n).continuous.comp (p3RealInclude38 n).continuous).add continuous_const
  have hbase : ∀ m : ℤ, Lib.sigmaOf (A t₀) m ∈ ball (C m) (R m) := by
    apply p5Complete_original_discs38 n (p3RealInclude38 n t₀) C R c N hg
    intro m
    have hm := (hsp.1 m.1).1 (ht₀ m)
    simpa only [Lib.sigmaOf,p2Extend_at38,p3RealInclude_apply38,countingCenter38] using hm
  obtain ⟨U,hU,_hUW,V,hV,c',N',_hg',hfam,hσ⟩ :=
    P3JacobianColumns.original_family_neighborhoods (realSlice u₀) (realSlice_mem_gkW u₀)
      (A t₀) C R ⟨c,N,hg,hsp⟩ hbase
  let W : Set (PhysicalL2 × P3RealSpace38 n) :=
    {p | realSlice p.1 ∈ U ∧ A p.2 ∈ V}
  have hWU : {p : PhysicalL2 × P3RealSpace38 n | realSlice p.1 ∈ U} ∈ 𝓝 (u₀,t₀) :=
    (continuous_realSlice.continuousAt.comp continuousAt_fst).preimage_mem_nhds hU
  have hWV : {p : PhysicalL2 × P3RealSpace38 n | A p.2 ∈ V} ∈ 𝓝 (u₀,t₀) :=
    (hA.continuousAt.comp continuousAt_snd).preimage_mem_nhds hV
  refine ⟨W,inter_mem hWU hWV,?_⟩
  intro p hp hzero
  have hcomplex : p2Fn38 n (realSlice p.1,p3RealInclude38 n p.2)=0 := by
    rw [← p3RealFn_graph38,hzero,map_zero]
  have hown (m : P2Index38 n) :
      Lib.sigmaOf (p2Extend38 n (p3RealInclude38 n p.2)) m.1 ∈ ball (C m.1) (R m.1) := by
    rw [← p5Complete_sigma_other38 n (C n) (p3RealInclude38 n p.2) m]
    exact hσ (A p.2) hp.2 m.1
  have hgap := p5Fn_zero_sigma_in_gap38 n p.1 C R (hfam (realSlice p.1) hp.1)
    (p3RealInclude38 n p.2) (fun m => by simp only [p3RealInclude_apply38,Complex.ofReal_im])
    hown hcomplex
  intro m
  simpa only [Lib.sigmaOf,p2Extend_at38,p3RealInclude_apply38,countingCenter38] using hgap m

end
end NlsGge.GK38
