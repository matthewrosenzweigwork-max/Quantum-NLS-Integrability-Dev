import NlsGge.GK38.AbelianFixedGapCube

/-! Uncompiled explicit original-family completed-chart equivalence. This
does NOT identify the source domain with a zero-extension slice. The omitted
coordinate is existentially completed INSIDE its original supplied disc. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p5Actual_gap_zero_iff_original_full_chart38 (n : ℤ) (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 (realSlice u) C R)
    (t : P3RealSpace38 n) :
    (t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t=0) ↔
      ∃ s : Lib.L2Seq, (∀ k : ℤ, (s k).im=0) ∧
        p2Restrict38 n s=p3RealInclude38 n t ∧
        (∀ k : ℤ, Lib.sigmaOf s k ∈ ball (C k) (R k)) ∧
        p2Fn38 n (realSlice u,p2Restrict38 n s)=0 := by
  constructor
  · rintro ⟨ht,hzero⟩
    obtain ⟨c,N,hg,hsp⟩ := hfam
    let s : Lib.L2Seq := p5CompleteInput38 n (C n) (p3RealInclude38 n t)
    have hown (m : P2Index38 n) :
        Lib.sigmaOf (p2Extend38 n (p3RealInclude38 n t)) m.1 ∈ ball (C m.1) (R m.1) := by
      have hm := (hsp.1 m.1).1 (ht m)
      simpa only [Lib.sigmaOf,p2Extend_at38,p3RealInclude_apply38,countingCenter38] using hm
    refine ⟨s,p5Complete_real38 n (C n) (hg.1 n).2 (p3RealInclude38 n t)
      (fun m => by simp only [p3RealInclude_apply38,Complex.ofReal_im]),
      p5Complete_restrict38 n (C n) (p3RealInclude38 n t),
      p5Complete_original_discs38 n (p3RealInclude38 n t) C R c N hg hown,?_⟩
    change p2Fn38 n (realSlice u,p2Restrict38 n (p5CompleteInput38 n (C n)
      (p3RealInclude38 n t)))=0
    rw [p5Complete_restrict38,← p3RealFn_graph38,hzero,map_zero]
  · rintro ⟨s,_hsreal,hrestrict,hown,hzero⟩
    have hzero' : p2Fn38 n (realSlice u,p3RealInclude38 n t)=0 := by
      simpa only [hrestrict] using hzero
    have hown' (m : P2Index38 n) :
        Lib.sigmaOf (p2Extend38 n (p3RealInclude38 n t)) m.1 ∈ ball (C m.1) (R m.1) := by
      have he : s m.1=(t m : ℂ) := by
        have hh := congrArg (fun q : P2Space38 n => q m) hrestrict
        simpa only [p2Restrict_apply38,p3RealInclude_apply38] using hh
      have hm := hown m.1
      simpa only [Lib.sigmaOf,p2Extend_at38,p3RealInclude_apply38,he] using hm
    have hgap := p5Fn_zero_sigma_in_gap38 n u C R hfam (p3RealInclude38 n t)
      (fun m => by simp only [p3RealInclude_apply38,Complex.ofReal_im]) hown' hzero'
    constructor
    · intro m
      simpa only [Lib.sigmaOf,p2Extend_at38,p3RealInclude_apply38,countingCenter38] using hgap m
    · apply (p3RealInclude38 n).injective
      rw [p3RealFn_graph38,map_zero]
      exact hzero'

end
end NlsGge.GK38
