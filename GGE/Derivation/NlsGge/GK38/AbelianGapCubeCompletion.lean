import NlsGge.GK38.AbelianFixedGapCube
import NlsGge.GK38.AbelianInputCompletion
import NlsGge.GK38.AbelianFullRealSpace

/-! UNCOMPILED genuine full-gap completion. Fill the omitted sigma at the
ACTUAL lower spectral endpoint before taking real coordinates. Every omitted
coordinate is retained exactly, including finite exceptional and collapsed gaps. -/
set_option autoImplicit false
open Set
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

def p6GapCubeComplete38 (n : ℤ) (u : PhysicalL2) (t : P3RealSpace38 n) :
    P6RealSpace38 :=
  p6RealPart38 (p5CompleteInput38 n (lamMinus (realSlice u) n)
    (p3RealInclude38 n t))

theorem p6GapCubeComplete_include38 (n : ℤ) (u : PhysicalL2)
    (t : P3RealSpace38 n) :
    p6RealInclude38 (p6GapCubeComplete38 n u t)=
      p5CompleteInput38 n (lamMinus (realSlice u) n) (p3RealInclude38 n t) := by
  have ha : (lamMinus (realSlice u) n).im=0 := by
    rw [(lamPlus_real u n).2]
    exact Complex.ofReal_im _
  have ht : p2RealSeq38 n (p3RealInclude38 n t) := by
    intro m
    exact Complex.ofReal_im (t m)
  exact p6RealInclude_realPart38 _ (p5Complete_real38 n _ ha _ ht)

theorem p6GapCubeComplete_restrict38 (n : ℤ) (u : PhysicalL2)
    (t : P3RealSpace38 n) :
    p2Restrict38 n (p6RealInclude38 (p6GapCubeComplete38 n u t))=
      p3RealInclude38 n t := by
  rw [p6GapCubeComplete_include38,p5Complete_restrict38]

theorem p6GapCubeComplete_mem38 (n : ℤ) (u : PhysicalL2)
    (t : P3RealSpace38 n) (ht : t ∈ p5RealGapCube38 n u) :
    p6GapCubeComplete38 n u t ∈ p5FullRealGapCube38 u := by
  intro m
  change Lib.sigmaOf (p6RealInclude38 (p6GapCubeComplete38 n u t)) m ∈
    segment ℝ (lamMinus (realSlice u) m) (lamPlus (realSlice u) m)
  rw [p6GapCubeComplete_include38]
  by_cases hm : m=n
  · subst m
    rw [p5Complete_sigma_self38]
    exact left_mem_segment ℝ _ _
  · rw [p5Complete_sigma_other38 n (lamMinus (realSlice u) n)
      (p3RealInclude38 n t) ⟨m,hm⟩]
    change countingCenter38 m+
      (p2Extend38 n (p3RealInclude38 n t)) (⟨m,hm⟩ : P2Index38 n).val ∈
        segment ℝ (lamMinus (realSlice u) m) (lamPlus (realSlice u) m)
    rw [p2Extend_at38,p3RealInclude_apply38]
    exact ht ⟨m,hm⟩

theorem p6RealGapCube_lifts_to_full38 (n : ℤ) (u : PhysicalL2)
    (t : P3RealSpace38 n) (ht : t ∈ p5RealGapCube38 n u) :
    ∃ s ∈ p5FullRealGapCube38 u,
      p2Restrict38 n (p6RealInclude38 s)=p3RealInclude38 n t ∧
      Lib.sigmaOf (p6RealInclude38 s) n=lamMinus (realSlice u) n := by
  refine ⟨p6GapCubeComplete38 n u t,p6GapCubeComplete_mem38 n u t ht,
    p6GapCubeComplete_restrict38 n u t,?_⟩
  rw [p6GapCubeComplete_include38,p5Complete_sigma_self38]

end
end NlsGge.GK38
