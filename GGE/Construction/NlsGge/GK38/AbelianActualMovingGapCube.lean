import NlsGge.GK38.AbelianFixedGapCube
import NlsGge.GK38.AbelianStrongGapEndpoints
import NlsGge.GK38.AbelianMovingLp2Box

/-! Uncompiled concrete moving-gap compactness. All strong endpoint and
generic compactness premises are realized by the ACTUAL spectral data. -/
set_option autoImplicit false
open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem p5RealGap_segment_iff38 (u : PhysicalL2) (m : ℤ) (q : ℝ) :
    countingCenter38 m+(q : ℂ) ∈
      segment ℝ (lamMinus (realSlice u) m) (lamPlus (realSlice u) m) ↔
    q ∈ Icc (actualGapLowerAllE02_38 u m-(m : ℝ)*Real.pi)
      (actualGapUpperAllE02_38 u m-(m : ℝ)*Real.pi) := by
  have horder : actualGapLowerAllE02_38 u m ≤ actualGapUpperAllE02_38 u m :=
    sub_nonneg.mp (p5RealGapWidth_nonneg38 u m)
  have himg := image_segment ℝ (Complex.ofRealCLM.toLinearMap.toAffineMap)
    (actualGapLowerAllE02_38 u m) (actualGapUpperAllE02_38 u m)
  change Complex.ofReal '' segment ℝ (actualGapLowerAllE02_38 u m)
      (actualGapUpperAllE02_38 u m) = segment ℝ
      (actualGapLowerAllE02_38 u m : ℂ) (actualGapUpperAllE02_38 u m : ℂ) at himg
  rw [(lamPlus_real u m).1,(lamPlus_real u m).2,← himg]
  constructor
  · rintro ⟨r,hr,he⟩
    have hre : r=(m : ℝ)*Real.pi+q := by
      have hh := congrArg Complex.re he
      simpa only [countingCenter38,Complex.ofReal_re,Complex.add_re,Complex.mul_re,
        Complex.intCast_re,Complex.ofReal_im,Complex.intCast_im,mul_zero,sub_zero] using hh
    rw [segment_eq_Icc horder] at hr
    constructor <;> linarith [hr.1,hr.2]
  · intro hq
    refine ⟨(m : ℝ)*Real.pi+q,?_,?_⟩
    · rw [segment_eq_Icc horder]
      constructor <;> linarith [hq.1,hq.2]
    · change (((m : ℝ)*Real.pi+q : ℝ) : ℂ)=(m : ℂ)*(Real.pi : ℂ)+(q : ℂ)
      push_cast
      rfl

theorem p5Actual_full_gap_cube_subseq38 (u : ℕ → PhysicalL2) (u₀ : PhysicalL2)
    (hu : Tendsto u atTop (𝓝 u₀)) (t : ℕ → lp (fun _ : ℤ => ℝ) 2)
    (ht : ∀ k, t k ∈ p5FullRealGapCube38 (u k)) :
    ∃ t₀ ∈ p5FullRealGapCube38 u₀, ∃ s : ℕ → ℕ,
      StrictMono s ∧ Tendsto (t ∘ s) atTop (𝓝 t₀) := by
  have ha := p5RealGapLowerShift_continuous38.continuousAt.tendsto.comp hu
  have hb := p5RealGapUpperShift_continuous38.continuousAt.tendsto.comp hu
  have h₀ (m : ℤ) : p5RealGapLowerShift38 u₀ m ≤ p5RealGapUpperShift38 u₀ m := by
    rw [p5RealGapLowerShift_value38,p5RealGapUpperShift_value38]
    have hh := p5RealGapWidth_nonneg38 u₀ m
    dsimp only [p5RealGapWidth38] at hh
    linarith
  have ht' (k : ℕ) (m : ℤ) : t k m ∈
      Icc (p5RealGapLowerShift38 (u k) m) (p5RealGapUpperShift38 (u k) m) := by
    rw [p5RealGapLowerShift_value38,p5RealGapUpperShift_value38]
    exact (p5RealGap_segment_iff38 (u k) m (t k m)).mp (ht k m)
  obtain ⟨t₀,ht₀,s,hs,hlim⟩ := p5MovingLp2OrderBox_subseq38 ℤ
    (fun k => p5RealGapLowerShift38 (u k)) (fun k => p5RealGapUpperShift38 (u k))
    (p5RealGapLowerShift38 u₀) (p5RealGapUpperShift38 u₀) ha hb h₀ t ht'
  refine ⟨t₀,?_,s,hs,hlim⟩
  intro m
  apply (p5RealGap_segment_iff38 u₀ m (t₀ m)).mpr
  have hm := ht₀ m
  rwa [p5RealGapLowerShift_value38,p5RealGapUpperShift_value38] at hm

end
end NlsGge.GK38
