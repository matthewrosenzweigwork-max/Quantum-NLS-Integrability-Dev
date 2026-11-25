import NlsGge.GK38.AbelianActualMovingGapCube

/-! Uncompiled omitted-coordinate realization. Fill the missing coordinate
with its ACTUAL lower endpoint, never the generally off-gap counting center. -/
set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

def p5FullRealInclude38 : lp (fun _ : ℤ => ℝ) 2 →L[ℝ] Lib.L2Seq :=
  lp.mapCLM 2 (fun _ : ℤ => Complex.ofRealCLM) zero_le_one
    (fun _ => by rw [Complex.ofRealCLM_norm])

def p5OmittedRealRestrict38 (n : ℤ) :
    lp (fun _ : ℤ => ℝ) 2 →L[ℝ] P3RealSpace38 n :=
  (p3RealPart38 n).comp (((p2Restrict38 n).restrictScalars ℝ).comp p5FullRealInclude38)

theorem p5OmittedRealRestrict_apply38 (n : ℤ) (t : lp (fun _ : ℤ => ℝ) 2)
    (m : P2Index38 n) : p5OmittedRealRestrict38 n t m=t m.1 := by
  change (p2Restrict38 n (p5FullRealInclude38 t) m).re=t m.1
  rw [p2Restrict_apply38]
  rfl

def p5RealCompleteAtGap38 (n : ℤ) (u : PhysicalL2) (t : P3RealSpace38 n) :
    lp (fun _ : ℤ => ℝ) 2 :=
  p5FullRealPart38 (p5CompleteInput38 n (actualGapLowerAllE02_38 u n : ℂ)
    (p3RealInclude38 n t))

theorem p5RealCompleteAtGap_self38 (n : ℤ) (u : PhysicalL2) (t : P3RealSpace38 n) :
    p5RealCompleteAtGap38 n u t n=actualGapLowerAllE02_38 u n-(n : ℝ)*Real.pi := by
  change (p5CompleteInput38 n (actualGapLowerAllE02_38 u n : ℂ)
    (p3RealInclude38 n t) n).re=_
  simp only [p5CompleteInput38,lp.coeFn_add,Pi.add_apply,p2Extend_self38,
    lp.single_apply_self,zero_add,Complex.sub_re,Complex.ofReal_re,
    countingCenter38,Complex.mul_re,Complex.intCast_re,Complex.intCast_im,
    Complex.ofReal_im,mul_zero,sub_zero]

theorem p5RealCompleteAtGap_other38 (n : ℤ) (u : PhysicalL2) (t : P3RealSpace38 n)
    (m : P2Index38 n) : p5RealCompleteAtGap38 n u t m.1=t m := by
  change (p5CompleteInput38 n (actualGapLowerAllE02_38 u n : ℂ)
    (p3RealInclude38 n t) m.1).re=_
  simp only [p5CompleteInput38,lp.coeFn_add,Pi.add_apply,
    lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 n _ m.2,add_zero]
  rw [p2Extend_at38 n (p3RealInclude38 n t) m,p3RealInclude_apply38,Complex.ofReal_re]

theorem p5RealCompleteAtGap_restrict38 (n : ℤ) (u : PhysicalL2) (t : P3RealSpace38 n) :
    p5OmittedRealRestrict38 n (p5RealCompleteAtGap38 n u t)=t := by
  apply Subtype.ext
  funext m
  rw [p5OmittedRealRestrict_apply38,p5RealCompleteAtGap_other38]

theorem p5RealCompleteAtGap_mem38 (n : ℤ) (u : PhysicalL2) (t : P3RealSpace38 n)
    (ht : t ∈ p5RealGapCube38 n u) :
    p5RealCompleteAtGap38 n u t ∈ p5FullRealGapCube38 u := by
  intro m
  by_cases hm : m=n
  · subst m
    rw [p5RealCompleteAtGap_self38]
    have he : countingCenter38 n+
        ((actualGapLowerAllE02_38 u n-(n : ℝ)*Real.pi : ℝ) : ℂ) =
        lamMinus (realSlice u) n := by
      rw [(lamPlus_real u n).2]
      dsimp only [countingCenter38]
      push_cast
      ring
    rw [he]
    exact left_mem_segment ℝ _ _
  · rw [p5RealCompleteAtGap_other38 n u t ⟨m,hm⟩]
    exact ht ⟨m,hm⟩

theorem p5Actual_omitted_gap_cube_subseq38 (n : ℤ) (u : ℕ → PhysicalL2)
    (u₀ : PhysicalL2) (hu : Tendsto u atTop (𝓝 u₀)) (t : ℕ → P3RealSpace38 n)
    (ht : ∀ k, t k ∈ p5RealGapCube38 n (u k)) :
    ∃ t₀ ∈ p5RealGapCube38 n u₀, ∃ s : ℕ → ℕ,
      StrictMono s ∧ Tendsto (t ∘ s) atTop (𝓝 t₀) := by
  let y : ℕ → lp (fun _ : ℤ => ℝ) 2 := fun k => p5RealCompleteAtGap38 n (u k) (t k)
  obtain ⟨y₀,hy₀,s,hs,hys⟩ := p5Actual_full_gap_cube_subseq38 u u₀ hu y
    (fun k => p5RealCompleteAtGap_mem38 n (u k) (t k) (ht k))
  refine ⟨p5OmittedRealRestrict38 n y₀,?_,s,hs,?_⟩
  · intro m
    rw [p5OmittedRealRestrict_apply38]
    exact hy₀ m.1
  · have hh := (p5OmittedRealRestrict38 n).continuous.continuousAt.tendsto.comp hys
    change Tendsto (fun k => p5OmittedRealRestrict38 n (y (s k))) atTop
      (𝓝 (p5OmittedRealRestrict38 n y₀)) at hh
    simpa only [y,p5RealCompleteAtGap_restrict38,Function.comp_def] using hh

end
end NlsGge.GK38
