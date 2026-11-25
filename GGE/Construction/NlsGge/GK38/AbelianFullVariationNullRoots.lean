import NlsGge.GK38.AbelianFullVariationDecay
import NlsGge.GK38.AbelianVariationReality
import NlsGge.GK38.AbelianGapChoiceGeometry
import NlsGge.GK38.AbelianZeroGap
import NlsGge.GK38.Lib.InterpolationLemma

/-! Full-period nullity yields an actual closed-gap interpolation node at
EVERY signed index. Every node and little-o hypothesis is earned. -/
set_option autoImplicit false
open Set
open NlsGge.Pilot
namespace NlsGge.GK38.P6FullNumeratorVariation
noncomputable section

theorem fullVariation_circleIntegrable (m : ℤ) (φ : PotPair) (hφ : φ ∈ gkW)
    (s h : Lib.L2Seq) :
    CircleIntegrable (fun z => fullVariation s h z/canonRoot38 φ z)
      (discC φ m) (discR φ m) :=
  (abelianPeriod_fullfamily_realization38 φ hφ (discC φ) (discC φ)
    (discR φ) (discR φ) (isolating_family38 φ hφ) (isolating_family38 φ hφ)
    m (fullVariation s h) (fullVariation_entire s h)).1

theorem fullVariation_real (s h : Lib.L2Seq)
    (hs : ∀ k : ℤ, (s k).im=0) (hh : ∀ k : ℤ, (h k).im=0) (x : ℝ) :
    (fullVariation s h (x : ℂ)).im=0 := by
  have hnum := p2FullNumerator_real38 0 s hs x
  have hvar := P4NumeratorVariation.variation_real 0 s h hs hh x
  have hσ : (Lib.sigmaOf s 0-(x : ℂ)).im=0 := by
    simp only [Lib.sigmaOf,Int.cast_zero,zero_mul,zero_add,Complex.sub_im,hs 0,
      Complex.ofReal_im,sub_zero]
  rw [fullVariation_factor 0]
  simp only [Complex.div_im,Complex.add_im,Complex.mul_im,hh 0,hnum,hvar,hσ,
    Complex.ofReal_im,zero_mul,mul_zero,add_zero,sub_zero,zero_div]

theorem full_period_null_gap_roots (u : PhysicalL2) (s h : Lib.L2Seq)
    (hs : ∀ k : ℤ, (s k).im=0) (hh : ∀ k : ℤ, (h k).im=0)
    (hnull : ∀ m : ℤ, abelianPeriod38 m (realSlice u) (fullVariation s h)=0) :
    ∀ m : ℤ, ∃ x : ℝ,
      (x : ℂ) ∈ segment ℝ (lamMinus (realSlice u) m) (lamPlus (realSlice u) m) ∧
      fullVariation s h (x : ℂ)=0 := by
  intro m
  have _hi := fullVariation_circleIntegrable m (realSlice u) (realSlice_mem_gkW u) s h
  exact p2Abelian_zero_in_gap38 m (m+1) (by omega) u
    (discC (realSlice u)) (discR (realSlice u))
    (isolating_family38 (realSlice u) (realSlice_mem_gkW u)) univ
    (fullVariation s h) isOpen_univ convex_univ (subset_univ _)
    (fullVariation_entire s h) (fun x _ => fullVariation_real s h hs hh x) (hnull m)

theorem full_period_null_variation_zero (u : PhysicalL2) (s h : Lib.L2Seq)
    (hs : ∀ k : ℤ, (s k).im=0) (hh : ∀ k : ℤ, (h k).im=0)
    (hnull : ∀ m : ℤ, abelianPeriod38 m (realSlice u) (fullVariation s h)=0) :
    ∀ z : ℂ, fullVariation s h z=0 := by
  classical
  choose x hxgap hxzero using full_period_null_gap_roots u s h hs hh hnull
  let nodes : ℤ → ℂ := fun m => (x m : ℂ)
  have hsum : Summable (fun m : ℤ => ‖nodes m-(m : ℂ)*(Real.pi : ℂ)‖^2) := by
    simpa only [countingCenter38] using p5GapChoice_summable38 u nodes hxgap
  have hinj : Function.Injective nodes := p5GapChoice_injective38 u
    (discC (realSlice u)) (discR (realSlice u))
    (isolating_family38 (realSlice u) (realSlice_mem_gkW u)) nodes hxgap
  intro z
  have hd : Differentiable ℂ (fullVariation s h) :=
    fun w => (fullVariation_entire s h w (mem_univ _)).differentiableAt
  obtain ⟨_hprod,_hseries,he⟩ := Lib.interpolation_lemma hd
    (fullVariation_countingDecay s h) hsum hinj z
  simpa only [nodes,hxzero,zero_mul,tsum_zero] using he

end
end NlsGge.GK38.P6FullNumeratorVariation
