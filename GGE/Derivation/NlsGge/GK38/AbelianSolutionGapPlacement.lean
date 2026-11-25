import NlsGge.GK38.AbelianInputCompletion
import NlsGge.GK38.AbelianZeroGap

/-! Uncompiled next-P5 actual solution consequence. Original-disc placement is a
premise; CLOSED-gap placement is earned from actual Fn=0, including collapsed gaps. -/
set_option autoImplicit false
open Set Filter Topology Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p5Fn_zero_sigma_in_gap38 (n : ℤ) (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 (realSlice u) C R)
    (t : P2Space38 n) (ht : p2RealSeq38 n t)
    (hσ : ∀ m : P2Index38 n,
      Lib.sigmaOf (p2Extend38 n t) m.1 ∈ ball (C m.1) (R m.1))
    (hzero : p2Fn38 n (realSlice u,t)=0) :
    ∀ m : P2Index38 n, Lib.sigmaOf (p2Extend38 n t) m.1 ∈
      segment ℝ (lamMinus (realSlice u) m.1) (lamPlus (realSlice u) m.1) := by
  have hφ := realSlice_mem_gkW u
  have heReal : ∀ k : ℤ, (p2Extend38 n t k).im=0 := by
    intro k
    have hc : (countingCenter38 n).im=0 := by
      simp only [countingCenter38,Complex.mul_im,Complex.intCast_im,Complex.ofReal_im,
        zero_mul,mul_zero,add_zero]
    have he := p5Complete_real38 n (countingCenter38 n) hc t ht k
    simpa only [p5CompleteInput38,sub_self,lp.single_zero,add_zero] using he
  intro m
  have hcoord : p2Fn38 n (realSlice u,t) m=0 := by
    rw [hzero]
    rfl
  rw [p2Fn_apply38 n (realSlice u,t) hφ m] at hcoord
  have hw : (((n-m.1 : ℤ) : ℂ)) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr m.2.symm
  have hp : abelianPeriod38 m.1 (realSlice u)
      (p2FullNumerator38 n (p2Extend38 n t))=0 :=
    (mul_eq_zero.mp hcoord).resolve_left hw
  have hf := p2FullNumerator_entire38 n (p2Extend38 n t)
  have hfamily := abelianPeriod_fullfamily_realization38 (realSlice u) hφ
    (discC (realSlice u)) C (discR (realSlice u)) R
    (isolating_family38 (realSlice u) hφ) hfam m.1
    (p2FullNumerator38 n (p2Extend38 n t)) hf
  have hpC : circleIntegral
      (fun z => p2FullNumerator38 n (p2Extend38 n t) z/canonRoot38 (realSlice u) z)
      (C m.1) (R m.1)=0 := by
    rw [← hfamily.2.2]
    exact hp
  obtain ⟨x,hx,hfzero⟩ := p2Abelian_zero_in_gap38 m.1 n m.2 u C R hfam
    univ (p2FullNumerator38 n (p2Extend38 n t)) isOpen_univ convex_univ
    (subset_univ _) hf (fun x _ => p2FullNumerator_real38 n _ heReal x) hpC
  have hO : Lib.omitProd n (p2Extend38 n t) (x : ℂ)=0 := by
    change (-2 : ℂ)*Lib.omitProd n (p2Extend38 n t) (x : ℂ)=0 at hfzero
    exact (mul_eq_zero.mp hfzero).resolve_left (by norm_num)
  obtain ⟨r,hrn,hrx⟩ := (Lib.omitProd_eq_zero_iff n (p2Extend38 n t) (x : ℂ)).mp hO
  obtain ⟨c,N,hg,hsp⟩ := hfam
  have hxc : (x : ℂ) ∈ closedBall (C m.1) (R m.1) :=
    ball_subset_closedBall ((hsp.1 m.1).1 hx)
  have hrm : r=m.1 := by
    by_contra hne
    have hd := (p2OwnSigma_denominator38 C R c N hg r m.1 hne (p2Extend38 n t)
      (ball_subset_closedBall (hσ ⟨r,hrn⟩)) (x : ℂ) hxc).1
    exact hd (sub_eq_zero.mpr hrx)
  subst r
  rw [hrx]
  exact hx

end
end NlsGge.GK38
