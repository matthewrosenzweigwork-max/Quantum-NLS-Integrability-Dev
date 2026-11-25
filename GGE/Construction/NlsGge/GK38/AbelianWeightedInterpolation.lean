import NlsGge.GK38.AbelianFullWeightedDecay
import NlsGge.GK38.AbelianNullGapRoots
import NlsGge.GK38.Lib.InterpolationLemma

/-! Corrected book14.7 interpolation: genuine o(1) is earned before applying
the accepted interpolation lemma. The missing node may be an actual endpoint;
no exceptional n-th isolating disc is assumed to contain n*pi. -/
set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38.P4NumeratorVariation
noncomputable section

theorem countingDecay_of_circle_norm_le {f g : ℂ → ℂ} (B : ℝ) (hB : 0 < B)
    (hfg : ∀ m : ℕ, ∀ z : ℂ, ‖z‖=m*Real.pi+Real.pi/2 → ‖f z‖ ≤ B*‖g z‖)
    (hg : countingDecay g) : countingDecay f := by
  intro ε hε
  obtain ⟨N,hN⟩ := hg (ε/B) (div_pos hε hB)
  refine ⟨N,?_⟩
  intro m hm z hz
  calc
    _ ≤ B*‖g z‖ := hfg m z hz
    _ ≤ B*((ε/B)*‖Complex.sin z‖) := mul_le_mul_of_nonneg_left (hN m hm z hz) hB.le
    _ = ε*‖Complex.sin z‖ := by field_simp

theorem variation_extend_arbitrary_weight_decay (n : ℤ) (s h : P2Space38 n) (a : ℂ) :
    countingDecay (fun z => p4NumeratorVariation38 n (p2Extend38 n s)
      (p2Extend38 n h) z*(a-z)) := by
  let q : Lib.L2Seq := lp.single 2 n (a-(n : ℂ)*(Real.pi : ℂ))
  have hq : Lib.sigmaOf q n=a := by
    simp only [Lib.sigmaOf,q,lp.single_apply_self]
    ring
  obtain ⟨B,hB,hbound⟩ := sigma_counting_norm_ratio n q
  have hbase := variation_full_weighted_countingDecay n (p2Extend38 n s) (p2Extend38 n h)
  apply countingDecay_of_circle_norm_le B hB ?_ hbase
  intro m z hz
  rw [norm_mul,norm_mul]
  have hσ : Lib.sigmaOf (p2Extend38 n s) n=(n : ℂ)*(Real.pi : ℂ) := by
    simp only [Lib.sigmaOf,p2Extend_self38,add_zero]
  rw [hσ,norm_sub_rev ((n : ℂ)*(Real.pi : ℂ)) z]
  have hb := hbound m z hz
  rw [hq] at hb
  calc
    _ ≤ ‖p4NumeratorVariation38 n (p2Extend38 n s) (p2Extend38 n h) z‖*
        (B*‖z-(n : ℂ)*(Real.pi : ℂ)‖) := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := by ring

theorem entire_zero_of_weighted_interpolation (f : ℂ → ℂ) (a : ℂ)
    (hf : AnalyticOnNhd ℂ f univ) (hdecay : countingDecay (fun z => f z*(a-z)))
    (σ : ℤ → ℂ) (hσ : Summable (fun m : ℤ => ‖σ m-(m : ℂ)*(Real.pi : ℂ)‖^2))
    (hinj : Function.Injective σ) (hz : ∀ m : ℤ, f (σ m)*(a-σ m)=0) :
    ∀ z : ℂ, f z=0 := by
  have hw : ∀ z : ℂ, f z*(a-z)=0 := by
    intro z
    have ha : Differentiable ℂ (fun z => f z*(a-z)) := by
      intro w
      exact ((hf w (mem_univ _)).mul (analyticAt_const.sub analyticAt_id)).differentiableAt
    obtain ⟨_hprod,_hseries,he⟩ := Lib.interpolation_lemma ha hdecay hσ hinj z
    simpa only [hz,zero_mul,tsum_zero] using he
  have hfa : f a=0 := by
    have hd := ((hf a (mem_univ _)).differentiableAt.hasDerivAt).mul
      ((hasDerivAt_const a a).sub (hasDerivAt_id a))
    change HasDerivAt (fun z : ℂ => f z*(a-z))
      (deriv f a*(a-a)+f a*(0-1)) a at hd
    have hd' : HasDerivAt (fun z => f z*(a-z)) (-f a) a := by
      simpa only [sub_self,mul_zero,zero_add,zero_sub,mul_neg,mul_one] using hd
    have hfun : (fun z => f z*(a-z))=fun _ => (0 : ℂ) := funext hw
    rw [hfun] at hd'
    exact neg_eq_zero.mp (hd'.unique (hasDerivAt_const a 0))
  intro z
  by_cases hza : z=a
  · simpa only [hza] using hfa
  · exact (mul_eq_zero.mp (hw z)).resolve_right (sub_ne_zero.mpr (Ne.symm hza))

theorem null_variation_zero_of_gap_nodes (n : ℤ) (s h : P2Space38 n) (x : ℤ → ℂ)
    (hxsum : Summable (fun m : ℤ => ‖x m-(m : ℂ)*(Real.pi : ℂ)‖^2))
    (hxinj : Function.Injective x)
    (hxzero : ∀ m : ℤ, m ≠ n →
      p4NumeratorVariation38 n (p2Extend38 n s) (p2Extend38 n h) (x m)=0) :
    ∀ z : ℂ, p4NumeratorVariation38 n (p2Extend38 n s) (p2Extend38 n h) z=0 := by
  apply entire_zero_of_weighted_interpolation
    (p4NumeratorVariation38 n (p2Extend38 n s) (p2Extend38 n h)) (x n)
    (variation_entire n _ _) (variation_extend_arbitrary_weight_decay n s h (x n))
    x hxsum hxinj
  intro m
  by_cases hm : m=n
  · subst m
    rw [sub_self,mul_zero]
  · rw [hxzero m hm,zero_mul]

end
end NlsGge.GK38.P4NumeratorVariation
