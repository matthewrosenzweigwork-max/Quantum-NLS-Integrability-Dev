import NlsGge.GK38.AbelianPeriodVariation
import NlsGge.GK38.AbelianVariationReality
import NlsGge.GK38.AbelianZeroGap

/-! A genuine null direction of the actual Fn produces real closed-gap roots
of its entire numerator variation. This is the root step in book Lemma14.7. -/
set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38.P4NumeratorVariation
noncomputable section

theorem extend_real (n : ℤ) (s : P2Space38 n) (hs : p2RealSeq38 n s) :
    ∀ k : ℤ, (p2Extend38 n s k).im=0 := by
  intro k
  by_cases hk : k=n
  · subst k
    rw [p2Extend_self38]
    rfl
  · change (p2RawExtend38 n s k).im=0
    simp only [p2RawExtend38,dite_eq_right hk]
    exact hs ⟨k,hk⟩

theorem fn_direction_period (n : ℤ) (φ : PotPair) (hφ : φ ∈ gkW)
    (s h : P2Space38 n) (m : P2Index38 n) :
    (fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (φ,t)) s) h m =
      (((n-m.1 : ℤ) : ℂ))*abelianPeriod38 m.1 φ
        (p4NumeratorVariation38 n (p2Extend38 n s) (p2Extend38 n h)) := by
  have hp := (period_hasDerivAt n m.1 φ hφ (p2Extend38 n s)
    (p2Extend38 n h)).const_mul (((n-m.1 : ℤ) : ℂ))
  have heq : (fun t : ℂ => p2Fn38 n (φ,s+t • h) m) =
      (fun t : ℂ => (((n-m.1 : ℤ) : ℂ))*abelianPeriod38 m.1 φ
        (p2FullNumerator38 n (p2Extend38 n s+t • p2Extend38 n h))) := by
    funext t
    apply (p2Fn_apply38 n (φ,s+t • h) hφ m).trans
    change (((n-m.1 : ℤ) : ℂ))*abelianPeriod38 m.1 φ
      (p2FullNumerator38 n (p2Extend38 n (s+t • h))) = _
    rw [map_add,map_smul]
  rw [← heq] at hp
  have ha : AnalyticAt ℂ (fun t : P2Space38 n => p2Fn38 n (φ,t)) s :=
    AnalyticAt.comp (g := p2Fn38 n) (f := fun t : P2Space38 n => (φ,t))
      (p2Fn_analytic38 n (φ,s) ⟨hφ,mem_univ _⟩) (analyticAt_const.prod analyticAt_id)
  have hline : HasDerivAt (fun t : ℂ => s+t • h) h 0 := by
    simpa only [one_smul] using! (((hasDerivAt_id (0 : ℂ)).smul_const h).const_add s)
  have hd := ha.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  let E : P2Space38 n →L[ℂ] ℂ := lp.evalCLM ℂ (fun _ : P2Index38 n => ℂ) 2 m
  have hc := E.hasFDerivAt.comp_hasDerivAt (0 : ℂ) hd
  have hc' : HasDerivAt (fun t : ℂ => p2Fn38 n (φ,s+t • h) m)
      ((fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (φ,t)) s) h m) 0 := hc
  exact hc'.unique hp

theorem null_direction_gap_roots (n : ℤ) (u : PhysicalL2) (s h : P2Space38 n)
    (hs : p2RealSeq38 n s) (hh : p2RealSeq38 n h)
    (hnull : (fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (realSlice u,t)) s) h=0) :
    ∀ m : P2Index38 n, ∃ x : ℝ,
      (x : ℂ) ∈ segment ℝ (lamMinus (realSlice u) m.1) (lamPlus (realSlice u) m.1) ∧
      p4NumeratorVariation38 n (p2Extend38 n s) (p2Extend38 n h) (x : ℂ)=0 := by
  intro m
  have hφ := realSlice_mem_gkW u
  have _hi := variation_circleIntegrable n m.1 (realSlice u) hφ
    (p2Extend38 n s) (p2Extend38 n h)
  have hp := fn_direction_period n (realSlice u) hφ s h m
  rw [hnull] at hp
  have hw : (((n-m.1 : ℤ) : ℂ)) ≠ 0 := by
    exact_mod_cast (sub_ne_zero.mpr (Ne.symm m.2))
  have hz : abelianPeriod38 m.1 (realSlice u)
      (p4NumeratorVariation38 n (p2Extend38 n s) (p2Extend38 n h))=0 :=
    (mul_eq_zero.mp hp.symm).resolve_left hw
  exact p2Abelian_zero_in_gap38 m.1 n m.2 u (discC (realSlice u)) (discR (realSlice u))
    (isolating_family38 (realSlice u) hφ) univ
    (p4NumeratorVariation38 n (p2Extend38 n s) (p2Extend38 n h)) isOpen_univ
    convex_univ (subset_univ _) (variation_entire n _ _)
    (fun x _ => variation_real n _ _ (extend_real n s hs) (extend_real n h hh) x) hz

end
end NlsGge.GK38.P4NumeratorVariation
