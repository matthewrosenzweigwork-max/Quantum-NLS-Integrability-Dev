import NlsGge.GK38.AbelianHilbert

/-! Actual entire psi numerators from omitted normalized roots. All off-index
period conditions follow from the actual Hilbert zero; the missing period's
2*pi normalization remains a separate contour/asymptotic theorem. -/
set_option autoImplicit false
open Set
namespace NlsGge.GK38
noncomputable section

def p6PsiNumerator38 (n : ℤ) (F : PotPair → P2Space38 n) (φ : PotPair) (z : ℂ) : ℂ :=
  p2Numerator38 n (F φ) z

theorem p6PsiNumerator_joint_analytic38 (n : ℤ) (W : Set PotPair)
    (F : PotPair → P2Space38 n) (hF : AnalyticOnNhd ℂ F W) :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => p6PsiNumerator38 n F p.1 p.2)
      (W ×ˢ (univ : Set ℂ)) := by
  intro p hp
  have hroot : AnalyticAt ℂ (fun q : PotPair × ℂ => F q.1) p :=
    (hF p.1 hp.1).comp analyticAt_fst
  have hfull : AnalyticAt ℂ
      (fun q : PotPair × ℂ => p2Extend38 n (F q.1)) p :=
    AnalyticAt.comp (g := p2Extend38 n) (f := fun q : PotPair × ℂ => F q.1)
      ((p2Extend38 n).analyticAt (F p.1)) hroot
  exact AnalyticAt.comp
    (g := fun q : ℂ × Lib.L2Seq => p2FullNumerator38 n q.2 q.1)
    (f := fun q : PotPair × ℂ => (q.2,p2Extend38 n (F q.1)))
    (p2FullNumerator_joint_analytic38 n _ (mem_univ _))
    (analyticAt_snd.prod hfull)

theorem p6PsiNumerator_entire38 (n : ℤ) (F : PotPair → P2Space38 n) (φ : PotPair) :
    AnalyticOnNhd ℂ (p6PsiNumerator38 n F φ) univ :=
  p2FullNumerator_entire38 n (p2Extend38 n (F φ))

theorem p6PsiNumerator_integrable_and_off_diagonal_periods38
    (n : ℤ) (φ : PotPair) (hφ : φ ∈ gkW) (F : PotPair → P2Space38 n)
    (hzero : p2Fn38 n (φ,F φ)=0) :
    (∀ m : ℤ, CircleIntegrable (fun z => p6PsiNumerator38 n F φ z/canonRoot38 φ z)
      (discC φ m) (discR φ m)) ∧
      ∀ m : ℤ, n ≠ m → abelianPeriod38 m φ (p6PsiNumerator38 n F φ)=0 := by
  refine ⟨fun m => p2Period_integrable38 m n φ hφ (p2Extend38 n (F φ)),?_⟩
  intro m hnm
  let k : P2Index38 n := ⟨m,Ne.symm hnm⟩
  have h := congrArg (fun x : P2Space38 n => x k) hzero
  rw [p2Fn_apply38 n (φ,F φ) hφ k] at h
  change (((n-m : ℤ) : ℂ))*abelianPeriod38 m φ (p6PsiNumerator38 n F φ)=0 at h
  have hw : (((n-m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hnm
  exact (mul_eq_zero.mp h).resolve_left hw

end
end NlsGge.GK38
