import NlsGge.GK38.AbelianRealJacobianUniform

/-! Uncompiled next-P5 input-chart bridge. Complete the omitted coordinate in the
SAME original isolating disc before applying the full-input P3 theorems. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

/-- `a` is the desired sigma_n, not the n-th sequence displacement. -/
def p5CompleteInput38 (n : ℤ) (a : ℂ) (t : P2Space38 n) : Lib.L2Seq :=
  p2Extend38 n t+lp.single 2 n (a-countingCenter38 n)

theorem p5Complete_restrict38 (n : ℤ) (a : ℂ) (t : P2Space38 n) :
    p2Restrict38 n (p5CompleteInput38 n a t)=t := by
  apply Subtype.ext
  funext m
  simp only [p2Restrict_apply38,p5CompleteInput38,lp.coeFn_add,Pi.add_apply,
    p2Extend_at38,lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 n (a-countingCenter38 n) m.2,
    add_zero]

theorem p5Complete_sigma_self38 (n : ℤ) (a : ℂ) (t : P2Space38 n) :
    Lib.sigmaOf (p5CompleteInput38 n a t) n=a := by
  simp only [Lib.sigmaOf,p5CompleteInput38,lp.coeFn_add,Pi.add_apply,p2Extend_self38,
    lp.single_apply_self,zero_add,countingCenter38]
  ring

theorem p5Complete_sigma_other38 (n : ℤ) (a : ℂ) (t : P2Space38 n)
    (m : P2Index38 n) :
    Lib.sigmaOf (p5CompleteInput38 n a t) m.1=
      Lib.sigmaOf (p2Extend38 n t) m.1 := by
  simp only [Lib.sigmaOf,p5CompleteInput38,lp.coeFn_add,Pi.add_apply,
    lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 n (a-countingCenter38 n) m.2,add_zero]

theorem p5Complete_real38 (n : ℤ) (a : ℂ) (ha : a.im=0) (t : P2Space38 n)
    (ht : p2RealSeq38 n t) : ∀ k : ℤ, (p5CompleteInput38 n a t k).im=0 := by
  intro k
  by_cases hk : k=n
  · subst k
    simp only [p5CompleteInput38,lp.coeFn_add,Pi.add_apply,p2Extend_self38,
      lp.single_apply_self,zero_add,countingCenter38,Complex.sub_im,Complex.mul_im,
      Complex.intCast_im,Complex.ofReal_im,zero_mul,mul_zero,add_zero,sub_zero,ha]
  · simp only [p5CompleteInput38,lp.coeFn_add,Pi.add_apply,
      lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 n (a-countingCenter38 n) hk,add_zero]
    rw [p2Extend_at38 n t ⟨k,hk⟩]
    exact ht ⟨k,hk⟩

theorem p5Complete_original_discs38 (n : ℤ) (t : P2Space38 n)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N)
    (ht : ∀ m : P2Index38 n,
      Lib.sigmaOf (p2Extend38 n t) m.1 ∈ ball (C m.1) (R m.1)) :
    ∀ k : ℤ, Lib.sigmaOf (p5CompleteInput38 n (C n) t) k ∈ ball (C k) (R k) := by
  intro k
  by_cases hk : k=n
  · subst k
    rw [p5Complete_sigma_self38]
    exact mem_ball_self (hg.1 n).1
  · rw [p5Complete_sigma_other38 n (C n) t ⟨k,hk⟩]
    exact ht ⟨k,hk⟩

end
end NlsGge.GK38
