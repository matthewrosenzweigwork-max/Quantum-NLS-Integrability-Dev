import NlsGge.GK38.AngleRatioSpectralPartialAnalytic
import NlsGge.GK38.AngleRatioSpectralDerivativeMajorant

/-! Source-only all-row actual spectral-derivative square majorant on cuts.
Actual far-disc Cauchy and finite ORIGINAL scalar-disc compact bounds are
combined before real tsums; no fixed-openball vanishing tail is assumed. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem angleOmittedRatio_spectral_deriv_all_cut_l2_majorant38
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) (s₀ : Lib.L2Seq) :
    ∃ U : Set PotPair, U ∈ nhds φ₀ ∧ U ⊆ gkW ∧
      ∃ V : Set Lib.L2Seq, V ∈ nhds s₀ ∧ ∃ B : ℝ, 0 ≤ B ∧
        ∀ φ ∈ U, ∀ s ∈ V, ∃ b : ℤ → ℝ,
          (∀ m, 0 ≤ b m) ∧ Summable (fun m : ℤ => b m^2) ∧
          (∑' m : ℤ, b m^2) ≤ B ∧
          ∀ m : ℤ, ∀ z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
            DifferentiableAt ℂ (fun w => p2OmittedRatio38 m ((φ,s),w)) z ∧
            ‖deriv (fun w => p2OmittedRatio38 m ((φ,s),w)) z‖ ≤ b m := by
  classical
  obtain ⟨Ut,hUt,hUtW,Vt,hVt,Nt,Bt,hBt,ht⟩ :=
    angleOmittedRatio_spectral_derivative_l2_majorant38 φ₀ hφ₀ s₀
  obtain ⟨Uc,hUc,_hUcW,Nc,hcut⟩ :=
    a5OwnCut_uniform_ball38 φ₀ hφ₀ (Real.pi/8) (by positivity)
  obtain ⟨Ug,hUg,_hUgW,_hUgo,_hUgc,C,R,c,Ng,hgeom,hspec⟩ :=
    local_isolatingFamily_common38 φ₀ hφ₀
  let N : ℕ := max Nt Nc
  let S : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have hfam₀ : IsolatingFamily38 φ₀ C R :=
    ⟨c,Ng,hgeom,hspec φ₀ (mem_of_mem_nhds hUg)⟩
  obtain ⟨ε,hε,H,hH,hhead⟩ :=
    angleOmittedRatio_finite_spectral_deriv_bound38 φ₀ hφ₀ s₀ C R hfam₀ S
  let f : ℤ → ℝ := fun m => if m ∈ S then H else 0
  have hf0 (m : ℤ) : 0 ≤ f m := by dsimp only [f]; split_ifs <;> positivity
  have hfs : Summable (fun m : ℤ => f m^2) :=
    summable_of_ne_finset_zero (s := S)
      (fun m hm => by simp only [f,ite_eq_right hm,zero_pow (by norm_num : (2 : ℕ) ≠ 0)])
  have hfmass : (∑' m : ℤ, f m^2)=(S.card : ℝ)*H^2 := by
    rw [tsum_eq_sum (s := S)
      (fun m hm => by simp only [f,ite_eq_right hm,zero_pow (by norm_num : (2 : ℕ) ≠ 0)])]
    calc
      (∑ m ∈ S, f m^2) = ∑ _m ∈ S, H^2 := by
        apply Finset.sum_congr rfl
        intro m hm
        simp only [f,ite_eq_left hm]
      _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]
  let U := Ut ∩ (Uc ∩ (Ug ∩ ball φ₀ ε))
  let V := Vt ∩ ball s₀ ε
  refine ⟨U,inter_mem hUt (inter_mem hUc (inter_mem hUg (ball_mem_nhds _ hε))),
    fun φ hφ => hUtW hφ.1,V,inter_mem hVt (ball_mem_nhds _ hε),
    2*Bt+2*((S.card : ℝ)*H^2),by positivity,?_⟩
  intro φ hφ s hs
  obtain ⟨a,ha0,has,haB,ha⟩ := ht φ hφ.1 s hs.1
  have hdom : Summable (fun m : ℤ => 2*a m^2+2*f m^2) :=
    (has.mul_left 2).add (hfs.mul_left 2)
  have hsq (m : ℤ) : (a m+f m)^2 ≤ 2*a m^2+2*f m^2 := by
    nlinarith [sq_nonneg (a m-f m)]
  have hsum : Summable (fun m : ℤ => (a m+f m)^2) :=
    hdom.of_nonneg_of_le (fun _ => sq_nonneg _) hsq
  refine ⟨fun m => a m+f m,fun m => add_nonneg (ha0 m) (hf0 m),hsum,?_,?_⟩
  · apply (hsum.tsum_le_tsum hsq hdom).trans
    rw [(has.mul_left 2).tsum_add (hfs.mul_left 2),tsum_mul_left,tsum_mul_left,hfmass]
    exact add_le_add (mul_le_mul_of_nonneg_left haB (by norm_num)) le_rfl
  · intro m z hz
    have hzOwn : z ∈ closedBall (C m) (R m) :=
      ball_subset_closedBall (((hspec φ hφ.2.2.1).1 m).1 hz)
    have hdiff : DifferentiableAt ℂ (fun w => p2OmittedRatio38 m ((φ,s),w)) z :=
      (p2OmittedRatio_own_disc_analytic38 m φ (hUtW hφ.1) C R
        ⟨c,Ng,hgeom,hspec φ hφ.2.2.1⟩ s z hzOwn).differentiableAt
    refine ⟨hdiff,?_⟩
    by_cases hmS : m ∈ S
    · have hp : (φ,s) ∈ ball (φ₀,s₀) ε := by
        rw [mem_ball,Prod.dist_eq]
        exact max_lt (mem_ball.mp hφ.2.2.2) (mem_ball.mp hs.2)
      have hh := hhead (φ,s) hp m hmS z hzOwn
      simpa only [f,ite_eq_left hmS] using hh.trans (le_add_of_nonneg_left (ha0 m))
    · have hm : (N : ℤ) < |m| := by
        apply lt_of_not_ge
        intro hm
        exact hmS (Finset.mem_Icc.mpr (abs_le.mp hm))
      have hmt : (Nt : ℤ) < |m| := by have he := le_max_left Nt Nc; omega
      have hmc : (Nc : ℤ) < |m| := by have he := le_max_right Nt Nc; omega
      have hh := (ha m hmt z (hcut φ hφ.2.1 m hmc hz)).2
      simpa only [f,ite_eq_right hmS,add_zero] using hh

end
end NlsGge.GK38
