import NlsGge.GK38.XiSqKernelMonotonicity

set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.GK38
noncomputable section

/-- Actual centered boundary errors have a genuine uniform full square-summable tail majorant.
The boundary root-domain hypothesis is geometric and will be discharged by the actual radial contour. -/
theorem a5CenteredKernel_circle_l2_majorant38 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧ ∃ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ φ ∈ U, ∃ b : ℤ → ℝ, (∀ n, 0 ≤ b n) ∧
        Summable (fun n : ℤ => b n^2) ∧ (∑' n : ℤ, b n^2) ≤ M ∧
        ∀ n : ℤ, (N:ℤ) < |n| → ∀ z ∈ sphere ((n:ℂ)*(Real.pi:ℂ)) (Real.pi/8),
          (φ,z) ∈ rootDomain38 →
          ‖a5CenteredKernel38 n (φ,z)-(-1/(8*Complex.I*((n:ℂ)*(Real.pi:ℂ)-z)))‖ ≤ b n := by
  let d : ℝ := Real.pi/16
  let r : ℝ := Real.pi/8
  have hd : 0 < d := by dsimp [d]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  obtain ⟨Uc,hUc,hUcW,Nc,Bc,hBc,hχ⟩ := a5Chi_Dn_l2_majorant38 φ₀ hφ₀
  obtain ⟨Ut,hUt,_hUtW,Nt,ht⟩ := a5Tau_uniform_tail38 φ₀ hφ₀ (min d (1/2)) (lt_min hd (by norm_num))
  obtain ⟨Us,hUs,_hUsW,Ns,hs⟩ := critical_uniform_tail38 φ₀ hφ₀ (1/2) (by norm_num)
  obtain ⟨Ug,hUg,_hUgW,Ng,hg⟩ := a5Gamma2_uniform_tail38 φ₀ hφ₀ (2*d^2) (by positivity)
  obtain ⟨Uv,hUv,_hUvW,Bt,hBt,hvals⟩ := tauGamma_common_value_bound38 discC discR
    isolating_selectors_admissible38 φ₀ hφ₀
  obtain ⟨Uh,hUh,Bs,hBs,hσ⟩ := critical_l2 φ₀
  obtain ⟨Uw,hUw,Bg,hγ⟩ := a5Gamma2_l2_38 φ₀ hφ₀
  let U := Uc ∩ (Ut ∩ (Us ∩ (Ug ∩ (Uv ∩ (Uh ∩ Uw)))))
  let N := max Nc (max Nt (max Ns Ng))
  have hN (n : ℤ) (hn : (N:ℤ) < |n|) :
      (Nc:ℤ) < |n| ∧ (Nt:ℤ) < |n| ∧ (Ns:ℤ) < |n| ∧ (Ng:ℤ) < |n| := by
    have hc : Nc ≤ N := le_max_left _ _
    have ht : Nt ≤ N := (le_max_left Nt _).trans (le_max_right _ _)
    have hs : Ns ≤ N := ((le_max_left Ns Ng).trans (le_max_right Nt _)).trans (le_max_right _ _)
    have hg : Ng ≤ N := ((le_max_right Ns Ng).trans (le_max_right Nt _)).trans (le_max_right _ _)
    omega
  let A : ℝ := (1/(8*d))*(4*(1+1/d))
  let B : ℝ := (1/(8*d))*(8*(1+1/d)/(4*d^2))
  let C : ℝ := (1/(8*d))/d
  let D : ℝ := C+1/(8*d*r)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let M : ℝ := 4*(A^2*Bc+B^2*Bg+C^2*Bs+D^2*Bt)
  have hBg : 0 ≤ Bg := by
    have h0 := hγ φ₀ (mem_of_mem_nhds hUw)
    exact (tsum_nonneg (fun n => sq_nonneg _)).trans h0.2
  refine ⟨U,inter_mem hUc (inter_mem hUt (inter_mem hUs
    (inter_mem hUg (inter_mem hUv (inter_mem hUh hUw))))),
    fun φ hφ => hUcW hφ.1,N,M,by dsimp [M]; positivity,?_⟩
  intro φ hφ
  obtain ⟨b,hb0,hbs,hbB,hb⟩ := hχ φ hφ.1
  have hφW := hUcW hφ.1
  have htφ := hvals φ hφ.2.2.2.2.1
  have hsφ := hσ φ hφ.2.2.2.2.2.1
  have hgφ := hγ φ hφ.2.2.2.2.2.2
  let t : ℤ → ℝ := fun n => ‖tauN φ n-(n:ℂ)*(Real.pi:ℂ)‖
  let s : ℤ → ℝ := fun n => ‖lamDot φ n-(n:ℂ)*(Real.pi:ℂ)‖
  let g : ℤ → ℝ := fun n => ‖gamma2 φ n‖
  let a : ℤ → ℝ := fun n => A*b n+B*g n+C*s n+D*t n
  have hsT : Summable (fun n => t n^2) := htφ.1
  have hsS : Summable (fun n => s n^2) := hsφ.1
  have hsG : Summable (fun n => g n^2) := hgφ.1
  have hdom := (((hbs.mul_left (A^2)).add (hsG.mul_left (B^2))).add
    (hsS.mul_left (C^2))).add (hsT.mul_left (D^2))
  have hsq (n : ℤ) : a n^2 ≤
      4*(A^2*b n^2+B^2*g n^2+C^2*s n^2+D^2*t n^2) := by
    dsimp [a]
    nlinarith [sq_nonneg (A*b n-B*g n),sq_nonneg (A*b n-C*s n),
      sq_nonneg (A*b n-D*t n),sq_nonneg (B*g n-C*s n),
      sq_nonneg (B*g n-D*t n),sq_nonneg (C*s n-D*t n)]
  have has := (hdom.mul_left 4).of_nonneg_of_le (fun n => sq_nonneg _) hsq
  have ha0 (n : ℤ) : 0 ≤ a n :=
    add_nonneg (add_nonneg (add_nonneg (mul_nonneg hA (hb0 n))
      (mul_nonneg hB (norm_nonneg _))) (mul_nonneg hC (norm_nonneg _)))
      (mul_nonneg hD (norm_nonneg _))
  refine ⟨a,ha0,has,?_,?_⟩
  · apply (has.tsum_le_tsum hsq (hdom.mul_left 4)).trans
    rw [tsum_mul_left, (((hbs.mul_left (A^2)).add (hsG.mul_left (B^2))).add
      (hsS.mul_left (C^2))).tsum_add (hsT.mul_left (D^2)),
      ((hbs.mul_left (A^2)).add (hsG.mul_left (B^2))).tsum_add (hsS.mul_left (C^2)),
      (hbs.mul_left (A^2)).tsum_add (hsG.mul_left (B^2)),
      tsum_mul_left,tsum_mul_left,tsum_mul_left,tsum_mul_left]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hbB (sq_nonneg A))
      (mul_le_mul_of_nonneg_left hgφ.2 (sq_nonneg B)))
      (mul_le_mul_of_nonneg_left hsφ.2 (sq_nonneg C)))
      (mul_le_mul_of_nonneg_left htφ.2.2.2.1 (sq_nonneg D))
  · intro n hn z hz hp
    obtain ⟨hnc,hnt,hns,hng⟩ := hN n hn
    have hτ := ht φ hφ.2.1 n hnt
    have hσ := hs φ hφ.2.2.1 n hns
    have hγ := hg φ hφ.2.2.2.1 n hng
    have hzn : ‖z-(n:ℂ)*(Real.pi:ℂ)‖ = r := mem_sphere_iff_norm.mp hz
    have hw : d ≤ ‖tauN φ n-z‖ := by
      have htri : ‖z-(n:ℂ)*(Real.pi:ℂ)‖ ≤
          ‖tauN φ n-z‖+‖tauN φ n-(n:ℂ)*(Real.pi:ℂ)‖ := by
        have he : z-(n:ℂ)*(Real.pi:ℂ) = -(tauN φ n-z)+(tauN φ n-(n:ℂ)*(Real.pi:ℂ)) := by ring
        rw [he]
        simpa only [norm_neg] using norm_add_le (-(tauN φ n-z)) (tauN φ n-(n:ℂ)*(Real.pi:ℂ))
      have hτd := hτ.trans_le (min_le_left _ _)
      dsimp [r,d] at *
      linarith
    have hw₀ : r ≤ ‖(n:ℂ)*(Real.pi:ℂ)-z‖ := by rw [norm_sub_rev]; exact hzn.ge
    have hcrit : ‖lamDot φ n-tauN φ n‖ ≤ s n+t n := by
      have he : lamDot φ n-tauN φ n =
          (lamDot φ n-(n:ℂ)*(Real.pi:ℂ))-(tauN φ n-(n:ℂ)*(Real.pi:ℂ)) := by ring
      rw [he]
      exact norm_sub_le _ _
    have hcrit1 : ‖lamDot φ n-tauN φ n‖ ≤ 1 := by
      have hτh := hτ.trans_le (min_le_right _ _)
      dsimp [s,t] at hcrit
      linarith
    have hgap : ‖gamma2 φ n‖/(4*d^2) ≤ (1/2:ℝ) := by
      apply (div_le_iff₀ (by positivity : 0 < 4*d^2)).mpr
      linarith
    have hmain := a5ActualCenteredKernel_error38 φ n z ((n:ℂ)*(Real.pi:ℂ)) hp
      d r hd hr hw hw₀ hcrit1 hgap
    have hzD : z ∈ Lib.Dn n := by
      apply mem_ball_iff_norm.mpr
      rw [hzn]
      dsimp [r]
      linarith [Real.pi_pos]
    have hχ := hb n hnc z hzD
    apply hmain.trans
    simpa only [a,A,B,C,D,g,s,t] using
      a5KernelMajorant_mono38 d r ‖a5Chi38 n (φ,z)-1‖ (b n) ‖gamma2 φ n‖
        ‖lamDot φ n-tauN φ n‖ (s n) (t n) hd hχ hcrit

end
end NlsGge.GK38
