import NlsGge.GK38.AbelianHilbert

/-! Actual full-space padded period maps have ONE local bound before ALL
signed indices. The missing coordinate is completed by the actual linear 2s_n.
This supplies the holomorphic equicontinuity argument without an open-ball
uniform-zero-tail assertion. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem p6Numerator_extend_restrict38 (n : ℤ) (s : Lib.L2Seq) :
    p2FullNumerator38 n (p2Extend38 n (p2Restrict38 n s))=p2FullNumerator38 n s := by
  have he : p2Extend38 n (p2Restrict38 n s)+(s n) • lp.single 2 n (1 : ℂ)=s := by
    apply Subtype.ext
    funext m
    by_cases hm : m=n
    · subst m
      simp only [lp.coeFn_add,Pi.add_apply,p2Extend_self38,lp.coeFn_smul,
        Pi.smul_apply,smul_eq_mul,lp.single_apply_self,mul_one,zero_add]
    · change p2Extend38 n (p2Restrict38 n s) m+
        (s n)*(lp.single (E := fun _ : ℤ => ℂ) 2 n (1 : ℂ)) m=s m
      rw [p2Extend_at38 n (p2Restrict38 n s) ⟨m,hm⟩,
        p2Restrict_apply38,lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 n (1 : ℂ) hm,
        mul_zero,add_zero]
  funext z
  change -2*Lib.omitProd n (p2Extend38 n (p2Restrict38 n s)) z=
    -2*Lib.omitProd n s z
  calc
    _ = -2*Lib.omitProd n
        (p2Extend38 n (p2Restrict38 n s)+(s n) • lp.single 2 n (1 : ℂ)) z := by
      rw [Lib.omitProd_add_single]
    _ = _ := congrArg (fun t : Lib.L2Seq => -2*Lib.omitProd n t z) he

def p6PaddedFn38 (n : ℤ) (p : PotPair × Lib.L2Seq) : Lib.L2Seq :=
  p2Extend38 n (p2Fn38 n (p.1,p2Restrict38 n p.2))+
    (2 : ℂ) • lp.single 2 n (p.2 n)

theorem p6PaddedFn_analytic38 (n : ℤ) :
    AnalyticOnNhd ℂ (p6PaddedFn38 n) (gkW ×ˢ (univ : Set Lib.L2Seq)) := by
  intro p hp
  have harg : AnalyticAt ℂ
      (fun q : PotPair × Lib.L2Seq => (q.1,p2Restrict38 n q.2)) p :=
    analyticAt_fst.prod (((p2Restrict38 n).analyticAt p.2).comp analyticAt_snd)
  have hf : AnalyticAt ℂ
      (fun q : PotPair × Lib.L2Seq => p2Fn38 n (q.1,p2Restrict38 n q.2)) p :=
    AnalyticAt.comp (g := p2Fn38 n)
      (f := fun q : PotPair × Lib.L2Seq => (q.1,p2Restrict38 n q.2))
      (p2Fn_analytic38 n (p.1,p2Restrict38 n p.2) ⟨hp.1,mem_univ _⟩) harg
  have he : AnalyticAt ℂ (fun q : PotPair × Lib.L2Seq =>
      p2Extend38 n (p2Fn38 n (q.1,p2Restrict38 n q.2))) p :=
    AnalyticAt.comp (g := p2Extend38 n)
      (f := fun q : PotPair × Lib.L2Seq => p2Fn38 n (q.1,p2Restrict38 n q.2))
      ((p2Extend38 n).analyticAt _) hf
  have hcoord : AnalyticAt ℂ (fun q : PotPair × Lib.L2Seq => q.2 n) p :=
    AnalyticAt.comp (g := lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n)
      (f := fun q : PotPair × Lib.L2Seq => q.2)
      ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).analyticAt _) analyticAt_snd
  have hs : AnalyticAt ℂ
      (fun q : PotPair × Lib.L2Seq => lp.single (E := fun _ : ℤ => ℂ) 2 n (q.2 n)) p :=
    AnalyticAt.comp (g := lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 n)
      (f := fun q : PotPair × Lib.L2Seq => q.2 n)
      ((lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 n).analyticAt _) hcoord
  exact he.add (hs.const_smul (c := (2 : ℂ)))

theorem p6PaddedFn_uniform_norm_bound38 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW)
    (s₀ : Lib.L2Seq) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧
      ∃ V : Set Lib.L2Seq, V ∈ 𝓝 s₀ ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ φ ∈ U, ∀ s ∈ V, ∀ n : ℤ, ‖p6PaddedFn38 n (φ,s)‖ ≤ M := by
  obtain ⟨U,hU,hUW,V,hV,B,hB,hb⟩ := p2OmittedPeriod_uniform_l2_bound38 φ₀ hφ₀ s₀
  refine ⟨U,hU,hUW,V ∩ ball s₀ 1,inter_mem hV (ball_mem_nhds _ (by norm_num)),
    Real.sqrt B+2*(‖s₀‖+1),by positivity,?_⟩
  intro φ hφ s hs n
  have hφW : φ ∈ gkW := hUW hφ
  have hmass := (hb φ hφ s hs.1 n).2
  have hsq : ‖p2Fn38 n (φ,p2Restrict38 n s)‖^2 ≤ B := by
    have he := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal)
      (p2Fn38 n (φ,p2Restrict38 n s))
    simp only [ENNReal.toReal_ofNat,Real.rpow_two] at he
    have hc (m : P2Index38 n) :
        p2Fn38 n (φ,p2Restrict38 n s) m=
        (((n-m.1 : ℤ) : ℂ))*abelianPeriod38 m.1 φ (p2FullNumerator38 n s) := by
      apply (p2Fn_apply38 n (φ,p2Restrict38 n s) hφW m).trans
      change (((n-m.1 : ℤ) : ℂ))*abelianPeriod38 m.1 φ
        (p2FullNumerator38 n (p2Extend38 n (p2Restrict38 n s)))=_
      rw [p6Numerator_extend_restrict38]
    calc
      _ = ∑' m : P2Index38 n, ‖p2Fn38 n (φ,p2Restrict38 n s) m‖^2 := he
      _ = ∑' m : P2Index38 n,
          ‖(((n-m.1 : ℤ) : ℂ))*abelianPeriod38 m.1 φ (p2FullNumerator38 n s)‖^2 :=
        tsum_congr (fun m => congrArg (fun z : ℂ => ‖z‖^2) (hc m))
      _ ≤ B := hmass
  have hnorm : ‖p2Fn38 n (φ,p2Restrict38 n s)‖ ≤ Real.sqrt B := by
    nlinarith [Real.sq_sqrt hB,Real.sqrt_nonneg B,
      norm_nonneg (p2Fn38 n (φ,p2Restrict38 n s))]
  have hsbound : ‖s‖ ≤ ‖s₀‖+1 := by
    have ht := norm_le_norm_sub_add s s₀
    have hd := mem_ball_iff_norm.mp hs.2
    linarith
  unfold p6PaddedFn38
  calc
    _ ≤ ‖p2Extend38 n (p2Fn38 n (φ,p2Restrict38 n s))‖+
        ‖(2 : ℂ) • lp.single 2 n (s n)‖ := norm_add_le _ _
    _ = ‖p2Fn38 n (φ,p2Restrict38 n s)‖+2*‖s n‖ := by
      rw [p2Extend_norm38,norm_smul,lp.norm_single (by norm_num)]
      norm_num
    _ ≤ Real.sqrt B+2*(‖s₀‖+1) :=
      add_le_add hnorm (mul_le_mul_of_nonneg_left ((Lib.norm_coord_le s n).trans hsbound)
        (by norm_num))

end
end NlsGge.GK38
