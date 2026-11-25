import NlsGge.GK38.AbelianPeriodBound
import NlsGge.GK38.AbelianDenominator

/-! Prospective full actual P2 uniform square bound. All n are signed integers;
ONE potential/input neighbourhood precedes EVERY n. No Hilbert Fn is bundled here. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem p2FullPeriod_uniform_l2_bound38 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) (s₀ : Lib.L2Seq) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧
      ∃ V : Set Lib.L2Seq, V ∈ 𝓝 s₀ ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ φ ∈ U, ∀ s ∈ V, ∀ n : ℤ,
        Summable (fun m : ℤ => ‖(((n-m:ℤ):ℂ))*
          abelianPeriod38 m φ (p2FullNumerator38 n s)‖^2) ∧
        (∑' m : ℤ, ‖(((n-m:ℤ):ℂ))*
          abelianPeriod38 m φ (p2FullNumerator38 n s)‖^2) ≤ B := by
  classical
  obtain ⟨Uh,hUh,hUhW,Vh,hVh,H,hH,hh⟩ := p2OmittedRatio_all_cut_bound38 φ₀ hφ₀ s₀
  obtain ⟨Ue,hUe,_hUeW,Ve,hVe,E,hE,he⟩ := p2RowEnvelope_common_l2_bound38 φ₀ hφ₀ s₀
  obtain ⟨Ug,hUg,hUgW,_hUgo,_hUgc,C,R,c,Ng,hgeom,hspec⟩ :=
    local_isolatingFamily_common38 φ₀ hφ₀
  have hc : 0 < c := lt_of_lt_of_le (by norm_num) hgeom.2.2.1
  obtain ⟨Vs,hVs,Ns,hs⟩ := p2Input_tail_own_disc38 s₀ C R c Ng hgeom
  let A : ℝ := ‖s₀‖+1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨J,hJ⟩ := exists_nat_gt ((Ns:ℝ)+2*(A+Real.pi/4)/Real.pi)
  let M : ℕ := max Ng J
  let Sn : Finset ℤ := Finset.Icc (-(Ns:ℤ)) (Ns:ℤ)
  let Sm : Finset ℤ := Finset.Icc (-(M:ℤ)) (M:ℤ)
  have hp₀ : (φ₀,s₀) ∈ gkW ×ˢ (univ : Set Lib.L2Seq) := ⟨hφ₀,mem_univ _⟩
  obtain ⟨ε,hε,F,hF,hf⟩ := p2FiniteCompact_parameter_bound38 (Sn ×ˢ Sm)
    (fun q p (_z : ℂ) => (((q.1-q.2:ℤ):ℂ))*
      abelianPeriod38 q.2 p.1 (p2FullNumerator38 q.1 p.2)) (φ₀,s₀)
    (fun _ => ({0} : Set ℂ)) (fun _ _ => isCompact_singleton)
    (fun q _ z _ => AnalyticAt.comp
      (g := fun p : PotPair × Lib.L2Seq => (((q.1-q.2:ℤ):ℂ))*
        abelianPeriod38 q.2 p.1 (p2FullNumerator38 q.1 p.2))
      (f := fun p : (PotPair × Lib.L2Seq) × ℂ => p.1)
      (p2FullCoordinate_analytic38 q.1 q.2 (φ₀,s₀) hp₀) analyticAt_fst)
  let U := Uh ∩ (Ue ∩ (Ug ∩ ball φ₀ ε))
  let V := Vh ∩ (Ve ∩ (Vs ∩ (ball s₀ 1 ∩ ball s₀ ε)))
  let D : ℝ := max c (2/Real.pi)
  have hD : 0 ≤ D := hc.le.trans (le_max_left _ _)
  let K : ℝ := 2*Real.pi*(D*H)
  have hK : 0 ≤ K := mul_nonneg (by positivity) (mul_nonneg hD hH)
  let F₀ : ℝ := max F (K*Real.sqrt E)
  have hF₀ : 0 ≤ F₀ := hF.trans (le_max_left _ _)
  refine ⟨U,inter_mem hUh (inter_mem hUe (inter_mem hUg (ball_mem_nhds _ hε))),
    fun φ hφ => hUhW hφ.1,V,inter_mem hVh (inter_mem hVe
      (inter_mem hVs (inter_mem (ball_mem_nhds _ (by norm_num)) (ball_mem_nhds _ hε)))),
    (Sm.card:ℝ)*F₀^2+2*(K^2*E),by positivity,?_⟩
  intro φ hφ s hsV n
  have hφW := hUhW hφ.1
  have hfam : IsolatingFamily38 φ C R := ⟨c,Ng,hgeom,hspec φ hφ.2.2.1⟩
  have hrow := he φ hφ.2.1 s hsV.2.1
  have hsA : ∀ j : ℤ, ‖s j‖ ≤ A := by
    intro j
    have ht := norm_le_norm_sub_add s s₀
    have hd : ‖s-s₀‖ < 1 := mem_ball_iff_norm.mp hsV.2.2.2.1
    exact (Lib.norm_coord_le s j).trans (by dsimp [A]; linarith)
  have hpair : (φ,s) ∈ ball (φ₀,s₀) ε := by
    change dist (φ,s) (φ₀,s₀)<ε
    rw [Prod.dist_eq]
    exact max_lt (mem_ball.mp hφ.2.2.2) (mem_ball.mp hsV.2.2.2.2)
  have hrowPoint (m : ℤ) : p2RowEnvelope38 φ s m ≤ Real.sqrt E := by
    have ht : p2RowEnvelope38 φ s m^2 ≤ ∑' j : ℤ, p2RowEnvelope38 φ s j^2 := by
      simpa only [Finset.sum_singleton] using
        hrow.1.sum_le_tsum ({m}:Finset ℤ) (fun _ _ => sq_nonneg _)
    have hb := ht.trans hrow.2
    nlinarith [Real.sq_sqrt hE,Real.sqrt_nonneg E]
  have hlargeN (hn : (Ns:ℤ) < |n|) (m : ℤ) :
      ‖(((n-m:ℤ):ℂ))*abelianPeriod38 m φ (p2FullNumerator38 n s)‖ ≤ K*p2RowEnvelope38 φ s m := by
    by_cases hnm : n=m
    · subst m
      simp only [sub_self,Int.cast_zero,zero_mul,norm_zero]
      exact mul_nonneg hK (p2RowEnvelope_nonneg38 φ s n)
    have hnball := ball_subset_closedBall (hs s hsV.2.2.1 n hn)
    have hd := fun z hz => p2OwnSigma_denominator38 C R c Ng hgeom n m hnm s hnball z hz
    have hb := p2Period_bound_of_denominator38 φ hφW C R hfam s n m D H hD hH
      (fun z hz => (hd z hz).1)
      (fun z hz => (hd z (ball_subset_closedBall (((hspec φ hφ.2.2.1).1 m).1 hz))).2.trans
        (le_max_left _ _))
      (hh φ hφ.1 s hsV.1 m)
    exact hb
  have htail (m : ℤ) (hm : m ∉ Sm) :
      ‖(((n-m:ℤ):ℂ))*abelianPeriod38 m φ (p2FullNumerator38 n s)‖ ≤ K*p2RowEnvelope38 φ s m := by
    by_cases hn : (Ns:ℤ) < |n|
    · exact hlargeN hn m
    have hnsmall : |n| ≤ (Ns:ℤ) := le_of_not_gt hn
    have hmlarge : (M:ℤ) < |m| := by
      by_contra hm'
      exact hm (by simpa only [Sm,Finset.mem_Icc] using abs_le.mp (not_lt.mp hm'))
    have hnm : n ≠ m := by
      intro heq
      subst m
      have hNsM : Ns < M := by
        have hJM : (J:ℝ) ≤ (M:ℝ) := by exact_mod_cast le_max_right Ng J
        have hpos : 0 < 2*(A+Real.pi/4)/Real.pi := by positivity
        exact_mod_cast (show (Ns:ℝ)<(M:ℝ) by linarith)
      omega
    have hmg : (Ng:ℤ) < |m| := by have he := le_max_left Ng J; omega
    have hfar : 2*(A+Real.pi/4) ≤ Real.pi*|((n-m:ℤ):ℝ)| := by
      have hmR : (M:ℝ) < |(m:ℝ)| := by exact_mod_cast hmlarge
      have hnR : |(n:ℝ)| ≤ (Ns:ℝ) := by exact_mod_cast hnsmall
      have hJM : (J:ℝ) ≤ (M:ℝ) := by exact_mod_cast le_max_right Ng J
      have htri : |(m:ℝ)| ≤ |(n:ℝ)-(m:ℝ)|+|(n:ℝ)| := by
        calc
          |(m:ℝ)| = |(n:ℝ)-((n:ℝ)-(m:ℝ))| := by congr 1; ring
          _ ≤ |(n:ℝ)|+|(n:ℝ)-(m:ℝ)| := by
            simpa only [Real.norm_eq_abs] using norm_sub_le (n:ℝ) ((n:ℝ)-(m:ℝ))
          _ = |(n:ℝ)-(m:ℝ)|+|(n:ℝ)| := add_comm _ _
      have hJ' := (div_lt_iff₀ Real.pi_pos).mp (show 2*(A+Real.pi/4)/Real.pi < (J:ℝ)-(Ns:ℝ) by linarith)
      have hgap : (J:ℝ)-(Ns:ℝ) < |(n:ℝ)-(m:ℝ)| := by linarith
      have hprod := mul_lt_mul_of_pos_right hgap Real.pi_pos
      push_cast
      nlinarith
    have ht := hgeom.2.2.2.2 m hmg
    have hd : ∀ z ∈ closedBall (C m) (R m),
        Lib.sigmaOf s n-z ≠ 0 ∧ ‖(((n-m:ℤ):ℂ))/(Lib.sigmaOf s n-z)‖ ≤ 2/Real.pi := by
      intro z hz
      apply p2Far_disc_denominator38 s n m A (hsA n) hfar hnm z
      simpa only [ht.1,ht.2.1,countingCenter38] using hz
    exact p2Period_bound_of_denominator38 φ hφW C R hfam s n m D H hD hH
      (fun z hz => (hd z hz).1)
      (fun z hz => (hd z (ball_subset_closedBall (((hspec φ hφ.2.2.1).1 m).1 hz))).2.trans
        (le_max_right _ _)) (hh φ hφ.1 s hsV.1 m)
  have hfinite (m : ℤ) (hm : m ∈ Sm) :
      ‖(((n-m:ℤ):ℂ))*abelianPeriod38 m φ (p2FullNumerator38 n s)‖ ≤ F₀ := by
    by_cases hn : (Ns:ℤ) < |n|
    · exact ((hlargeN hn m).trans
        (mul_le_mul_of_nonneg_left (hrowPoint m) hK)).trans (le_max_right _ _)
    have hnSn : n ∈ Sn := by simpa only [Sn,Finset.mem_Icc] using abs_le.mp (not_lt.mp hn)
    exact (hf (φ,s) hpair (n,m) (Finset.mem_product.mpr ⟨hnSn,hm⟩) 0 (by simp)).trans
      (le_max_left _ _)
  have hks : Summable (fun m : ℤ => (K*p2RowEnvelope38 φ s m)^2) := by
    simpa only [mul_pow] using hrow.1.mul_left (K^2)
  have hkB : (∑' m : ℤ, (K*p2RowEnvelope38 φ s m)^2) ≤ K^2*E := by
    simp only [mul_pow,tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hrow.2 (sq_nonneg K)
  have hz : Summable (fun _ : ℤ => (0:ℝ)^2) := by simp
  have hsum := finite_tail_square_sum38
    (fun m => (((n-m:ℤ):ℂ))*abelianPeriod38 m φ (p2FullNumerator38 n s))
    Sm F₀ 0 (K^2*E) 0 hF₀ le_rfl (fun m => K*p2RowEnvelope38 φ s m) (fun _ => 0)
    (fun m => mul_nonneg hK (p2RowEnvelope_nonneg38 φ s m)) (fun _ => le_rfl)
    hks hz hkB (by simp) hfinite (fun m hm => by simpa using htail m hm)
  simpa using hsum

#print axioms p2FullPeriod_uniform_l2_bound38
end
end NlsGge.GK38
