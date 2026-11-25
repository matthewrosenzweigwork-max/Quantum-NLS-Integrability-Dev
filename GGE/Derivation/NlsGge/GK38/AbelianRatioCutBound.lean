import NlsGge.GK38.AbelianRatioMajorant
import NlsGge.GK38.AbelianParameterBounds
import NlsGge.GK38.XiSqUniformSmallness

/-! Prospective actual uniform omitted-ratio bound on every complex spectral cut.
Only finitely many spectral discs are compact; no parameter ball is compact. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem p2FiniteCompact_parameter_bound38 {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι : Type*} (S : Finset ι) (F : ι → E → ℂ → ℂ)
    (x₀ : E) (K : ι → Set ℂ) (hK : ∀ i ∈ S, IsCompact (K i))
    (hF : ∀ i ∈ S, ∀ z ∈ K i, AnalyticAt ℂ (Function.uncurry (F i)) (x₀,z)) :
    ∃ ε > 0, ∃ B : ℝ, 0 ≤ B ∧
      ∀ x ∈ ball x₀ ε, ∀ i ∈ S, ∀ z ∈ K i, ‖F i x z‖ ≤ B := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,0,le_rfl,by simp⟩
  | @insert i S hi ih =>
    obtain ⟨ε,hε,B,hB,hb⟩ := ih (fun j hj => hK j (Finset.mem_insert_of_mem hj))
      (fun j hj => hF j (Finset.mem_insert_of_mem hj))
    obtain ⟨δ,hδ,A,hA,ha⟩ := p2Compact_parameter_bound38 (F i) x₀ (K i)
      (hK i (Finset.mem_insert_self i S)) (hF i (Finset.mem_insert_self i S))
    refine ⟨min ε δ,lt_min hε hδ,max B A,(hB.trans (le_max_left _ _)),?_⟩
    intro x hx j hj z hz
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (ha x (ball_subset_ball (min_le_right _ _) hx) z hz).trans (le_max_right _ _)
    · exact (hb x (ball_subset_ball (min_le_left _ _) hx) j hj z hz).trans (le_max_left _ _)

/-- One potential neighbourhood and one arbitrary-input neighbourhood, before ALL rows.
Far rows use an actual square-summable ratio error; finite rows use fixed original
full-family discs and their actual omitted-domain analyticity. -/
theorem p2OmittedRatio_all_cut_bound38 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) (s₀ : Lib.L2Seq) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧
      ∃ V : Set Lib.L2Seq, V ∈ 𝓝 s₀ ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ φ ∈ U, ∀ s ∈ V, ∀ m : ℤ,
        ∀ z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
          ‖p2OmittedRatio38 m ((φ,s),z)‖ ≤ B := by
  obtain ⟨Ut,hUt,hUtW,Vt,hVt,Nt,Bt,hBt,ht⟩ :=
    p2OmittedRatio_Dn_l2_majorant38 φ₀ hφ₀ s₀
  obtain ⟨Uc,hUc,_hUcW,Nc,hcut⟩ :=
    a5OwnCut_uniform_ball38 φ₀ hφ₀ (Real.pi/16) (by positivity)
  obtain ⟨Ug,hUg,hUgW,_hUgo,_hUgc,C,R,c,Ng,hgeom,hspec⟩ :=
    local_isolatingFamily_common38 φ₀ hφ₀
  let N := max Nt Nc
  let S : Finset ℤ := Finset.Icc (-(N:ℤ)) (N:ℤ)
  have hφg : φ₀ ∈ Ug := mem_of_mem_nhds hUg
  have hfam₀ : IsolatingFamily38 φ₀ C R := ⟨c,Ng,hgeom,hspec φ₀ hφg⟩
  obtain ⟨ε,hε,Bh,hBh,hh⟩ := p2FiniteCompact_parameter_bound38 S
    (fun m p z => p2OmittedRatio38 m (p,z)) (φ₀,s₀)
    (fun m => closedBall (C m) (R m)) (fun _ _ => isCompact_closedBall _ _)
    (fun m _ z hz => p2OmittedRatio_analytic38 m ((φ₀,s₀),z)
      (a5OwnClosedBall_omittedDomain38 φ₀ hφ₀ C R hfam₀ m z hz))
  let U := Ut ∩ (Uc ∩ (Ug ∩ ball φ₀ ε))
  let V := Vt ∩ ball s₀ ε
  refine ⟨U,inter_mem hUt (inter_mem hUc (inter_mem hUg (ball_mem_nhds _ hε))),
    fun φ hφ => hUtW hφ.1,V,inter_mem hVt (ball_mem_nhds _ hε),
    max Bh (1+Real.sqrt Bt),hBh.trans (le_max_left _ _),?_⟩
  intro φ hφ s hs m z hz
  by_cases hm : (N:ℤ) < |m|
  · have hmt : (Nt:ℤ) < |m| := by have he := le_max_left Nt Nc; omega
    have hmc : (Nc:ℤ) < |m| := by have he := le_max_right Nt Nc; omega
    obtain ⟨b,hb0,hbs,hbB,hb⟩ := ht φ hφ.1 s hs.1
    have hterm : b m^2 ≤ ∑' j : ℤ, b j^2 := by
      simpa only [Finset.sum_singleton] using
        hbs.sum_le_tsum ({m}:Finset ℤ) (fun _ _ => sq_nonneg _)
    have hpoint : b m^2 ≤ Bt := hterm.trans hbB
    have hbm : b m ≤ Real.sqrt Bt := by
      nlinarith [Real.sq_sqrt hBt,Real.sqrt_nonneg Bt]
    have hzDn : z ∈ Lib.Dn m :=
      ball_subset_ball (by nlinarith [Real.pi_pos] : Real.pi/16 ≤ Real.pi/4)
        (hcut φ hφ.2.1 m hmc hz)
    have herror := hb m hmt z hzDn
    have hnorm := norm_le_norm_sub_add (p2OmittedRatio38 m ((φ,s),z)) (1:ℂ)
    rw [norm_one] at hnorm
    exact (show ‖p2OmittedRatio38 m ((φ,s),z)‖ ≤ 1+Real.sqrt Bt by linarith).trans
      (le_max_right _ _)
  · have hmS : m ∈ S := by
      simp only [S,Finset.mem_Icc]
      have hmle : |m| ≤ (N:ℤ) := le_of_not_gt hm
      exact abs_le.mp hmle
    have hp : (φ,s) ∈ ball (φ₀,s₀) ε := by
      change dist (φ,s) (φ₀,s₀) < ε
      rw [Prod.dist_eq]
      exact max_lt (mem_ball.mp hφ.2.2.2) (mem_ball.mp hs.2)
    have hown := (hspec φ hφ.2.2.1).1 m
    exact (hh (φ,s) hp m hmS z (ball_subset_closedBall (hown.1 hz))).trans (le_max_left _ _)

#print axioms p2FiniteCompact_parameter_bound38
#print axioms p2OmittedRatio_all_cut_bound38
end
end NlsGge.GK38
