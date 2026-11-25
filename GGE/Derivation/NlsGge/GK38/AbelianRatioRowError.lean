import NlsGge.GK38.AbelianRatioCutBound

/-! Actual all-complex-cut ratio error with current-point ℓ² rows.
UNCOMPILED source preparation. A finite row correction extends the genuine P2 tail. -/
set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.GK38
noncomputable section

theorem p3OmittedRatio_all_cut_error38 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW)
    (s₀ : Lib.L2Seq) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧
    ∃ V : Set Lib.L2Seq, V ∈ 𝓝 s₀ ∧ ∃ B H : ℝ, 0 ≤ B ∧ 0 ≤ H ∧
    ∀ φ ∈ U, ∀ s ∈ V, ∃ b : ℤ → ℝ,
      (∀ m, 0 ≤ b m) ∧ Summable (fun m : ℤ => b m^2) ∧
      (∑' m : ℤ, b m^2) ≤ B ∧
      ∀ m : ℤ, ∀ z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
        ‖p2OmittedRatio38 m ((φ,s),z)-1‖ ≤ b m ∧
        ‖p2OmittedRatio38 m ((φ,s),z)‖ ≤ H := by
  classical
  obtain ⟨Ut,hUt,hUtW,Vt,hVt,Nt,Bt,hBt,ht⟩ :=
    p2OmittedRatio_Dn_l2_majorant38 φ₀ hφ₀ s₀
  obtain ⟨Uh,hUh,_hUhW,Vh,hVh,H,hH,hh⟩ :=
    p2OmittedRatio_all_cut_bound38 φ₀ hφ₀ s₀
  obtain ⟨Uc,hUc,_hUcW,Nc,hc⟩ :=
    a5OwnCut_uniform_ball38 φ₀ hφ₀ (Real.pi/16) (by positivity)
  let U := Ut ∩ (Uh ∩ Uc)
  let V := Vt ∩ Vh
  let N := max Nt Nc
  let S : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let f : ℤ → ℝ := fun m => if m ∈ S then H+1 else 0
  have hf0 (m : ℤ) : 0 ≤ f m := by
    dsimp [f]
    split_ifs <;> positivity
  have hfs : Summable (fun m : ℤ => f m^2) :=
    summable_of_ne_finset_zero (s := S) (fun m hm => by simp only [f,ite_eq_right hm,zero_pow (by norm_num : (2 : ℕ) ≠ 0)])
  have hfmass : (∑' m : ℤ, f m^2) = (S.card : ℝ)*(H+1)^2 := by
    rw [tsum_eq_sum (s := S) (fun m hm => by simp only [f,ite_eq_right hm,zero_pow (by norm_num : (2 : ℕ) ≠ 0)])]
    calc
      (∑ m ∈ S, f m^2) = ∑ _m ∈ S, (H+1)^2 := by
        apply Finset.sum_congr rfl
        intro m hm
        simp only [f,ite_eq_left hm]
      _ = (S.card : ℝ)*(H+1)^2 := by rw [Finset.sum_const,nsmul_eq_mul]
  refine ⟨U,inter_mem hUt (inter_mem hUh hUc),fun φ hφ => hUtW hφ.1,
    V,inter_mem hVt hVh,2*Bt+2*((S.card : ℝ)*(H+1)^2),H,?_,hH,?_⟩
  · positivity
  · intro φ hφ s hs
    obtain ⟨b,hb0,hbs,hbB,hb⟩ := ht φ hφ.1 s hs.1
    have hdom : Summable (fun m : ℤ => 2*b m^2+2*f m^2) :=
      (hbs.mul_left 2).add (hfs.mul_left 2)
    have hsq (m : ℤ) : (b m+f m)^2 ≤ 2*b m^2+2*f m^2 := by
      nlinarith [sq_nonneg (b m-f m)]
    have hsum : Summable (fun m : ℤ => (b m+f m)^2) :=
      hdom.of_nonneg_of_le (fun _ => sq_nonneg _) hsq
    refine ⟨fun m => b m+f m,fun m => add_nonneg (hb0 m) (hf0 m),hsum,?_,?_⟩
    · apply (hsum.tsum_le_tsum hsq hdom).trans
      rw [(hbs.mul_left 2).tsum_add (hfs.mul_left 2),tsum_mul_left,tsum_mul_left,hfmass]
      exact add_le_add (mul_le_mul_of_nonneg_left hbB (by norm_num)) le_rfl
    · intro m z hz
      have hnorm := hh φ hφ.2.1 s hs.2 m z hz
      refine ⟨?_,hnorm⟩
      by_cases hmS : m ∈ S
      · have herr : ‖p2OmittedRatio38 m ((φ,s),z)-1‖ ≤ H+1 := by
          calc
            _ ≤ ‖p2OmittedRatio38 m ((φ,s),z)‖+‖(1 : ℂ)‖ := norm_sub_le _ _
            _ = ‖p2OmittedRatio38 m ((φ,s),z)‖+1 := by rw [norm_one]
            _ ≤ H+1 := add_le_add hnorm (le_refl 1)
        simpa only [f,ite_eq_left hmS] using herr.trans (le_add_of_nonneg_left (hb0 m))
      · have hm : (N : ℤ) < |m| := by
          apply lt_of_not_ge
          intro hm
          exact hmS (Finset.mem_Icc.mpr (abs_le.mp hm))
        have hmt : (Nt : ℤ) < |m| := by have he := le_max_left Nt Nc; omega
        have hmc : (Nc : ℤ) < |m| := by have he := le_max_right Nt Nc; omega
        have hzDn : z ∈ Lib.Dn m :=
          ball_subset_ball (by nlinarith [Real.pi_pos] : Real.pi/16 ≤ Real.pi/4)
            (hc φ hφ.2.2 m hmc hz)
        simpa only [f,ite_eq_right hmS,add_zero] using hb m hmt z hzDn

end
end NlsGge.GK38
