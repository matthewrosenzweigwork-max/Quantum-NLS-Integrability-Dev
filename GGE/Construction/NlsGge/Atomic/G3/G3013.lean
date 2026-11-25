                                                                                                                                                                                                                                                                                                                                                                                                                                                                                
import Mathlib
import NlsGge.GK38.AngleEndpointVariety
import NlsGge.GK38.RealTypeSpectrumSigns
import NlsGge.GK38.Lib.Rouche
import NlsGge.GK38.IsolatingFamily
import NlsGge.Atomic.G1.G1060
import NlsGge.Atomic.G3.G3008
import NlsGge.Atomic.G3.G3012

set_option autoImplicit false

                                                                         
                                                                                                                  
                                                                                                              
                                                                                                             
                                                                                                                      
                                                                                                             

namespace NlsGge.Atomic.G3013S3

open Filter Topology Set Metric
open NlsGge.GK38 NlsGge.Pilot

noncomputable section

theorem root_mem_labels (ψ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hψ : IsolatingSpectral38 ψ C R) (m : ℤ) (z : ℂ) (hz : z ∈ ball (C m) (R m))
    (hz0 : perChar ψ z = 0) : z = lamMinus ψ m ∨ z = lamPlus ψ m := by
  have hpc : AnalyticOnNhd ℂ (perChar ψ) (closedBall (C m) (R m)) :=
    (analyticOnNhd_perChar_z ψ).mono (subset_univ _)
  obtain ⟨w, hw⟩ : (sphere (C m) (R m)).Nonempty := NormedSpace.sphere_nonempty.mpr (hRpos m).le
  have hw0 : perChar ψ w ≠ 0 :=
    (((hψ.1 m).2.2.2.2.2.2.2.2.2.2.2.2 w hw).1)
  have hmem := (Lib.mem_zeroMultiset_iff_zero hpc ball_subset_closedBall
    ⟨w, sphere_subset_closedBall hw, hw0⟩).mpr ⟨hz, hz0⟩
  rw [← (hψ.1 m).2.2.2.2.1] at hmem
  simpa only [Multiset.mem_cons, Multiset.notMem_zero, or_false] using hmem

theorem perChar_order_one (ψ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hψ : IsolatingSpectral38 ψ C R) (m : ℤ) (hab : lamMinus ψ m ≠ lamPlus ψ m) (z : ℂ)
    (hz : z = lamMinus ψ m ∨ z = lamPlus ψ m) : analyticOrderNatAt (perChar ψ) z = 1 := by
  classical
  have hpc : AnalyticOnNhd ℂ (perChar ψ) (closedBall (C m) (R m)) :=
    (analyticOnNhd_perChar_z ψ).mono (subset_univ _)
  have hzb : z ∈ ball (C m) (R m) := by
    rcases hz with rfl | rfl
    · exact (hψ.1 m).1 (left_mem_segment ℝ _ _)
    · exact (hψ.1 m).1 (right_mem_segment ℝ _ _)
  have hc := Lib.count_zeroMultiset_ball hpc z
  rw [← (hψ.1 m).2.2.2.2.1, if_pos hzb] at hc
  rw [← hc]
  rcases hz with rfl | rfl
  · simp [Multiset.count_cons, hab]
  · simp [Multiset.count_cons, hab.symm]

theorem neg_one_zpow_sq (m : ℤ) : ((-1 : ℂ) ^ m) ^ 2 = 1 := by
  rcases Int.even_or_odd m with h | h
  · rw [h.neg_one_zpow]; norm_num
  · rw [h.neg_one_zpow]; norm_num

theorem exists_endpoint_branch (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) (m : ℤ)
    (hne : lamPlus φ₀ m ≠ lamMinus φ₀ m) (z : ℂ)
    (hz : z = lamMinus φ₀ m ∨ z = lamPlus φ₀ m) :
    ∃ (κ : PotPair → ℂ) (U : Set PotPair), IsOpen U ∧ φ₀ ∈ U ∧ AnalyticOnNhd ℂ κ U ∧
      κ φ₀ = z ∧ ∀ ψ ∈ U, perChar ψ (κ ψ) = 0 := by
  obtain ⟨u, ρ, ⟨hρ, C, R, c, N, hg, hspec⟩, hmem⟩ := hφ₀
  have hRpos : ∀ n, 0 < R n := fun n => (hg.1 n).1
  have hφ₀gk : φ₀ ∈ gkW := ⟨u, ρ, ⟨hρ, C, R, c, N, hg, hspec⟩, hmem⟩
  set c₁ : ℂ := (-1 : ℂ) ^ m with hc₁def
  have hc₁ : c₁ ^ 2 = 1 := neg_one_zpow_sq m
  have hc0 : c₁ ≠ 0 := by
    intro h
    rw [h] at hc₁
    norm_num at hc₁
  obtain ⟨hs1, hs2⟩ := NlsGge.Atomic.G3012S3.sign_on_gkW φ₀ hφ₀gk m
  have hDz : NlsGge.GK38.discrim φ₀ z = 2 * c₁ := by
    rcases hz with rfl | rfl
    · exact hs1
    · exact hs2
  have hord := perChar_order_one φ₀ C R hRpos (hspec φ₀ hmem) m (Ne.symm hne) z hz
  have hfa : AnalyticAt ℂ (fun w => NlsGge.GK38.discrim φ₀ w - 2 * c₁) z :=
    (((analyticOnNhd_discrim_z φ₀).sub analyticOnNhd_const) z (mem_univ z))
  have hga : AnalyticAt ℂ (fun w => NlsGge.GK38.discrim φ₀ w + 2 * c₁) z :=
    (((analyticOnNhd_discrim_z φ₀).add analyticOnNhd_const) z (mem_univ z))
  have hprod : perChar φ₀ = (fun w => NlsGge.GK38.discrim φ₀ w - 2 * c₁) *
      (fun w => NlsGge.GK38.discrim φ₀ w + 2 * c₁) := by
    funext w
    simp only [Pi.mul_apply]
    rw [perChar_eq]
    linear_combination 4 * hc₁
  have hg0 : analyticOrderAt (fun w => NlsGge.GK38.discrim φ₀ w + 2 * c₁) z = 0 := by
    apply hga.analyticOrderAt_eq_zero.mpr
    show NlsGge.GK38.discrim φ₀ z + 2 * c₁ ≠ 0
    rw [hDz]
    intro h
    apply hc0
    linear_combination (1 / 4 : ℂ) * h
  have hne_top : analyticOrderAt (perChar φ₀) z ≠ ⊤ := by
    intro h
    simp [analyticOrderNatAt, h] at hord
  have hone : analyticOrderAt (perChar φ₀) z = 1 := by
    have h := ENat.coe_toNat hne_top
    have h' : (analyticOrderAt (perChar φ₀) z).toNat = 1 := hord
    rw [h'] at h
    simpa using h.symm
  have hf1 : analyticOrderAt (fun w => NlsGge.GK38.discrim φ₀ w - 2 * c₁) z = 1 := by
    have h := analyticOrderAt_mul hfa hga
    rw [← hprod, hg0, add_zero, hone] at h
    exact h.symm
  have hs : SimpleBoundary38.IsSimpleBoundaryEigenvalue (SimpleBoundary38.floquetProblem c₁ hc₁) φ₀ z :=
    ⟨by
      show NlsGge.GK38.discrim φ₀ z - 2 * c₁ = 0
      rw [hDz]; ring, hf1⟩
  obtain ⟨b⟩ := SimpleBoundary38.localEigenvalue_exists _ φ₀ z hs
  refine ⟨b.toFun, b.domain, b.isOpen_domain, b.base_mem, b.analytic, b.value, fun ψ hψ => ?_⟩
  have h := b.root ψ hψ
  have h' : NlsGge.GK38.discrim ψ (b.toFun ψ) - 2 * c₁ = 0 := h
  rw [perChar_eq]
  have h2 : NlsGge.GK38.discrim ψ (b.toFun ψ) = 2 * c₁ := sub_eq_zero.mp h'
  rw [h2]
  linear_combination 4 * hc₁

theorem finish_core (m : ℤ) (φ₀ : PotPair) (u : PhysicalL2) (ρ : ℝ)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hVgk : ∀ ψ ∈ ball (realSlice u) ρ, ψ ∈ gkW)
    (hspec : ∀ φ ∈ ball (realSlice u) ρ, IsolatingSpectral38 φ C R)
    (hmem : φ₀ ∈ ball (realSlice u) ρ) (hφ₀ : φ₀ ∈ gkW)
    (x y : ℂ) (hxy : x ≠ y) (hnear : ‖muSeq φ₀ m - x‖ ≤ ‖muSeq φ₀ m - y‖)
    (hxb : x ∈ ball (C m) (R m)) (hyb : y ∈ ball (C m) (R m))
    (κx κy : PotPair → ℂ) (U : Set PotPair) (hU : IsOpen U) (hφU : φ₀ ∈ U)
    (hκx : AnalyticOnNhd ℂ κx U) (hκy : AnalyticOnNhd ℂ κy U)
    (hx0 : κx φ₀ = x) (hy0 : κy φ₀ = y)
    (hrx : ∀ ψ ∈ U, perChar ψ (κx ψ) = 0) (hry : ∀ ψ ∈ U, perChar ψ (κy ψ) = 0) :
    ∃ V : Set PotPair, IsOpen V ∧ IsConnected V ∧ φ₀ ∈ V ∧ V ⊆ gkW ∧
      ∃ ρm ρp : PotPair → ℂ, AnalyticOnNhd ℂ ρm V ∧ AnalyticOnNhd ℂ ρp V ∧
        ∀ ψ ∈ V,
          ((ρm ψ = lamMinus ψ m ∧ ρp ψ = lamPlus ψ m) ∨
            (ρm ψ = lamPlus ψ m ∧ ρp ψ = lamMinus ψ m)) ∧
          ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
            ‖lamPlus ψ m - lamMinus ψ m‖ / 3 ≤
              ‖ρp ψ - ((t : ℂ) * muSeq ψ m + (1 - (t : ℂ)) * ρm ψ)‖ := by
  have hg0 : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy.symm)
  set δ : ℝ := ‖y - x‖ / 24 with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hcx : ContinuousAt κx φ₀ := (hκx.continuousOn).continuousAt (hU.mem_nhds hφU)
  have hcy : ContinuousAt κy φ₀ := (hκy.continuousOn).continuousAt (hU.mem_nhds hφU)
  have hcμ : ContinuousAt (fun ψ : PotPair => muSeq ψ m) φ₀ :=
    (analyticOnNhd_muSeq_complex38 m φ₀ hφ₀).continuousAt
  have e1 : ∀ᶠ ψ in 𝓝 φ₀, ψ ∈ U := hU.mem_nhds hφU
  have e2 : ∀ᶠ ψ in 𝓝 φ₀, ψ ∈ ball (realSlice u) ρ := isOpen_ball.mem_nhds hmem
  have e3 : ∀ᶠ ψ in 𝓝 φ₀, κx ψ ∈ ball (C m) (R m) :=
    hcx.preimage_mem_nhds (isOpen_ball.mem_nhds (by rw [hx0]; exact hxb))
  have e4 : ∀ᶠ ψ in 𝓝 φ₀, κy ψ ∈ ball (C m) (R m) :=
    hcy.preimage_mem_nhds (isOpen_ball.mem_nhds (by rw [hy0]; exact hyb))
  have e5 : ∀ᶠ ψ in 𝓝 φ₀, ‖κx ψ - x‖ < δ := by
    have := hcx.preimage_mem_nhds (isOpen_ball.mem_nhds (show κx φ₀ ∈ ball x δ by
      rw [hx0]; exact mem_ball_self hδpos))
    filter_upwards [this] with ψ hψ
    simpa [dist_eq_norm, Set.mem_preimage, mem_ball] using hψ
  have e6 : ∀ᶠ ψ in 𝓝 φ₀, ‖κy ψ - y‖ < δ := by
    have := hcy.preimage_mem_nhds (isOpen_ball.mem_nhds (show κy φ₀ ∈ ball y δ by
      rw [hy0]; exact mem_ball_self hδpos))
    filter_upwards [this] with ψ hψ
    simpa [dist_eq_norm, Set.mem_preimage, mem_ball] using hψ
  have e7 : ∀ᶠ ψ in 𝓝 φ₀, ‖muSeq ψ m - muSeq φ₀ m‖ < δ := by
    have := hcμ.preimage_mem_nhds (isOpen_ball.mem_nhds (show muSeq φ₀ m ∈ ball (muSeq φ₀ m) δ from
      mem_ball_self hδpos))
    filter_upwards [this] with ψ hψ
    simpa [dist_eq_norm, Set.mem_preimage, mem_ball] using hψ
  have hev := e1.and (e2.and (e3.and (e4.and (e5.and (e6.and e7)))))
  obtain ⟨r, hr, hrT⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ball φ₀ r, isOpen_ball, (convex_ball φ₀ r).isConnected ⟨φ₀, mem_ball_self hr⟩,
    mem_ball_self hr, ?_, κx, κy, hκx.mono (fun ψ hψ => (hrT (mem_ball.mp hψ)).1),
    hκy.mono (fun ψ hψ => (hrT (mem_ball.mp hψ)).1), ?_⟩
  · intro ψ hψ
    exact hVgk ψ (hrT (mem_ball.mp hψ)).2.1
  · intro ψ hψ
    obtain ⟨hU', hball, hxbψ, hybψ, hdx, hdy, hdμ⟩ := hrT (mem_ball.mp hψ)
    have hroots := hspec ψ hball
    have hlx := root_mem_labels ψ C R hRpos hroots m (κx ψ) hxbψ (hrx ψ hU')
    have hly := root_mem_labels ψ C R hRpos hroots m (κy ψ) hybψ (hry ψ hU')
    have hdiff : κx ψ ≠ κy ψ := by
      intro h
      have h1 : ‖y - x‖ ≤ ‖κy ψ - y‖ + ‖κx ψ - x‖ := by
        have e : y - x = -(κy ψ - y) + (κx ψ - x) := by rw [h]; ring
        calc ‖y - x‖ = ‖-(κy ψ - y) + (κx ψ - x)‖ := by rw [← e]
          _ ≤ ‖-(κy ψ - y)‖ + ‖κx ψ - x‖ := norm_add_le _ _
          _ = _ := by rw [norm_neg]
      linarith
    have hdisj : (κx ψ = lamMinus ψ m ∧ κy ψ = lamPlus ψ m) ∨
        (κx ψ = lamPlus ψ m ∧ κy ψ = lamMinus ψ m) := by
      rcases hlx with h | h
      · rcases hly with h' | h'
        · exact absurd (h.trans h'.symm) hdiff
        · exact Or.inl ⟨h, h'⟩
      · rcases hly with h' | h'
        · exact Or.inr ⟨h, h'⟩
        · exact absurd (h.trans h'.symm) hdiff
    have hgapψ : ‖lamPlus ψ m - lamMinus ψ m‖ = ‖κy ψ - κx ψ‖ := by
      rcases hdisj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]
      · rw [← h1, ← h2, norm_sub_rev]
    refine ⟨hdisj, fun t ht => ?_⟩
    rw [hgapψ]
    have hbase := NlsGge.Atomic.G3.nearest_endpoint_segment x y (muSeq φ₀ m) t hxy hnear ht
    have key : κy ψ - ((t : ℂ) * muSeq ψ m + (1 - (t : ℂ)) * κx ψ) =
        (y - (x + (t : ℂ) * (muSeq φ₀ m - x))) + (κy ψ - y) - (1 - (t : ℂ)) * (κx ψ - x)
          - (t : ℂ) * (muSeq ψ m - muSeq φ₀ m) := by ring
    have ht1 : ‖(t : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; exact ht.2
    have ht2 : ‖(1 - (t : ℂ))‖ ≤ 1 := by
      have : (1 - (t : ℂ)) = ((1 - t : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
      linarith [ht.1]
    have hA : ‖(1 - (t : ℂ)) * (κx ψ - x)‖ ≤ ‖κx ψ - x‖ := by
      rw [norm_mul]
      calc ‖(1 - (t : ℂ))‖ * ‖κx ψ - x‖ ≤ 1 * ‖κx ψ - x‖ :=
            mul_le_mul_of_nonneg_right ht2 (norm_nonneg _)
        _ = ‖κx ψ - x‖ := one_mul _
    have hB : ‖(t : ℂ) * (muSeq ψ m - muSeq φ₀ m)‖ ≤ ‖muSeq ψ m - muSeq φ₀ m‖ := by
      rw [norm_mul]
      calc ‖(t : ℂ)‖ * ‖muSeq ψ m - muSeq φ₀ m‖ ≤ 1 * ‖muSeq ψ m - muSeq φ₀ m‖ :=
            mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
        _ = ‖muSeq ψ m - muSeq φ₀ m‖ := one_mul _
    have hZ : ‖y - (x + (t : ℂ) * (muSeq φ₀ m - x))‖ ≤
        ‖κy ψ - ((t : ℂ) * muSeq ψ m + (1 - (t : ℂ)) * κx ψ)‖ + ‖κy ψ - y‖ +
          ‖(1 - (t : ℂ)) * (κx ψ - x)‖ + ‖(t : ℂ) * (muSeq ψ m - muSeq φ₀ m)‖ := by
      have e : y - (x + (t : ℂ) * (muSeq φ₀ m - x)) =
          (κy ψ - ((t : ℂ) * muSeq ψ m + (1 - (t : ℂ)) * κx ψ)) - (κy ψ - y) +
            (1 - (t : ℂ)) * (κx ψ - x) + (t : ℂ) * (muSeq ψ m - muSeq φ₀ m) := by ring
      rw [e]
      calc _ ≤ ‖(κy ψ - ((t : ℂ) * muSeq ψ m + (1 - (t : ℂ)) * κx ψ)) - (κy ψ - y) +
            (1 - (t : ℂ)) * (κx ψ - x)‖ + ‖(t : ℂ) * (muSeq ψ m - muSeq φ₀ m)‖ := norm_add_le _ _
        _ ≤ (‖(κy ψ - ((t : ℂ) * muSeq ψ m + (1 - (t : ℂ)) * κx ψ)) - (κy ψ - y)‖ +
            ‖(1 - (t : ℂ)) * (κx ψ - x)‖) + ‖(t : ℂ) * (muSeq ψ m - muSeq φ₀ m)‖ := by
              gcongr; exact norm_add_le _ _
        _ ≤ ((‖κy ψ - ((t : ℂ) * muSeq ψ m + (1 - (t : ℂ)) * κx ψ)‖ + ‖κy ψ - y‖) +
            ‖(1 - (t : ℂ)) * (κx ψ - x)‖) + ‖(t : ℂ) * (muSeq ψ m - muSeq φ₀ m)‖ := by
              gcongr; exact norm_sub_le _ _
        _ = _ := by ring
    have hY : ‖κy ψ - κx ψ‖ ≤ ‖y - x‖ + ‖κy ψ - y‖ + ‖κx ψ - x‖ := by
      have e : κy ψ - κx ψ = (y - x) + (κy ψ - y) - (κx ψ - x) := by ring
      rw [e]
      calc _ ≤ ‖(y - x) + (κy ψ - y)‖ + ‖κx ψ - x‖ := norm_sub_le _ _
        _ ≤ (‖y - x‖ + ‖κy ψ - y‖) + ‖κx ψ - x‖ := by gcongr; exact norm_add_le _ _
    have hδ' : δ = ‖y - x‖ / 24 := hδ
    linarith [hZ, hY, hA, hB, hdx, hdy, hdμ, hbase, hδ']

theorem G3013_main (m : ℤ) (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW)
    (hZ : lamPlus φ₀ m ≠ lamMinus φ₀ m)
    (hE : muSeq φ₀ m ≠ lamMinus φ₀ m ∧ muSeq φ₀ m ≠ lamPlus φ₀ m) : ((
    ∃ V : Set PotPair, IsOpen V ∧ IsConnected V ∧ φ₀ ∈ V ∧ V ⊆ gkW ∧
      ∃ ρm ρp : PotPair → ℂ, AnalyticOnNhd ℂ ρm V ∧ AnalyticOnNhd ℂ ρp V ∧
        ∀ ψ ∈ V,
          ((ρm ψ = lamMinus ψ m ∧ ρp ψ = lamPlus ψ m) ∨
            (ρm ψ = lamPlus ψ m ∧ ρp ψ = lamMinus ψ m)) ∧
          ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
            ‖lamPlus ψ m - lamMinus ψ m‖ / 3 ≤
              ‖ρp ψ - ((t : ℂ) * muSeq ψ m + (1 - (t : ℂ)) * ρm ψ)‖
  : Prop)) := by
  have hcert := hφ₀
  obtain ⟨u, ρ, ⟨hρ, C, R, c, N, hg, hspec⟩, hmem⟩ := hcert
  have hRpos : ∀ n, 0 < R n := fun n => (hg.1 n).1
  have ha : lamMinus φ₀ m ∈ ball (C m) (R m) := ((hspec φ₀ hmem).1 m).1 (left_mem_segment ℝ _ _)
  have hb : lamPlus φ₀ m ∈ ball (C m) (R m) := ((hspec φ₀ hmem).1 m).1 (right_mem_segment ℝ _ _)
  obtain ⟨κa, Ua, hUa, hφUa, hκa, hκa0, hra⟩ :=
    exists_endpoint_branch φ₀ hφ₀ m hZ (lamMinus φ₀ m) (Or.inl rfl)
  obtain ⟨κb, Ub, hUb, hφUb, hκb, hκb0, hrb⟩ :=
    exists_endpoint_branch φ₀ hφ₀ m hZ (lamPlus φ₀ m) (Or.inr rfl)
  have hab : lamMinus φ₀ m ≠ lamPlus φ₀ m := fun h => hZ h.symm
  have hVgk : ∀ ψ ∈ ball (realSlice u) ρ, ψ ∈ gkW :=
    fun ψ hψ => ⟨u, ρ, ⟨hρ, C, R, c, N, hg, hspec⟩, hψ⟩
  rcases le_total ‖muSeq φ₀ m - lamMinus φ₀ m‖ ‖muSeq φ₀ m - lamPlus φ₀ m‖ with hle | hle
  · exact finish_core m φ₀ u ρ C R hRpos hVgk hspec hmem hφ₀ _ _ hab hle ha hb
      κa κb (Ua ∩ Ub) (hUa.inter hUb) ⟨hφUa, hφUb⟩ (hκa.mono inter_subset_left)
      (hκb.mono inter_subset_right) hκa0 hκb0 (fun ψ hψ => hra ψ hψ.1) (fun ψ hψ => hrb ψ hψ.2)
  · exact finish_core m φ₀ u ρ C R hRpos hVgk hspec hmem hφ₀ _ _ hab.symm hle hb ha
      κb κa (Ub ∩ Ua) (hUb.inter hUa) ⟨hφUb, hφUa⟩ (hκb.mono inter_subset_left)
      (hκa.mono inter_subset_right) hκb0 hκa0 (fun ψ hψ => hrb ψ hψ.1) (fun ψ hψ => hra ψ hψ.2)

end

end NlsGge.Atomic.G3013S3
