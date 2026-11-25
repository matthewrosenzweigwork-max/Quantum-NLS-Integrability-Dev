import Mathlib
import NlsGge.GK38.IsolatingFamily
import NlsGge.GK38.Lib.Rouche
import NlsGge.GK38.PeriodicLabellingFreeLabels
import NlsGge.GK38.ContourAction

                                                                                                     
                                                                      
                                                                                 
                                                                                                                
                                                                                                               
                                                                                                               
                                                                                                                 
                                                                                                                
                                    

set_option autoImplicit false
open Set Filter Topology Metric

namespace NlsGge.ThirdConsultation.M016ChartAux

open NlsGge.GK38

/-- Membership in the zero multiset on a disc, for a function analytic on the closed disc that does not vanish
identically there. -/
theorem mem_zeroMultiset_ball_iff {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c r)) {w : ℂ} (hw : w ∈ closedBall c r) (hfw : f w ≠ 0)
    (z : ℂ) : z ∈ Lib.zeroMultiset f (ball c r) ↔ z ∈ ball c r ∧ f z = 0 := by
  classical
  rw [← Multiset.count_pos, Lib.count_zeroMultiset_ball hf z]
  constructor
  · intro h
    by_cases hz : z ∈ ball c r
    · rw [ite_cond_eq_true _ _ (eq_true hz)] at h
      refine ⟨hz, ?_⟩
      by_contra hne
      have h0 : analyticOrderAt f z = 0 :=
        (hf z (ball_subset_closedBall hz)).analyticOrderAt_eq_zero.2 hne
      simp [analyticOrderNatAt, h0] at h
    · rw [ite_cond_eq_false _ _ (eq_false hz)] at h
      exact absurd h (lt_irrefl 0)
  · rintro ⟨hz, hfz⟩
    rw [ite_cond_eq_true _ _ (eq_true hz)]
    have hzc : z ∈ closedBall c r := ball_subset_closedBall hz
    have hne0 : analyticOrderAt f z ≠ 0 := fun h =>
      ((hf z hzc).analyticOrderAt_eq_zero.1 h) hfz
    have hnetop : analyticOrderAt f z ≠ ⊤ := by
      intro h
      have hev : f =ᶠ[𝓝 z] 0 := analyticOrderAt_eq_top.1 h
      have := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_closedBall c r).isPreconnected hzc hev hw
      exact hfw this
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hnetop
    rw [← hn] at hne0
    have hn0 : n ≠ 0 := fun h => hne0 (by simp [h])
    simp only [analyticOrderNatAt, ← hn, ENat.toNat_natCast]
    exact Nat.pos_of_ne_zero hn0

theorem perChar_eq_mul (φ : PotPair) (z : ℂ) :
    perChar φ z = (discrim φ z - 2) * (discrim φ z + 2) := by
  show discrim φ z ^ 2 - 4 = _
  ring

theorem analyticOnNhd_perChar (φ : PotPair) (s : Set ℂ) : AnalyticOnNhd ℂ (perChar φ) s := by
  have h : AnalyticOnNhd ℂ (fun z => discrim φ z ^ 2 - 4) univ :=
    ((analyticOnNhd_discrim_z φ).pow 2).sub analyticOnNhd_const
  exact fun z _ => h z (mem_univ z)

theorem analyticOnNhd_discrim_add_two (φ : PotPair) (s : Set ℂ) :
    AnalyticOnNhd ℂ (fun z => discrim φ z + 2) s := fun z _ =>
  ((analyticOnNhd_discrim_z φ).add analyticOnNhd_const) z (mem_univ z)

/-- **Count characterization.** In the `0`-th isolating disc, both base endpoint values are `+2` iff `Δ+2` has no
zero in the disc. -/
theorem base_sign_iff_card (ψ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ) (hR : 0 < R 0)
    (hspec : IsolatingSpectral38 ψ C R) :
    (discrim ψ (lamMinus ψ 0) = 2 ∧ discrim ψ (lamPlus ψ 0) = 2) ↔
      Multiset.card (Lib.zeroMultiset (fun z => discrim ψ z + 2) (ball (C 0) (R 0))) = 0 := by
  obtain ⟨w, hw⟩ := (NormedSpace.sphere_nonempty (x := C 0)).2 hR.le
  have hwc : w ∈ closedBall (C 0) (R 0) := sphere_subset_closedBall hw
  have hpw : perChar ψ w ≠ 0 := ((hspec.1 0).2.2.2.2.2.2.2.2.2.2.2.2 w hw).1
  have hmw : discrim ψ w + 2 ≠ 0 := by
    intro h; apply hpw; rw [perChar_eq_mul, h, mul_zero]
  have hmulti := (hspec.1 0).2.2.2.2.1
  have hperMem : ∀ z, z ∈ ball (C 0) (R 0) → perChar ψ z = 0 →
      z = lamMinus ψ 0 ∨ z = lamPlus ψ 0 := by
    intro z hz hpz
    have hm : z ∈ Lib.zeroMultiset (perChar ψ) (ball (C 0) (R 0)) :=
      (mem_zeroMultiset_ball_iff (analyticOnNhd_perChar ψ _) hwc hpw z).2 ⟨hz, hpz⟩
    rw [← hmulti] at hm
    simpa using hm
  have hendMem : ∀ z, (z = lamMinus ψ 0 ∨ z = lamPlus ψ 0) →
      z ∈ ball (C 0) (R 0) ∧ perChar ψ z = 0 := by
    intro z hz
    have hm : z ∈ (lamMinus ψ 0 ::ₘ lamPlus ψ 0 ::ₘ 0) := by
      rcases hz with h | h <;> simp [h]
    rw [hmulti] at hm
    exact (mem_zeroMultiset_ball_iff (analyticOnNhd_perChar ψ _) hwc hpw z).1 hm
  have hmem := mem_zeroMultiset_ball_iff (analyticOnNhd_discrim_add_two ψ _) hwc hmw
  rw [Multiset.card_eq_zero, Multiset.eq_zero_iff_forall_notMem]
  constructor
  · rintro ⟨h1, h2⟩ z hz
    obtain ⟨hzB, hz0⟩ := (hmem z).1 hz
    have hp : perChar ψ z = 0 := by rw [perChar_eq_mul, hz0, mul_zero]
    rcases hperMem z hzB hp with h | h
    · rw [h, h1] at hz0; norm_num at hz0
    · rw [h, h2] at hz0; norm_num at hz0
  · intro hnone
    have key : ∀ z, (z = lamMinus ψ 0 ∨ z = lamPlus ψ 0) → discrim ψ z = 2 := by
      intro z hz
      obtain ⟨hzB, hp⟩ := hendMem z hz
      rw [perChar_eq_mul] at hp
      rcases mul_eq_zero.1 hp with h | h
      · exact sub_eq_zero.1 h
      · exact absurd ((hmem z).2 ⟨hzB, h⟩) (hnone z)
    exact ⟨key _ (Or.inl rfl), key _ (Or.inr rfl)⟩

/-- The base-sign property is locally constant near every point of `gkW`. -/
theorem base_sign_eventually (φ₀ : PotPair) (h₀ : φ₀ ∈ gkW) :
    ∀ᶠ ψ in 𝓝 φ₀,
      ((discrim ψ (lamMinus ψ 0) = 2 ∧ discrim ψ (lamPlus ψ 0) = 2) ↔
        (discrim φ₀ (lamMinus φ₀ 0) = 2 ∧ discrim φ₀ (lamPlus φ₀ 0) = 2)) := by
  obtain ⟨V, hV, _, _, _, C, R, c, N, hgeom, hspec⟩ := local_isolatingFamily_common38 φ₀ h₀
  have hR : 0 < R 0 := (hgeom.1 0).1
  have hcont : ContinuousOn (Function.uncurry fun (x : PotPair) (z : ℂ) => discrim x z + 2)
      (univ ×ˢ sphere (C 0) (R 0)) := by
    have hc : Continuous fun p : PotPair × ℂ => discrim p.1 p.2 :=
      continuousOn_univ.1 analyticOnNhd_discrim.continuousOn
    exact (hc.add continuous_const).continuousOn
  have hne : ∀ z ∈ sphere (C 0) (R 0), discrim φ₀ z + 2 ≠ 0 := by
    intro z hz h
    apply ((hspec φ₀ (mem_of_mem_nhds hV)).1 0).2.2.2.2.2.2.2.2.2.2.2.2 z hz |>.1
    rw [perChar_eq_mul, h, mul_zero]
  have hev := Lib.eventually_card_zeroMultiset_eq (F := fun (x : PotPair) (z : ℂ) => discrim x z + 2)
    hR (fun x => analyticOnNhd_discrim_add_two x _) hcont φ₀ hne
  filter_upwards [hev, hV] with ψ hψ hψV
  rw [base_sign_iff_card ψ C R hR (hspec ψ hψV), hψ,
    ← base_sign_iff_card φ₀ C R hR (hspec φ₀ (mem_of_mem_nhds hV))]

theorem base_sign_vacuum :
    GK38.discrim 0 (lamMinus 0 0) = 2 ∧ GK38.discrim 0 (lamPlus 0 0) = 2 := by
  refine ⟨?_, ?_⟩
  · rw [lamMinus_zero38, discrim_zero]; simp [countingCenter38]
  · rw [lamPlus_zero38, discrim_zero]; simp [countingCenter38]

/-- **(S4c).** Both base periodic endpoints carry discriminant value `+2`, on all of `gkW`. -/
theorem discrim_base_endpoints (φ : PotPair) (hφ : φ ∈ gkW) :
    discrim φ (lamMinus φ 0) = 2 ∧ discrim φ (lamPlus φ 0) = 2 := by
  let f : gkW → Prop := fun ψ =>
    discrim ψ.1 (lamMinus ψ.1 0) = 2 ∧ discrim ψ.1 (lamPlus ψ.1 0) = 2
  have hf : IsLocallyConstant f := by
    refine (IsLocallyConstant.iff_eventually_eq f).2 fun x => ?_
    have h := (continuous_subtype_val.tendsto x).eventually (base_sign_eventually x.1 x.2)
    filter_upwards [h] with y hy
    exact propext hy
  have : PreconnectedSpace gkW := Subtype.preconnectedSpace isConnected_gkW38.isPreconnected
  have heq : f ⟨φ, hφ⟩ = f ⟨0, free_mem_gkW⟩ :=
    hf.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial
  have h0 : f ⟨0, free_mem_gkW⟩ := base_sign_vacuum
  rw [← heq] at h0
  exact h0

/-- **(S4c), stated as in M016CHART_STOP.md.** -/
theorem discrim_lamMinus_zero (φ : PotPair) (hφ : φ ∈ gkW) : discrim φ (lamMinus φ 0) = 2 :=
  (discrim_base_endpoints φ hφ).1

theorem discrim_lamPlus_zero (φ : PotPair) (hφ : φ ∈ gkW) : discrim φ (lamPlus φ 0) = 2 :=
  (discrim_base_endpoints φ hφ).2

end NlsGge.ThirdConsultation.M016ChartAux
