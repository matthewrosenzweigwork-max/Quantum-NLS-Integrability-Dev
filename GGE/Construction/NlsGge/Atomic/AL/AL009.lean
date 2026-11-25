                                                                                                                                                                                                                               
import Mathlib
import NlsGge.Hierarchy.ALExteriorBranch38
import NlsGge.Hierarchy.ALComplexExteriorLog38
import NlsGge.Hierarchy.ALLaurent38
import NlsGge.Hierarchy.ALPoissonLiouville38
import NlsGge.Hierarchy.ALEnergyAnalytic38

                                                                                                                                       
                                                                                                                                    
                                                                                                                                 
                                                   
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.AblowitzLadik

namespace NlsGge.ThirdConsultation.AL
noncomputable section

namespace AL009Aux

theorem exists_radius {ι : Type*} (t : Finset ι) (ρ : ι → ℝ) (hρ : ∀ i ∈ t, 0 < ρ i) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ i ∈ t, r ≤ ρ i := by
  classical
  revert hρ
  induction t using Finset.induction_on with
  | empty => intro _; exact ⟨1 / 2, by norm_num, by norm_num, by simp⟩
  | insert a s ha ih =>
    intro hρ
    obtain ⟨r, hr0, hr1, hr⟩ := ih (fun i hi => hρ i (Finset.mem_insert_of_mem hi))
    refine ⟨min r (ρ a), lt_min hr0 (hρ a (Finset.mem_insert_self _ _)),
      (min_le_left _ _).trans_lt hr1, ?_⟩
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | h
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hr i h)

theorem roots_unique (w W tr : ℂ) (h1 : w ^ 2 - tr * w + 1 = 0) (h2 : W ^ 2 - tr * W + 1 = 0)
    (hw : 1 < ‖w‖) (hW : 1 < ‖W‖) : w = W := by
  by_contra hne
  have h3 : (w - W) * (w + W - tr) = 0 := by linear_combination h1 - h2
  have h4 : w + W - tr = 0 := by
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h
  have h5 : w * W = 1 := by
    have : tr = w + W := by linear_combination -h4
    rw [this] at h2
    linear_combination -h2
  have h6 : ‖w‖ * ‖W‖ = 1 := by rw [← norm_mul, h5, norm_one]
  nlinarith [norm_nonneg w, norm_nonneg W]

theorem sq_eq_D {L : ℕ} (a b : ZMod L → ℂ) (ζ : ℂ) :
    alComplexS38 a b ζ ^ 2 = alComplexD38 a b ζ := by
  unfold alComplexS38
  exact Complex.cpow_ofNat_inv_pow _ 2

theorem G_root {L : ℕ} (a b : ZMod L → ℂ) (ζ : ℂ) :
    (alComplexG38 a b ζ) ^ 2 - alComplexT38 a b ζ * alComplexG38 a b ζ + ζ ^ (2 * L) = 0 := by
  have hS := sq_eq_D a b ζ
  have hD : alComplexD38 a b ζ = alComplexT38 a b ζ ^ 2 - 4 * ζ ^ (2 * L) := rfl
  unfold alComplexG38
  rw [hD] at hS
  linear_combination (1 / 4 : ℂ) * hS

end AL009Aux

open AL009Aux in
theorem al009 {L : ℕ} [NeZero L] (α : ZMod L → ℂ)
    (hα : IsALField38 α) :
  AnalyticOnNhd ℂ (fun z => alExtW38 α z⁻¹) {z : ℂ | 1 < ‖z‖} ∧
  (∀ z : ℂ, 1 < ‖z‖ →
    (alExtW38 α z⁻¹)^2 - (alMonodromy38 α z).trace * alExtW38 α z⁻¹ + 1 = 0 ∧
    1 < ‖alExtW38 α z⁻¹‖ ∧ alExtW38 α z⁻¹ ≠ 0 ∧
    ∃ v : Fin 2 → ℂ, v ≠ 0 ∧
      (alMonodromy38 α z).mulVec v = alExtW38 α z⁻¹ • v) ∧
  (∀ w : ℂ → ℂ,
    AnalyticOnNhd ℂ w {z : ℂ | 1 < ‖z‖} →
    (∀ z : ℂ, 1 < ‖z‖ →
      w z^2 - (alMonodromy38 α z).trace*w z + 1 = 0 ∧ 1 < ‖w z‖) →
    Set.EqOn w (fun z => alExtW38 α z⁻¹) {z : ℂ | 1 < ‖z‖}) ∧
  (∀ K : Set (ZMod L → ℂ), IsCompact K → K ⊆ alDisk38 L →
    ∃ (U : Set ((ZMod L → ℂ) × (ZMod L → ℂ))) (r : ℝ),
      IsOpen U ∧ alIota38 '' K ⊆ U ∧ U ⊆ alComplexDomain38 L ∧ 0 < r ∧ r < 1 ∧
      AnalyticOnNhd ℂ
        (fun q : ℂ × ((ZMod L → ℂ) × (ZMod L → ℂ)) =>
          alComplexG38 q.2.1 q.2.2 q.1) (Metric.ball 0 r ×ˢ U) ∧
      (∀ p ∈ U, ∀ ζ ∈ Metric.ball (0 : ℂ) r,
        alComplexG38 p.1 p.2 ζ ≠ 0 ∧
        (alComplexG38 p.1 p.2 ζ)^2 -
          alComplexT38 p.1 p.2 ζ * alComplexG38 p.1 p.2 ζ + ζ^(2*L) = 0) ∧
      ∀ a : ZMod L → ℂ, IsALField38 a → alIota38 a ∈ U →
        ∀ ζ ∈ Metric.ball (0 : ℂ) r,
          alComplexG38 a (fun j => star (a j)) ζ = alExteriorG38 a ζ) := by
  -- facts for the exterior branch
  have hint : ∀ z : ℂ, 1 < ‖z‖ → z⁻¹ ∈ Metric.ball (0 : ℂ) 1 ∧ z⁻¹ ≠ 0 := by
    intro z hz
    have hz0 : z ≠ 0 := norm_pos_iff.1 (by linarith)
    refine ⟨?_, inv_ne_zero hz0⟩
    rw [mem_ball_zero_iff, norm_inv]
    exact inv_lt_one_of_one_lt₀ hz
  have hmul : ∀ z : ℂ, 1 < ‖z‖ →
      (alExtW38 α z⁻¹)^2 - (alMonodromy38 α z).trace * alExtW38 α z⁻¹ + 1 = 0 ∧
      1 < ‖alExtW38 α z⁻¹‖ ∧ alExtW38 α z⁻¹ ≠ 0 ∧
      ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ (alMonodromy38 α z).mulVec v = alExtW38 α z⁻¹ • v := by
    intro z hz
    obtain ⟨hb, h0⟩ := hint z hz
    obtain ⟨⟨v, hv, hev⟩, hroot, hn⟩ := alExteriorG38_multiplier hα hb h0
    have hzz : (z⁻¹)⁻¹ = z := inv_inv z
    rw [hzz] at hev hroot
    have hn' : 1 < ‖alExtW38 α z⁻¹‖ := hn
    refine ⟨hroot, hn', ?_, v, hv, hev⟩
    intro h
    rw [h, norm_zero] at hn'
    linarith
  refine ⟨?_, hmul, ?_, ?_⟩
  · intro z hz
    have hz1 : 1 < ‖z‖ := hz
    obtain ⟨hb, h0⟩ := hint z hz1
    have hz0 : z ≠ 0 := norm_pos_iff.1 (by linarith)
    have hinv : AnalyticAt ℂ (fun z : ℂ => z⁻¹) z := analyticAt_id.inv hz0
    have hG : AnalyticAt ℂ (alExteriorG38 α) z⁻¹ := (alExteriorG38_analytic hα) z⁻¹ hb
    have hpow : AnalyticAt ℂ (fun z : ℂ => (z⁻¹) ^ L) z := hinv.pow L
    have h2 : AnalyticAt ℂ (fun z : ℂ => ((z⁻¹) ^ L)⁻¹) z := hpow.inv (pow_ne_zero _ h0)
    exact h2.mul (hG.comp hinv)
  · intro w _ hw z hz
    have hz1 : 1 < ‖z‖ := hz
    obtain ⟨hr, hn, -, -⟩ := hmul z hz1
    obtain ⟨h1, h2⟩ := hw z hz1
    exact roots_unique (w z) _ _ h1 hr h2 hn
  · intro K hK hKd
    -- local data at each point of K
    have hloc : ∀ α₀ ∈ K, ∃ (U : Set ((ZMod L → ℂ) × (ZMod L → ℂ))) (ρ₁ : ℝ),
        IsOpen U ∧ (α₀, fun j => star (α₀ j)) ∈ U ∧ U ⊆ alComplexDomain38 L ∧
        0 < ρ₁ ∧ ρ₁ ≤ 1 ∧
        (∀ ζ ∈ Metric.ball (0 : ℂ) ρ₁, ∀ p ∈ U,
          alComplexD38 p.1 p.2 ζ ∈ Complex.slitPlane ∧ alComplexG38 p.1 p.2 ζ ∈ Complex.slitPlane) ∧
        (∀ ζ ∈ Metric.ball (0 : ℂ) ρ₁, ∀ p ∈ U,
          Complex.exp (alComplexLog38 p.1 p.2 ζ) = alComplexG38 p.1 p.2 ζ) ∧
        (∀ a : ZMod L → ℂ, IsALField38 a → (a, fun j => star (a j)) ∈ U →
          ∀ ζ ∈ Metric.ball (0 : ℂ) ρ₁, alComplexLog38 a (fun j => star (a j)) ζ = alLog38 a ζ) := by
      intro α₀ hα₀
      obtain ⟨U, ρ₁, h1, h2, h3, h4, h5, h6, -, h8, h9⟩ := exists_alComplexLogNhd38 (hKd hα₀)
      exact ⟨U, ρ₁, h1, h2, h3, h4, h5, h6, h8, h9⟩
    choose! U ρ hU using hloc
    -- finite subcover
    obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun α₀ => (alIota38 ⁻¹' (U α₀)))
      (fun α₀ hα₀ => ((hU α₀ hα₀).1.preimage alIota38.continuous).mem_nhds (by
        have := (hU α₀ hα₀).2.1
        simpa [alIota38_apply] using this))
    obtain ⟨r, hr0, hr1, hrle⟩ := exists_radius t ρ (fun i hi => (hU i (htK i hi)).2.2.2.1)
    refine ⟨⋃ i ∈ t, U i, r, ?_, ?_, ?_, hr0, hr1, ?_, ?_, ?_⟩
    · exact isOpen_biUnion fun i hi => (hU i (htK i hi)).1
    · intro p hp
      obtain ⟨a, haK, rfl⟩ := hp
      have := hcov haK
      simp only [mem_iUnion, mem_preimage, exists_prop] at this
      obtain ⟨i, hi, hai⟩ := this
      exact mem_biUnion hi hai
    · intro p hp
      simp only [mem_iUnion, exists_prop] at hp
      obtain ⟨i, hi, hpi⟩ := hp
      exact (hU i (htK i hi)).2.2.1 hpi
    · intro q hq
      obtain ⟨hqζ, hqp⟩ := hq
      simp only [mem_iUnion, exists_prop] at hqp
      obtain ⟨i, hi, hpi⟩ := hqp
      have hρ : Metric.ball (0 : ℂ) r ⊆ Metric.ball 0 (ρ i) := Metric.ball_subset_ball (hrle i hi)
      have hd := (hU i (htK i hi)).2.2.1 hpi
      have hD := ((hU i (htK i hi)).2.2.2.2.2.1 q.1 (hρ hqζ) q.2 hpi).1
      exact analyticAt_alComplexG38 (q.1, q.2) hd hD
    · intro p hp ζ hζ
      simp only [mem_iUnion, exists_prop] at hp
      obtain ⟨i, hi, hpi⟩ := hp
      have hρ : Metric.ball (0 : ℂ) r ⊆ Metric.ball 0 (ρ i) := Metric.ball_subset_ball (hrle i hi)
      have hG := ((hU i (htK i hi)).2.2.2.2.2.1 ζ (hρ hζ) p hpi).2
      exact ⟨Complex.slitPlane_ne_zero hG, G_root p.1 p.2 ζ⟩
    · intro a ha haU ζ hζ
      simp only [alIota38_apply, mem_iUnion, exists_prop] at haU
      obtain ⟨i, hi, hai⟩ := haU
      have hρ : Metric.ball (0 : ℂ) r ⊆ Metric.ball 0 (ρ i) := Metric.ball_subset_ball (hrle i hi)
      have hb1 : ζ ∈ Metric.ball (0 : ℂ) 1 := Metric.ball_subset_ball hr1.le hζ
      have e1 := (hU i (htK i hi)).2.2.2.2.2.2.1 ζ (hρ hζ) _ hai
      have e2 := (hU i (htK i hi)).2.2.2.2.2.2.2 a ha hai ζ (hρ hζ)
      rw [← e1]
      simp only at e1 ⊢
      rw [e2]
      exact (alLog38_spec ha).2.1 ζ hb1

end
end NlsGge.ThirdConsultation.AL
