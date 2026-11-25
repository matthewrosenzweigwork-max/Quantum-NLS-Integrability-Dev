import Mathlib
import NlsGge.GK38.Lib.Rouche

/-!
# M-029 support: exact two-zero factorization (proof development, AUTHOR; not self-reviewed)

Pure complex-analysis support for `schur_has_two_roots`: (a) a homotopy/Rouche count of exactly two zeros
(`card_two`, from `zeroCount_locallyConstant`), (b) an order-tracking factorization of an analytic function with
exactly two zeros (with multiplicity) in a disc and no other zero on a set (`factor_two`).
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M029C

open Complex Metric Set Filter Topology
open NlsGge.GK38.Lib

theorem analyticOnNhd_dslope {f : ℂ → ℂ} {S : Set ℂ} (hf : AnalyticOnNhd ℂ f S) (ξ : ℂ) :
    AnalyticOnNhd ℂ (dslope f ξ) S := by
  intro z hz
  by_cases hzξ : z = ξ
  · subst hzξ
    have hU : {y | AnalyticAt ℂ f y} ∈ 𝓝 z := (hf z hz).eventually_analyticAt
    have hdiff : DifferentiableOn ℂ f {y | AnalyticAt ℂ f y} := fun y hy =>
      hy.differentiableAt.differentiableWithinAt
    exact ((differentiableOn_dslope hU).2 hdiff).analyticAt hU
  · have h1 : dslope f ξ =ᶠ[𝓝 z] fun y => (f y - f ξ) / (y - ξ) := by
      filter_upwards [dslope_eventuallyEq_slope_of_ne f hzξ] with y hy
      rw [hy, slope_def_field]
    refine AnalyticAt.congr ?_ h1.symm
    exact ((hf z hz).sub analyticAt_const).div (analyticAt_id.sub analyticAt_const)
      (sub_ne_zero.2 hzξ)

theorem eq_sub_mul_dslope (f : ℂ → ℂ) (ξ : ℂ) (h : f ξ = 0) (z : ℂ) :
    f z = (z - ξ) * dslope f ξ z := by
  have := sub_smul_dslope f ξ z
  rw [smul_eq_mul, h, sub_zero] at this
  exact this.symm

theorem analyticOrderAt_sub_const (ξ z : ℂ) :
    analyticOrderAt (fun y : ℂ => y - ξ) z = if z = ξ then 1 else 0 := by
  split_ifs with h
  · subst h
    have := (analyticAt_id (𝕜 := ℂ) (z := z)).analyticOrderAt_sub_eq_one_of_deriv_ne_zero
      (by simp)
    simpa using this
  · have : AnalyticAt ℂ (fun y : ℂ => y - ξ) z := analyticAt_id.sub analyticAt_const
    rw [this.analyticOrderAt_eq_zero]
    exact sub_ne_zero.2 h

theorem dslope_step {h : ℂ → ℂ} {S : Set ℂ} (hh : AnalyticOnNhd ℂ h S) (ξ : ℂ) (h0 : h ξ = 0)
    (k : ℂ → ℕ) (hk : ∀ z ∈ S, analyticOrderAt h z = (k z : ℕ∞)) :
    ∀ z ∈ S, analyticOrderAt (dslope h ξ) z = ((k z - if z = ξ then 1 else 0 : ℕ) : ℕ∞) := by
  intro z hz
  have hfun : h = (fun y : ℂ => y - ξ) * dslope h ξ :=
    funext fun y => eq_sub_mul_dslope h ξ h0 y
  have hA : AnalyticAt ℂ (fun y : ℂ => y - ξ) z := analyticAt_id.sub analyticAt_const
  have hB : AnalyticAt ℂ (dslope h ξ) z := analyticOnNhd_dslope hh ξ z hz
  have hm := analyticOrderAt_mul hA hB
  rw [← hfun, hk z hz, analyticOrderAt_sub_const] at hm
  generalize analyticOrderAt (dslope h ξ) z = o at hm ⊢
  induction o using ENat.recTopCoe with
  | top =>
    exfalso
    simp at hm
  | coe m =>
    by_cases hzξ : z = ξ
    · subst hzξ
      rw [if_pos rfl] at hm ⊢
      have : k z = 1 + m := by exact_mod_cast hm
      rw [this]
      simp
    · rw [if_neg hzξ] at hm ⊢
      have : k z = 0 + m := by exact_mod_cast hm
      rw [this]
      simp

theorem factor_two {f : ℂ → ℂ} {S : Set ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f S) (hball : closedBall c R ⊆ S)
    (hout : ∀ z ∈ S, z ∉ ball c R → f z ≠ 0)
    (ξ1 ξ2 : ℂ) (hM : zeroMultiset f (ball c R) = {ξ1, ξ2}) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g S ∧ (∀ z ∈ S, g z ≠ 0) ∧
      ∀ z, f z = (z - ξ1) * (z - ξ2) * g z := by
  classical
  have hfc : AnalyticOnNhd ℂ f (closedBall c R) := hf.mono hball
  have hbS : ball c R ⊆ S := ball_subset_closedBall.trans hball
  have hw : ∃ w ∈ closedBall c R, f w ≠ 0 := by
    refine ⟨c + R, ?_, ?_⟩
    · simp [abs_of_pos hR]
    · refine hout _ (hball (by simp [abs_of_pos hR])) ?_
      simp [abs_of_pos hR]
  have hmem1 : ξ1 ∈ ball c R := by
    have : ξ1 ∈ zeroMultiset f (ball c R) := by rw [hM]; simp
    exact ((mem_zeroMultiset_ball hfc).1 this).1
  have hmem2 : ξ2 ∈ ball c R := by
    have : ξ2 ∈ zeroMultiset f (ball c R) := by rw [hM]; simp
    exact ((mem_zeroMultiset_ball hfc).1 this).1
  have hfin : ∀ z ∈ ball c R, analyticOrderAt f z ≠ ⊤ := by
    intro z hz htop
    obtain ⟨w, hwm, hwne⟩ := hw
    have hev : f =ᶠ[𝓝 z] 0 := by
      have := analyticOrderAt_eq_top.1 htop
      exact this
    have := hfc.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_closedBall c R).isPreconnected (ball_subset_closedBall hz) hev hwm
    exact hwne this
  have hord : ∀ z ∈ S, analyticOrderAt f z =
      (((if z = ξ1 then 1 else 0) + (if z = ξ2 then 1 else 0) : ℕ) : ℕ∞) := by
    intro z hz
    by_cases hzb : z ∈ ball c R
    · have hc := count_zeroMultiset_ball hfc z
      rw [hM, if_pos hzb] at hc
      have hc' : (if z = ξ1 then 1 else 0) + (if z = ξ2 then 1 else 0) =
          analyticOrderNatAt f z := by
        rw [← hc]
        simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
        by_cases a : z = ξ1
        · subst a
          by_cases b : z = ξ2
          · subst b; simp
          · simp [b]
        · by_cases b : z = ξ2
          · subst b; simp [a]
          · simp [a, b]
      rw [hc']
      unfold analyticOrderNatAt
      exact (ENat.natCast_toNat (hfin z hzb)).symm
    · have h0 : analyticOrderAt f z = 0 := (hf z hz).analyticOrderAt_eq_zero.2 (hout z hz hzb)
      have a : z ≠ ξ1 := fun e => hzb (e ▸ hmem1)
      have b : z ≠ ξ2 := fun e => hzb (e ▸ hmem2)
      simp [h0, a, b]
  set e : ℂ → ℕ := fun z => (if z = ξ1 then 1 else 0) + (if z = ξ2 then 1 else 0) with he
  have hord' : ∀ z ∈ S, analyticOrderAt f z = (e z : ℕ∞) := hord
  have hf1 : f ξ1 = 0 := by
    have hz := hbS hmem1
    refine ((hf ξ1 hz).analyticOrderAt_ne_zero).1 ?_
    rw [hord' ξ1 hz]
    simp [he]
  have h1ord := dslope_step hf ξ1 hf1 e hord'
  obtain ⟨h1, hh1⟩ : ∃ h1 : ℂ → ℂ, h1 = dslope f ξ1 := ⟨_, rfl⟩
  rw [← hh1] at h1ord
  have h1an : AnalyticOnNhd ℂ h1 S := hh1 ▸ analyticOnNhd_dslope hf ξ1
  have h12 : h1 ξ2 = 0 := by
    have hz := hbS hmem2
    refine ((h1an ξ2 hz).analyticOrderAt_ne_zero).1 ?_
    rw [h1ord ξ2 hz]
    by_cases hq : ξ2 = ξ1 <;> simp [he, hq]
  have h2ord := dslope_step h1an ξ2 h12 (fun z => e z - if z = ξ1 then 1 else 0) h1ord
  obtain ⟨g, hg⟩ : ∃ g : ℂ → ℂ, g = dslope h1 ξ2 := ⟨_, rfl⟩
  rw [← hg] at h2ord
  have gan : AnalyticOnNhd ℂ g S := hg ▸ analyticOnNhd_dslope h1an ξ2
  refine ⟨g, gan, ?_, ?_⟩
  · intro z hz
    refine ((gan z hz).analyticOrderAt_eq_zero).1 ?_
    rw [h2ord z hz]
    have : (e z - (if z = ξ1 then 1 else 0) - (if z = ξ2 then 1 else 0) : ℕ) = 0 := by
      simp only [he]; omega
    rw [this]; rfl
  · intro z
    have e1 : f z = (z - ξ1) * h1 z := by
      rw [hh1]; exact eq_sub_mul_dslope f ξ1 hf1 z
    have e2 : h1 z = (z - ξ2) * g z := by
      rw [hg]; exact eq_sub_mul_dslope h1 ξ2 h12 z
    rw [e1, e2]; ring

theorem card_two {c : ℂ} {R : ℝ} (hR : 0 < R) {a1 a2 b : ℂ → ℂ}
    (h1 : AnalyticOnNhd ℂ a1 (closedBall c R)) (h2 : AnalyticOnNhd ℂ a2 (closedBall c R))
    (h3 : AnalyticOnNhd ℂ b (closedBall c R))
    (hne : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z ∈ sphere c R,
      (z - c - (t : ℂ) * a1 z) * (z - c - (t : ℂ) * a2 z) - (t : ℂ) ^ 2 * b z ≠ 0) :
    Multiset.card (zeroMultiset
      (fun z => (z - c - a1 z) * (z - c - a2 z) - b z) (ball c R)) = 2 := by
  let F : Set.Icc (0 : ℝ) 1 → ℂ → ℂ := fun t z =>
    (z - c - ((t : ℝ) : ℂ) * a1 z) * (z - c - ((t : ℝ) : ℂ) * a2 z) - ((t : ℝ) : ℂ) ^ 2 * b z
  have hF : ∀ x, AnalyticOnNhd ℂ (F x) (closedBall c R) := by
    intro x z hz
    exact (((analyticAt_id.sub analyticAt_const).sub (analyticAt_const.mul (h1 z hz))).mul
      ((analyticAt_id.sub analyticAt_const).sub (analyticAt_const.mul (h2 z hz)))).sub
      (analyticAt_const.mul (h3 z hz))
  have hc1 : ContinuousOn a1 (closedBall c R) := h1.continuousOn
  have hc2 : ContinuousOn a2 (closedBall c R) := h2.continuousOn
  have hc3 : ContinuousOn b (closedBall c R) := h3.continuousOn
  have hcont : ContinuousOn (Function.uncurry F) (univ ×ˢ sphere c R) := by
    have hm : Set.MapsTo (fun p : Set.Icc (0 : ℝ) 1 × ℂ => p.2) (univ ×ˢ sphere c R)
        (closedBall c R) := fun p hp => sphere_subset_closedBall hp.2
    have e1 : ContinuousOn (fun p : Set.Icc (0 : ℝ) 1 × ℂ => a1 p.2) (univ ×ˢ sphere c R) :=
      hc1.comp continuousOn_snd hm
    have e2 : ContinuousOn (fun p : Set.Icc (0 : ℝ) 1 × ℂ => a2 p.2) (univ ×ˢ sphere c R) :=
      hc2.comp continuousOn_snd hm
    have e3 : ContinuousOn (fun p : Set.Icc (0 : ℝ) 1 × ℂ => b p.2) (univ ×ˢ sphere c R) :=
      hc3.comp continuousOn_snd hm
    have et : Continuous (fun p : Set.Icc (0 : ℝ) 1 × ℂ => ((p.1 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
    have es : Continuous (fun p : Set.Icc (0 : ℝ) 1 × ℂ => p.2) := continuous_snd
    unfold Function.uncurry F
    exact (((es.continuousOn.sub continuousOn_const).sub (et.continuousOn.mul e1)).mul
      ((es.continuousOn.sub continuousOn_const).sub (et.continuousOn.mul e2))).sub
      ((et.continuousOn.pow 2).mul e3)
  have hne' : ∀ x, ∀ z ∈ sphere c R, F x z ≠ 0 := fun x z hz => hne x x.2.1 x.2.2 z hz
  have hloc := zeroCount_locallyConstant hR hF hcont hne'
  have : PreconnectedSpace (Set.Icc (0 : ℝ) 1) :=
    Subtype.preconnectedSpace isPreconnected_Icc
  have h01 := hloc.apply_eq_of_preconnectedSpace ⟨1, by simp⟩ ⟨0, by simp⟩
  have eF1 : F ⟨1, by simp⟩ = fun z => (z - c - a1 z) * (z - c - a2 z) - b z := by
    funext z; simp [F]
  have eF0 : F ⟨0, by simp⟩ = fun z => (z - c) * (z - c) := by
    funext z; simp [F]
  rw [eF1, eF0] at h01
  rw [h01]
  have han : AnalyticOnNhd ℂ (fun z : ℂ => (z - c) * (z - c)) (closedBall c R) := fun z _ =>
    (analyticAt_id.sub analyticAt_const).mul (analyticAt_id.sub analyticAt_const)
  have hrep := zeroMultiset_ball_eq_replicate hR han (fun z _ hzc h0 => by
    rcases mul_eq_zero.1 h0 with h | h <;> exact hzc (sub_eq_zero.1 h))
  rw [hrep, Multiset.card_replicate]
  have hA : AnalyticAt ℂ (fun y : ℂ => y - c) c := analyticAt_id.sub analyticAt_const
  have hm := analyticOrderAt_mul hA hA
  have e : (fun z : ℂ => (z - c) * (z - c)) = (fun y : ℂ => y - c) * (fun y : ℂ => y - c) := rfl
  unfold analyticOrderNatAt
  rw [e, hm, analyticOrderAt_sub_const]
  simp
  rfl

end NlsGge.ThirdConsultation.M029C

end
