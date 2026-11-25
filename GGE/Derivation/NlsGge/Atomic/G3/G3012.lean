/- G3-012 PRODUCTION01 (proof development landing kit; HELD for landing). Source: proof development/G3012_PROOF03.lean.txt (author proof development; proof review proof development G3-012_G3-013_PROOF_REVIEW01.md). #print axioms lines removed; nothing else changed. Target NlsGge/Atomic/G3/G3012.lean. -/
import Mathlib
import NlsGge.GK38.AngleEndpointVariety
import NlsGge.GK38.RealTypeSpectrumSigns
import NlsGge.GK38.Lib.Rouche
import NlsGge.GK38.IsolatingFamily

set_option autoImplicit false

/-! G3-012 (proof development, AUTHOR; not self-reviewed; no acceptance claimed).
Exceptional sets are analytic zero sets, for the house almost-real domain `gkW`.
Z_m = {phi in gkW | gamma_m = 0} = {gamma_m^2 = 0} with `gamma_m^2 = (lamPlus - lamMinus)^2`,
E_m = {phi in gkW | mu_m in {lamMinus, lamPlus}} = {Delta(mu_m) = 2 (-1)^m} = zero set of the analytic function
`Delta(phi, mu_m(phi)) - 2 (-1)^m`.
Route for E_m: the detector `perChar(mu_m)` of `AngleEndpointVariety.lean` gives the endpoint implication; the sign
`Delta(lamMinus), Delta(lamPlus) = 2 (-1)^m` for complex phi in a certified ball is proved by local constancy
(`Lib.zeroCount_locallyConstant`, Rouche) of the zero count of `Delta - s` on the connected ball, from the real centre
(`periodic_real_pair_signs38`). -/

namespace NlsGge.Atomic.G3012S3

open Filter Topology Set Metric
open NlsGge.GK38 NlsGge.Pilot

noncomputable section

theorem zeroMultiset_pm_split (D : ℂ → ℂ) (hD : AnalyticOnNhd ℂ D univ) (s : ℂ) (hs : s ^ 2 = 4)
    (c : ℂ) (R : ℝ) (hR : 0 < R) (hne : ∀ z ∈ sphere c R, D z ^ 2 - 4 ≠ 0) :
    Lib.zeroMultiset (fun z => D z ^ 2 - 4) (ball c R) =
      Lib.zeroMultiset (fun z => D z - s) (ball c R) +
        Lib.zeroMultiset (fun z => D z + s) (ball c R) := by
  classical
  have hf : AnalyticOnNhd ℂ (fun z => D z - s) (closedBall c R) :=
    (hD.sub analyticOnNhd_const).mono (subset_univ _)
  have hg : AnalyticOnNhd ℂ (fun z => D z + s) (closedBall c R) :=
    (hD.add analyticOnNhd_const).mono (subset_univ _)
  have hp : AnalyticOnNhd ℂ (fun z => D z ^ 2 - 4) (closedBall c R) :=
    ((hD.pow 2).sub analyticOnNhd_const).mono (subset_univ _)
  have hprod : (fun z => D z ^ 2 - 4) = (fun z => D z - s) * (fun z => D z + s) := by
    funext z
    simp only [Pi.mul_apply]
    linear_combination hs
  obtain ⟨w, hw⟩ : (sphere c R).Nonempty := NormedSpace.sphere_nonempty.mpr hR.le
  have hwB := sphere_subset_closedBall hw
  have hw0 : D w ^ 2 - 4 ≠ 0 := hne w hw
  have hfw : D w - s ≠ 0 := fun h => hw0 (by
    have : D w = s := sub_eq_zero.mp h
    rw [this]; linear_combination hs)
  have hgw : D w + s ≠ 0 := fun h => hw0 (by
    have : D w = -s := eq_neg_of_add_eq_zero_left h
    rw [this]; linear_combination hs)
  have hfin : ∀ (F : ℂ → ℂ), AnalyticOnNhd ℂ F (closedBall c R) → F w ≠ 0 →
      ∀ z ∈ closedBall c R, analyticOrderAt F z ≠ ⊤ := by
    intro F hF hFw z hz
    refine hF.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall c R).isPreconnected
      hwB hz ?_
    rw [(hF w hwB).analyticOrderAt_eq_zero.2 hFw]
    exact ENat.zero_ne_top
  refine Multiset.ext' fun z => ?_
  rw [Multiset.count_add, Lib.count_zeroMultiset_ball hp, Lib.count_zeroMultiset_ball hf,
    Lib.count_zeroMultiset_ball hg]
  by_cases hz : z ∈ ball c R
  · simp only [if_pos hz]
    have hzB := ball_subset_closedBall hz
    rw [hprod]
    exact analyticOrderNatAt_mul (hf z hzB) (hg z hzB) (hfin _ hf hfw z hzB) (hfin _ hg hgw z hzB)
  · simp [hz]

theorem neg_one_zpow_cases (m : ℤ) : (-1 : ℂ) ^ m = 1 ∨ (-1 : ℂ) ^ m = -1 := by
  rcases Int.even_or_odd m with h | h
  · exact Or.inl h.neg_one_zpow
  · exact Or.inr h.neg_one_zpow

theorem sign_on_certified_ball (u : PhysicalL2) (ρ : ℝ) (hρ : 0 < ρ) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hRpos : ∀ n, 0 < R n)
    (hspec : ∀ φ ∈ ball (realSlice u) ρ, IsolatingSpectral38 φ C R) (m : ℤ) :
    ∀ φ ∈ ball (realSlice u) ρ,
      NlsGge.GK38.discrim φ (lamMinus φ m) = 2 * (-1 : ℂ) ^ m ∧
      NlsGge.GK38.discrim φ (lamPlus φ m) = 2 * (-1 : ℂ) ^ m := by
  set s : ℂ := 2 * (-1 : ℂ) ^ m with hsdef
  have hs2 : s ^ 2 = 4 := by
    rcases neg_one_zpow_cases m with h | h <;> rw [hsdef, h] <;> norm_num
  have hs0 : s ≠ 0 := by
    intro h
    have := hs2
    rw [h] at this
    norm_num at this
  have hsphere : ∀ ψ ∈ ball (realSlice u) ρ, ∀ z ∈ sphere (C m) (R m), perChar ψ z ≠ 0 :=
    fun ψ hψ z hz => (((hspec ψ hψ).1 m).2.2.2.2.2.2.2.2.2.2.2.2 z hz).1
  have hsplit : ∀ ψ ∈ ball (realSlice u) ρ,
      Lib.zeroMultiset (perChar ψ) (ball (C m) (R m)) =
        Lib.zeroMultiset (fun z => NlsGge.GK38.discrim ψ z - s) (ball (C m) (R m)) +
          Lib.zeroMultiset (fun z => NlsGge.GK38.discrim ψ z + s) (ball (C m) (R m)) :=
    fun ψ hψ => zeroMultiset_pm_split (NlsGge.GK38.discrim ψ) (analyticOnNhd_discrim_z ψ) s hs2
      (C m) (R m) (hRpos m) (hsphere ψ hψ)
  have hd : Continuous (fun p : PotPair × ℂ => NlsGge.GK38.discrim p.1 p.2) :=
    continuousOn_univ.mp analyticOnNhd_discrim.continuousOn
  let X := ↥(ball (realSlice u) ρ)
  let F : X → ℂ → ℂ := fun x z => NlsGge.GK38.discrim x.1 z - s
  have hcont : Continuous (Function.uncurry F) := by
    have h : Continuous (fun p : X × ℂ => NlsGge.GK38.discrim p.1.1 p.2 - s) :=
      (hd.comp (continuous_subtype_val.prodMap continuous_id)).sub continuous_const
    exact h
  have hFan : ∀ x : X, AnalyticOnNhd ℂ (F x) (closedBall (C m) (R m)) := fun x =>
    ((analyticOnNhd_discrim_z x.1).sub analyticOnNhd_const).mono (subset_univ _)
  have hFne : ∀ x : X, ∀ z ∈ sphere (C m) (R m), F x z ≠ 0 := by
    intro x z hz h
    apply hsphere x.1 x.2 z hz
    have : NlsGge.GK38.discrim x.1 z = s := sub_eq_zero.mp h
    rw [perChar_eq, this]
    linear_combination hs2
  have hlc := Lib.zeroCount_locallyConstant (F := F) (c := C m) (R := R m) (hRpos m) hFan
    hcont.continuousOn hFne
  haveI : PreconnectedSpace X :=
    Subtype.preconnectedSpace (convex_ball (realSlice u) ρ).isPreconnected
  have hmult : ∀ ψ ∈ ball (realSlice u) ρ,
      Multiset.card (Lib.zeroMultiset (perChar ψ) (ball (C m) (R m))) = 2 := by
    intro ψ hψ
    rw [← ((hspec ψ hψ).1 m).2.2.2.2.1]
    simp
  have hr : realSlice u ∈ ball (realSlice u) ρ := mem_ball_self hρ
  -- the real centre: no zero of `Delta + s`
  have hbase : Lib.zeroMultiset (fun z => NlsGge.GK38.discrim (realSlice u) z + s) (ball (C m) (R m)) = 0 := by
    classical
    have hg : AnalyticOnNhd ℂ (fun z => NlsGge.GK38.discrim (realSlice u) z + s) (closedBall (C m) (R m)) :=
      ((analyticOnNhd_discrim_z (realSlice u)).add analyticOnNhd_const).mono (subset_univ _)
    refine Multiset.ext' fun z => ?_
    rw [Lib.count_zeroMultiset_ball hg, Multiset.count_zero]
    split_ifs with hz
    · have hne : NlsGge.GK38.discrim (realSlice u) z + s ≠ 0 := by
        intro h
        have hz0 : perChar (realSlice u) z = 0 := by
          rw [perChar_eq]
          have : NlsGge.GK38.discrim (realSlice u) z = -s := eq_neg_of_add_eq_zero_left h
          rw [this]
          linear_combination hs2
        have hpc : AnalyticOnNhd ℂ (perChar (realSlice u)) (closedBall (C m) (R m)) :=
          (analyticOnNhd_perChar_z (realSlice u)).mono (subset_univ _)
        obtain ⟨w, hw⟩ : (sphere (C m) (R m)).Nonempty := NormedSpace.sphere_nonempty.mpr (hRpos m).le
        have hmem := (Lib.mem_zeroMultiset_iff_zero hpc ball_subset_closedBall
          ⟨w, sphere_subset_closedBall hw, hsphere _ hr w hw⟩).mpr ⟨hz, hz0⟩
        rw [← ((hspec _ hr).1 m).2.2.2.2.1] at hmem
        have hsr := periodic_real_pair_signs38 u m
        have hc : ((Real.cos ((m : ℝ) * Real.pi) : ℝ) : ℂ) = (-1 : ℂ) ^ m := by
          rw [Real.cos_int_mul_pi]
          simp
        have hmem' : z = lamMinus (realSlice u) m ∨ z = lamPlus (realSlice u) m := by
          simpa only [Multiset.mem_cons, Multiset.notMem_zero, or_false] using hmem
        have hDz : NlsGge.GK38.discrim (realSlice u) z = s := by
          rcases hmem' with rfl | rfl
          · rw [hsr.1, hc]
          · rw [hsr.2, hc]
        have h2 : NlsGge.GK38.discrim (realSlice u) z = -s := eq_neg_of_add_eq_zero_left h
        apply hs0
        linear_combination (-1 / 2 : ℂ) * (h2.symm.trans hDz)
      have h0 : analyticOrderAt (fun z => NlsGge.GK38.discrim (realSlice u) z + s) z = 0 :=
        (hg z (ball_subset_closedBall hz)).analyticOrderAt_eq_zero.2 hne
      simp only [analyticOrderNatAt, h0, ENat.toNat_zero]
    · rfl
  have hcardP : ∀ ψ ∈ ball (realSlice u) ρ,
      Multiset.card (Lib.zeroMultiset (fun z => NlsGge.GK38.discrim ψ z - s) (ball (C m) (R m))) = 2 := by
    intro ψ hψ
    have hconst := hlc.apply_eq_of_preconnectedSpace (⟨ψ, hψ⟩ : X) ⟨realSlice u, hr⟩
    have hrcard : Multiset.card (Lib.zeroMultiset (fun z => NlsGge.GK38.discrim (realSlice u) z - s) (ball (C m) (R m))) = 2 := by
      have h := hmult _ hr
      rw [hsplit _ hr, hbase, add_zero] at h
      exact h
    exact hconst.trans hrcard
  intro ψ hψ
  have hZm : Lib.zeroMultiset (fun z => NlsGge.GK38.discrim ψ z + s) (ball (C m) (R m)) = 0 := by
    have h := hmult ψ hψ
    rw [hsplit ψ hψ, Multiset.card_add, hcardP ψ hψ] at h
    exact Multiset.card_eq_zero.mp (by omega)
  have hmultψ := ((hspec ψ hψ).1 m).2.2.2.2.1
  rw [hsplit ψ hψ, hZm, add_zero] at hmultψ
  have hfψ : AnalyticOnNhd ℂ (fun z => NlsGge.GK38.discrim ψ z - s) (closedBall (C m) (R m)) :=
    ((analyticOnNhd_discrim_z ψ).sub analyticOnNhd_const).mono (subset_univ _)
  have hroot : ∀ z : ℂ, z ∈ lamMinus ψ m ::ₘ lamPlus ψ m ::ₘ 0 → NlsGge.GK38.discrim ψ z = s := by
    intro z hz
    rw [hmultψ] at hz
    have hz' := (Lib.mem_zeroMultiset_ball hfψ).mp hz
    by_contra hne
    have h0 : analyticOrderAt (fun z => NlsGge.GK38.discrim ψ z - s) z = 0 :=
      (hfψ z (ball_subset_closedBall hz'.1)).analyticOrderAt_eq_zero.2 (sub_ne_zero.mpr hne)
    exact hz'.2 (by simp only [analyticOrderNatAt, h0, ENat.toNat_zero])
  exact ⟨hroot _ (by simp), hroot _ (by simp)⟩

theorem sign_on_gkW (φ : PotPair) (hφ : φ ∈ gkW) (m : ℤ) :
    NlsGge.GK38.discrim φ (lamMinus φ m) = 2 * (-1 : ℂ) ^ m ∧
    NlsGge.GK38.discrim φ (lamPlus φ m) = 2 * (-1 : ℂ) ^ m := by
  obtain ⟨u, ρ, ⟨hρ, C, R, c, N, hg, hspec⟩, hmem⟩ := hφ
  exact sign_on_certified_ball u ρ hρ C R (fun n => (hg.1 n).1) hspec m φ hmem

theorem gammaSq_analytic (n : ℤ) :
    AnalyticOnNhd ℂ (fun φ : PotPair => (lamPlus φ n - lamMinus φ n) ^ 2) gkW := by
  have h1 := symmetric_pair_powers_analytic38 n 1
  have h2 := symmetric_pair_powers_analytic38 n 2
  have h3 : AnalyticOnNhd ℂ (fun φ : PotPair =>
      2 * (lamMinus φ n ^ 2 + lamPlus φ n ^ 2) - (lamMinus φ n ^ 1 + lamPlus φ n ^ 1) ^ 2) gkW :=
    (analyticOnNhd_const.mul h2).sub (h1.pow 2)
  have he : (fun φ : PotPair => (lamPlus φ n - lamMinus φ n) ^ 2) = fun φ : PotPair =>
      2 * (lamMinus φ n ^ 2 + lamPlus φ n ^ 2) - (lamMinus φ n ^ 1 + lamPlus φ n ^ 1) ^ 2 := by
    funext φ
    ring
  rw [he]
  exact h3

theorem endpointDelta_analytic (m : ℤ) :
    AnalyticOnNhd ℂ (fun φ : PotPair => NlsGge.GK38.discrim φ (muSeq φ m) - 2 * (-1 : ℂ) ^ m) gkW := by
  intro φ hφ
  have h : AnalyticAt ℂ (fun ψ : PotPair => NlsGge.GK38.discrim ψ (muSeq ψ m)) φ :=
    AnalyticAt.comp
      (g := fun p : PotPair × ℂ => NlsGge.GK38.discrim p.1 p.2)
      (f := fun ψ : PotPair => (ψ, muSeq ψ m))
      (analyticOnNhd_discrim (φ, muSeq φ m) (mem_univ _))
      ((analyticAt_id (𝕜 := ℂ)).prod (analyticOnNhd_muSeq_complex38 m φ hφ))
  exact h.sub analyticAt_const

theorem G3012_main (m : ℤ) : ((
    AnalyticOnNhd ℂ (fun φ : PotPair => (lamPlus φ m - lamMinus φ m) ^ 2) gkW ∧
    AnalyticOnNhd ℂ
      (fun φ : PotPair => NlsGge.GK38.discrim φ (muSeq φ m) - 2 * (-1 : ℂ) ^ m) gkW ∧
    {φ : PotPair | φ ∈ gkW ∧ lamPlus φ m = lamMinus φ m} =
      {φ : PotPair | φ ∈ gkW ∧ (lamPlus φ m - lamMinus φ m) ^ 2 = 0} ∧
    {φ : PotPair | φ ∈ gkW ∧ (muSeq φ m = lamMinus φ m ∨ muSeq φ m = lamPlus φ m)} =
      {φ : PotPair | φ ∈ gkW ∧ NlsGge.GK38.discrim φ (muSeq φ m) = 2 * (-1 : ℂ) ^ m} ∧
    {φ : PotPair | φ ∈ gkW ∧ (muSeq φ m = lamMinus φ m ∨ muSeq φ m = lamPlus φ m)} =
      {φ : PotPair | φ ∈ gkW ∧
        NlsGge.GK38.discrim φ (muSeq φ m) - 2 * (-1 : ℂ) ^ m = 0}
  : Prop)) := by
  refine ⟨gammaSq_analytic m, endpointDelta_analytic m, ?_, ?_, ?_⟩
  · ext φ
    simp only [Set.mem_setOf_eq, sq_eq_zero_iff, sub_eq_zero]
  · ext φ
    simp only [Set.mem_setOf_eq]
    refine and_congr_right fun hφ => ?_
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := sign_on_gkW φ hφ m
      rcases h with h | h
      · rw [h]; exact h1
      · rw [h]; exact h2
    · intro h
      apply (angleEndpointDetector_zero_iff38 φ hφ m).mp
      change perChar φ (muSeq φ m) = 0
      rw [perChar_eq, h]
      rcases neg_one_zpow_cases m with h' | h' <;> rw [h'] <;> norm_num
  · ext φ
    simp only [Set.mem_setOf_eq]
    refine and_congr_right fun hφ => ?_
    rw [sub_eq_zero]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := sign_on_gkW φ hφ m
      rcases h with h | h
      · rw [h]; exact h1
      · rw [h]; exact h2
    · intro h
      apply (angleEndpointDetector_zero_iff38 φ hφ m).mp
      change perChar φ (muSeq φ m) = 0
      rw [perChar_eq, h]
      rcases neg_one_zpow_cases m with h' | h' <;> rw [h'] <;> norm_num

end

end NlsGge.Atomic.G3012S3
