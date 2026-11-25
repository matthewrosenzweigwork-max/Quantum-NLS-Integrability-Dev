                                                                                                              
                                                                                                    
                                                                                                            
                                                  
import Mathlib
import NlsGge.Atomic.KST.KST019
import NlsGge.GK38.PeriodicLabellingCanonical
import NlsGge.GK38.CountingLemmaGeometry
import NlsGge.GK38.Lib.CircleArgument

section SmallSec

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace NlsGge.ThirdConsultation.KST

open NlsGge.Atomic.KST002 NlsGge.Atomic.KST003
open NlsGge.Atomic.KST004 NlsGge.Atomic.KST006 NlsGge.Atomic.KST007
open NlsGge.Atomic.KST012 NlsGge.Atomic.KST013 NlsGge.Atomic.KST016
open NlsGge.Analysis NlsGge.Pilot NlsGge.Schur

/-! ### Majorant sequences: sums, differences, tails -/

theorem hasSum_pc_sq (φ : Potential) (b : Bool) :
    HasSum (fun k : ℤ => ‖potentialCoeff φ b k‖ ^ 2) (‖φ b‖ ^ 2) := by
  have h := lpC_hasSum_sq ((fourierBasis (T := (2 : ℝ))).repr (naturalPhysicalCoverL2 (φ b)))
  have e : ‖(fourierBasis (T := (2 : ℝ))).repr (naturalPhysicalCoverL2 (φ b))‖ = ‖φ b‖ :=
    ((fourierBasis (T := (2 : ℝ))).repr.norm_map _).trans (naturalPhysicalCoverL2_norm _)
  rw [e] at h
  convert h using 2
  simp only [potentialCoeff]
  exact congrArg (fun t => ‖t‖ ^ 2) (fc_repr _ _)

theorem hasSum_maj_sq (φ : Potential) :
    HasSum (fun k : ℤ => majorantCoeff φ k ^ 2) (‖majorantSequence φ‖ ^ 2) := by
  have h := lpR_hasSum_sq (majorantSequence φ)
  convert h using 2
  simp [majorantSequence_apply, Real.norm_eq_abs, abs_of_nonneg (majorant_nonneg φ _)]

theorem potentialCoeff_sub (φ φ0 : Potential) (b : Bool) (k : ℤ) :
    potentialCoeff (φ - φ0) b k = potentialCoeff φ b k - potentialCoeff φ0 b k := by
  simp only [potentialCoeff, PiLp.sub_apply, map_sub]
  rw [fc_repr, fc_repr, fc_repr]
  exact congrArg (fun t : lp (fun _ : ℤ => ℂ) 2 => t k)
    (LinearIsometryEquiv.map_sub (fourierBasis (T := (2 : ℝ))).repr _ _)

theorem majorant_add_le (φ φ0 : Potential) (k : ℤ) :
    majorantCoeff φ k ≤ majorantCoeff φ0 k + majorantCoeff (φ - φ0) k := by
  have key : ∀ (b : Bool) (j : ℤ), (j = k ∨ j = -k) →
      ‖potentialCoeff φ b j‖ ≤ majorantCoeff φ0 k + majorantCoeff (φ - φ0) k := by
    intro b j hj
    have h1 : potentialCoeff φ b j = potentialCoeff φ0 b j + potentialCoeff (φ - φ0) b j := by
      rw [potentialCoeff_sub]; ring
    have h2 := potentialCoeff_norm_le_majorant φ0 b j
    have h3 := potentialCoeff_norm_le_majorant (φ - φ0) b j
    have he : majorantCoeff φ0 j = majorantCoeff φ0 k ∧
        majorantCoeff (φ - φ0) j = majorantCoeff (φ - φ0) k := by
      rcases hj with h | h
      · rw [h]; exact ⟨rfl, rfl⟩
      · rw [h]; exact ⟨majorant_even φ0 k, majorant_even (φ - φ0) k⟩
    rw [h1]
    calc ‖potentialCoeff φ0 b j + potentialCoeff (φ - φ0) b j‖
        ≤ ‖potentialCoeff φ0 b j‖ + ‖potentialCoeff (φ - φ0) b j‖ := norm_add_le _ _
      _ ≤ _ := by rw [he.1] at h2; rw [he.2] at h3; linarith
  unfold majorantCoeff
  simp only [max_le_iff]
  exact ⟨⟨key true k (Or.inl rfl), key true (-k) (Or.inr rfl)⟩,
    ⟨key false k (Or.inl rfl), key false (-k) (Or.inr rfl)⟩⟩

theorem maj_sq_le_norm_sq (δ : Potential) : ‖majorantSequence δ‖ ^ 2 ≤ 2 * ‖δ‖ ^ 2 := by
  have hmax : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → max x y ^ 2 ≤ x ^ 2 + y ^ 2 := by
    intro x y hx hy
    rcases le_total x y with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  have hT := hasSum_pc_sq δ true
  have hF := hasSum_pc_sq δ false
  have hTn : HasSum (fun k : ℤ => ‖potentialCoeff δ true (-k)‖ ^ 2) (‖δ true‖ ^ 2) :=
    (Equiv.neg ℤ).hasSum_iff.2 hT
  have hFn : HasSum (fun k : ℤ => ‖potentialCoeff δ false (-k)‖ ^ 2) (‖δ false‖ ^ 2) :=
    (Equiv.neg ℤ).hasSum_iff.2 hF
  have hE : HasSum (fun k : ℤ => (‖potentialCoeff δ true k‖ ^ 2 + ‖potentialCoeff δ true (-k)‖ ^ 2) +
      (‖potentialCoeff δ false k‖ ^ 2 + ‖potentialCoeff δ false (-k)‖ ^ 2))
      ((‖δ true‖ ^ 2 + ‖δ true‖ ^ 2) + (‖δ false‖ ^ 2 + ‖δ false‖ ^ 2)) :=
    (hT.add hTn).add (hF.add hFn)
  have hle : ∀ k : ℤ, majorantCoeff δ k ^ 2 ≤
      (‖potentialCoeff δ true k‖ ^ 2 + ‖potentialCoeff δ true (-k)‖ ^ 2) +
      (‖potentialCoeff δ false k‖ ^ 2 + ‖potentialCoeff δ false (-k)‖ ^ 2) := by
    intro k
    have hu := hmax ‖potentialCoeff δ true k‖ ‖potentialCoeff δ true (-k)‖ (norm_nonneg _) (norm_nonneg _)
    have hl := hmax ‖potentialCoeff δ false k‖ ‖potentialCoeff δ false (-k)‖ (norm_nonneg _) (norm_nonneg _)
    have h := hmax (max ‖potentialCoeff δ true k‖ ‖potentialCoeff δ true (-k)‖)
      (max ‖potentialCoeff δ false k‖ ‖potentialCoeff δ false (-k)‖)
      (le_trans (norm_nonneg _) (le_max_left _ _)) (le_trans (norm_nonneg _) (le_max_left _ _))
    exact h.trans (add_le_add hu hl)
  have := hasSum_le hle (hasSum_maj_sq δ) hE
  have hn := norm_pair_sq δ
  nlinarith

theorem tailSum_sub_le (φ φ0 : Potential) (N : ℕ) :
    tailSum φ N ≤ 2 * tailSum φ0 N + 2 * ‖majorantSequence (φ - φ0)‖ ^ 2 := by
  have hs0 := tailTerm_summable φ0 N
  have hsd := (hasSum_maj_sq (φ - φ0)).summable
  have hg : Summable (fun j : ℤ => 2 * (if N ≤ j.natAbs then majorantCoeff φ0 j ^ 2 else 0) +
      2 * majorantCoeff (φ - φ0) j ^ 2) := (hs0.mul_left 2).add (hsd.mul_left 2)
  have hsum : ∑' j : ℤ, (2 * (if N ≤ j.natAbs then majorantCoeff φ0 j ^ 2 else 0) +
      2 * majorantCoeff (φ - φ0) j ^ 2) = 2 * tailSum φ0 N + 2 * ‖majorantSequence (φ - φ0)‖ ^ 2 := by
    rw [Summable.tsum_add (hs0.mul_left 2) (hsd.mul_left 2), tsum_mul_left, tsum_mul_left,
      (hasSum_maj_sq (φ - φ0)).tsum_eq]
    rfl
  rw [← hsum]
  refine Summable.tsum_le_tsum (fun j => ?_) (tailTerm_summable φ N) hg
  have hm := majorant_add_le φ φ0 j
  have h0 := majorant_nonneg φ j
  have h1 := majorant_nonneg φ0 j
  have h2 := majorant_nonneg (φ - φ0) j
  split_ifs with hj
  · nlinarith [sq_nonneg (majorantCoeff φ0 j - majorantCoeff (φ - φ0) j)]
  · nlinarith [sq_nonneg (majorantCoeff (φ - φ0) j)]

theorem maj_sq_sub_le (φ φ0 : Potential) :
    ‖majorantSequence φ‖ ^ 2 ≤ 2 * ‖majorantSequence φ0‖ ^ 2 + 2 * ‖majorantSequence (φ - φ0)‖ ^ 2 := by
  have h := tailSum_sub_le φ φ0 0
  have e : ∀ ψ : Potential, tailSum ψ 0 = ‖majorantSequence ψ‖ ^ 2 := by
    intro ψ
    unfold tailSum
    simp only [Nat.zero_le, ite_true]
    exact (hasSum_maj_sq ψ).tsum_eq
  rw [e, e] at h
  exact h


/-! ### Analyticity of the reduced coefficients on the strip -/

theorem abc_analyticOnNhd (φ : Potential) (n : ℤ)
    (hq : ∀ (z : ℂ) (hz : z ∈ spectralStrip n), ‖qOperator φ n z hz ^ 2‖ ≤ (1 / 2 : ℝ)) :
    AnalyticOnNhd ℂ (a φ n) (spectralStrip n) ∧ AnalyticOnNhd ℂ (b φ n) (spectralStrip n) ∧
      AnalyticOnNhd ℂ (c φ n) (spectralStrip n) := by
  have key : ∀ z0 ∈ spectralStrip n,
      AnalyticAt ℂ (fun z : ℂ => localABC n (center n) (center_mem_strip n) (z, φ)) z0 := by
    intro z0 hz0
    have hfree : IsUnit (localFreeFactor n (center n) (center_mem_strip n) (z0, φ)) :=
      isUnit_free_of_strips n (center n) z0 (center_mem_strip n) hz0
    have hunit : IsUnit (1 - qOperator φ n z0 hz0) :=
      (inverse_one_sub_of_sq_norm_lt (qOperator φ n z0 hz0)
        (lt_of_le_of_lt (hq z0 hz0) (by norm_num))).1
    have hmem : (z0, φ) ∈ localInverseDomain n (center n) (center_mem_strip n) := by
      refine ⟨hfree, ?_⟩
      rw [qOperator_local_resolvent_identity φ n (center n) z0 (center_mem_strip n) hz0 hfree]
      exact hunit
    have hA := localABC_analyticOnNhd n (center n) (center_mem_strip n) (z0, φ) hmem
    have hid : AnalyticAt ℂ (fun z : ℂ => z) z0 := analyticAt_id
    have hf : AnalyticAt ℂ (fun z : ℂ => (z, φ)) z0 := hid.prod analyticAt_const
    exact AnalyticAt.comp (f := fun z : ℂ => (z, φ)) hA hf
  refine ⟨fun z0 hz0 => ?_, fun z0 hz0 => ?_, fun z0 hz0 => ?_⟩
  · exact ((ContinuousLinearMap.fst ℂ ℂ (ℂ × ℂ)).analyticAt _).comp (key z0 hz0)
  · exact (((ContinuousLinearMap.fst ℂ ℂ ℂ).comp
      (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))).analyticAt _).comp (key z0 hz0)
  · exact (((ContinuousLinearMap.snd ℂ ℂ ℂ).comp
      (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))).analyticAt _).comp (key z0 hz0)


/-! ### Uniform smallness of the reduced coefficients near a potential -/

theorem uniform_small_abc (φ0 : Potential) :
    ∃ e : ℝ, 0 < e ∧ ∃ N : ℕ, 5 ≤ N ∧
    ∀ φ : Potential, ‖φ - φ0‖ < e → ∀ n : ℤ, N ≤ n.natAbs →
      (∀ (z : ℂ) (hz : z ∈ spectralStrip n), ‖qOperator φ n z hz ^ 2‖ ≤ (1 / 2 : ℝ)) ∧
      SmallCoefficients n (a φ n) (b φ n) (c φ n) := by
  obtain ⟨ε, hε, N₀, hN₀, hloc⟩ := reducedBC_uniform_local φ0
  set s0 : ℝ := ‖majorantSequence φ0‖ with hs0
  have hs0nn : 0 ≤ s0 := norm_nonneg _
  set S : ℝ := Real.sqrt (2 * s0 ^ 2 + 4) with hS
  have hS2 : S ^ 2 = 2 * s0 ^ 2 + 4 := Real.sq_sqrt (by positivity)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  set K : ℝ := 2 * S + 4 * S ^ 2 + 1 with hK
  have hKpos : 0 < K := by positivity
  set δ : ℝ := Real.pi / (48 * K) with hδ
  have hδpos : 0 < δ := by positivity
  have hKδ : K * δ = Real.pi / 48 := by rw [hδ]; field_simp
  have ht : Tendsto (fun N : ℕ => tailSum φ0 N) atTop (𝓝 0) := tailSum_tendsto φ0
  obtain ⟨Nt, hNt⟩ := Filter.eventually_atTop.mp
    (ht.eventually (gt_mem_nhds (show (0 : ℝ) < δ ^ 2 / 16 by positivity)))
  obtain ⟨Nl, hNl⟩ := exists_nat_gt (2 * S / δ)
  refine ⟨min ε (min 1 (δ / 6)), lt_min hε (lt_min one_pos (by positivity)),
    max N₀ (max Nt (max Nl 5)), (le_max_right Nl 5).trans ((le_max_right Nt _).trans (le_max_right N₀ _)),
    ?_⟩
  intro φ hφ n hn
  have hn₀ : N₀ ≤ n.natAbs := le_trans (le_max_left _ _) hn
  have hnt : Nt ≤ n.natAbs := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnl : Nl ≤ n.natAbs :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hn
  have hn5 : 5 ≤ n.natAbs :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hn
  have hn0 : n ≠ 0 := by
    intro h; subst h; simp at hn5
  have hq : ∀ (z : ℂ) (hz : z ∈ spectralStrip n), ‖qOperator φ n z hz ^ 2‖ ≤ (1 / 2 : ℝ) :=
    fun z hz => (hloc φ (lt_of_lt_of_le hφ (min_le_left _ _)) n hn₀ z hz).1
  refine ⟨hq, ?_⟩
  obtain ⟨ha, hb, hc⟩ := abc_analyticOnNhd φ n hq
  refine ⟨ha, hb, hc, fun z hz => ?_⟩
  set d : ℝ := ‖φ - φ0‖ with hd
  have hd0 : 0 ≤ d := norm_nonneg _
  have hd1 : d < 1 := lt_of_lt_of_le hφ ((min_le_right _ _).trans (min_le_left _ _))
  have hd2 : d < δ / 6 := lt_of_lt_of_le hφ ((min_le_right _ _).trans (min_le_right _ _))
  have hMd : ‖majorantSequence (φ - φ0)‖ ^ 2 ≤ 2 * d ^ 2 := maj_sq_le_norm_sq _
  have hsφ : ‖majorantSequence φ‖ ≤ S := by
    have h := maj_sq_sub_le φ φ0
    have hd2' : d ^ 2 ≤ 1 := pow_le_one₀ hd0 hd1.le
    have h' : ‖majorantSequence φ‖ ^ 2 ≤ 2 * s0 ^ 2 + 4 := by linarith
    have := Real.abs_le_sqrt h'
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have hNpos : (0 : ℝ) < (n.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.mpr hn0
  have htail : tailSum φ n.natAbs ≤ (δ / 2) ^ 2 := by
    have h1 := tailSum_sub_le φ φ0 n.natAbs
    have h2 : tailSum φ0 n.natAbs < δ ^ 2 / 16 := hNt _ hnt
    have h3 : d ^ 2 ≤ (δ / 6) ^ 2 := pow_le_pow_left₀ hd0 hd2.le 2
    have e1 : (δ / 6) ^ 2 = δ ^ 2 / 36 := by ring
    have e2 : (δ / 2) ^ 2 = δ ^ 2 / 4 := by ring
    have h4 : 0 ≤ δ ^ 2 := sq_nonneg δ
    linarith
  have hτ : Real.sqrt (tailSum φ n.natAbs) ≤ δ / 2 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, htail⟩
  have hsN : ‖majorantSequence φ‖ / (n.natAbs : ℝ) ≤ δ / 2 := by
    rw [div_le_iff₀ hNpos]
    have h3 : (Nl : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast hnl
    have h4 : 2 * S / δ < (n.natAbs : ℝ) := lt_of_lt_of_le hNl h3
    rw [div_lt_iff₀ hδpos] at h4
    linarith
  have hρ := rho_le φ n hn0
  have hρδ : Real.sqrt (∑' k, gDen φ n k) ≤ δ := by linarith
  have hρ0 : 0 ≤ Real.sqrt (∑' k, gDen φ n k) := Real.sqrt_nonneg _
  have hs := norm_nonneg (majorantSequence φ)
  have habc := abc_eq_reduced φ n z hz
  have haeq : a φ n z = reducedA φ n z hz := by unfold a; rw [habc]
  have hbeq : b φ n z = reducedB φ n z hz := by unfold b; rw [habc]
  have hceq : c φ n z = reducedC φ n z hz := by unfold c; rw [habc]
  have hA := reducedA_bound φ n z hz (hq z hz)
  have hB := reducedB_bound φ n z hz (hq z hz)
  have hC := reducedC_bound φ n z hz (hq z hz)
  have hcb := cov_le φ n false (2 * n) (by omega)
  have hcc := cov_le φ n true (-2 * n) (by omega)
  have hK1 : 2 * S ≤ K := by have := sq_nonneg S; linarith [hK]
  have hK2 : 4 * S ^ 2 + 1 / 2 ≤ K := by linarith [hK]
  have hAfin : 2 * ‖majorantSequence φ‖ * Real.sqrt (∑' k, gDen φ n k) ≤ K * δ := by
    calc 2 * ‖majorantSequence φ‖ * Real.sqrt (∑' k, gDen φ n k) ≤ 2 * S * δ := by gcongr
      _ ≤ K * δ := mul_le_mul_of_nonneg_right hK1 hδpos.le
  have hBfin : 4 * ‖majorantSequence φ‖ ^ 2 * Real.sqrt (∑' k, gDen φ n k) + δ / 2 ≤ K * δ := by
    have h1 : 4 * ‖majorantSequence φ‖ ^ 2 * Real.sqrt (∑' k, gDen φ n k) ≤ 4 * S ^ 2 * δ := by gcongr
    calc 4 * ‖majorantSequence φ‖ ^ 2 * Real.sqrt (∑' k, gDen φ n k) + δ / 2
        ≤ (4 * S ^ 2 + 1 / 2) * δ := by linarith
      _ ≤ K * δ := mul_le_mul_of_nonneg_right hK2 hδpos.le
  rw [haeq, hbeq, hceq]
  refine ⟨hA.trans (hAfin.trans hKδ.le), ?_, ?_⟩
  · calc ‖reducedB φ n z hz‖
        = ‖(reducedB φ n z hz - coveredCoeff φ false (2 * n)) + coveredCoeff φ false (2 * n)‖ := by
          congr 1; ring
      _ ≤ ‖reducedB φ n z hz - coveredCoeff φ false (2 * n)‖ + ‖coveredCoeff φ false (2 * n)‖ :=
          norm_add_le _ _
      _ ≤ 4 * ‖majorantSequence φ‖ ^ 2 * Real.sqrt (∑' k, gDen φ n k) + δ / 2 :=
          add_le_add hB (hcb.trans hτ)
      _ ≤ Real.pi / 48 := hBfin.trans hKδ.le
  · calc ‖reducedC φ n z hz‖
        = ‖(reducedC φ n z hz - coveredCoeff φ true (-2 * n)) + coveredCoeff φ true (-2 * n)‖ := by
          congr 1; ring
      _ ≤ ‖reducedC φ n z hz - coveredCoeff φ true (-2 * n)‖ + ‖coveredCoeff φ true (-2 * n)‖ :=
          norm_add_le _ _
      _ ≤ 4 * ‖majorantSequence φ‖ ^ 2 * Real.sqrt (∑' k, gDen φ n k) + δ / 2 :=
          add_le_add hC (hcc.trans hτ)
      _ ≤ Real.pi / 48 := hBfin.trans hKδ.le

end NlsGge.ThirdConsultation.KST
end
end SmallSec



set_option autoImplicit false

section AsmSec
open Metric Set

namespace NlsGge.Atomic.KST029Asm
noncomputable section

/-- Order of an entire function that is not identically zero is finite everywhere. -/
theorem analyticOrderAt_ne_top_of_entire {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    (hw : ∃ w, f w ≠ 0) (z : ℂ) : analyticOrderAt f z ≠ ⊤ := by
  intro htop
  obtain ⟨w, hw⟩ := hw
  have hev : f =ᶠ[nhds z] 0 := by
    have := analyticOrderAt_eq_top.1 htop
    exact this.mono (fun _ h => by simpa using h)
  have h0 := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ z) hev (Set.mem_univ w)
  exact hw h0

/-- Members of a zero multiset of an entire function are zeros of it, and conversely for points of the
disc (the function being not identically zero). -/
theorem mem_zeroMultiset_ball_iff {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ) (hw : ∃ w, f w ≠ 0)
    {c : ℂ} {r : ℝ} {z : ℂ} :
    z ∈ NlsGge.GK38.Lib.zeroMultiset f (ball c r) ↔ z ∈ ball c r ∧ f z = 0 := by
  rw [NlsGge.GK38.Lib.mem_zeroMultiset_ball (hf.mono (Set.subset_univ _))]
  refine and_congr_right fun hz => ?_
  have hz' : AnalyticAt ℂ f z := hf z (Set.mem_univ z)
  have hne := analyticOrderAt_ne_top_of_entire hf hw z
  constructor
  · intro h
    by_contra hf0
    apply h
    have : analyticOrderAt f z = 0 := hz'.analyticOrderAt_eq_zero.2 hf0
    simp [analyticOrderNatAt, this]
  · intro h0 hnat
    have h1 : analyticOrderAt f z ≠ 0 := by
      intro h; exact (hz'.analyticOrderAt_eq_zero.1 h) h0
    unfold analyticOrderNatAt at hnat
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hne
    rw [← hk] at hnat h1
    simp at hnat
    apply h1
    simp [← hnat]

theorem assemble {D f : ℂ → ℂ} {c : ℂ} {R r : ℝ}
    (hDan : AnalyticOnNhd ℂ D (closedBall c R)) (hDw : ∃ w ∈ closedBall c R, D w ≠ 0)
    (hcard : Multiset.card (NlsGge.GK38.Lib.zeroMultiset D (ball c R)) = 2)
    (hfan : AnalyticOnNhd ℂ f univ) (hfw : ∃ w, f w ≠ 0)
    (x y : ℂ) (hxy : NlsGge.GK38.Lib.zeroMultiset f (ball c r) = {x, y})
    (hrR : r ≤ R)
    (hout : ∀ z ∈ ball c R, f z = 0 → z ∈ ball c r)
    (heq : ∀ z ∈ ball c R, D z = 0 ↔ f z = 0) :
    NlsGge.GK38.Lib.zeroMultiset D (ball c R) = {x, y} := by
  classical
  have hmemD : ∀ {z : ℂ}, z ∈ NlsGge.GK38.Lib.zeroMultiset D (ball c R) ↔ z ∈ ball c R ∧ D z = 0 :=
    fun {z} => NlsGge.GK38.Lib.mem_zeroMultiset_iff_zero hDan (Set.Subset.trans ball_subset_closedBall
      (Set.Subset.refl _)) hDw
  have hx : x ∈ NlsGge.GK38.Lib.zeroMultiset f (ball c r) := by rw [hxy]; simp
  have hy : y ∈ NlsGge.GK38.Lib.zeroMultiset f (ball c r) := by rw [hxy]; simp
  rw [mem_zeroMultiset_ball_iff hfan hfw] at hx hy
  have hxS : x ∈ NlsGge.GK38.Lib.zeroMultiset D (ball c R) :=
    hmemD.2 ⟨ball_subset_ball hrR hx.1, (heq x (ball_subset_ball hrR hx.1)).2 hx.2⟩
  have hyS : y ∈ NlsGge.GK38.Lib.zeroMultiset D (ball c R) :=
    hmemD.2 ⟨ball_subset_ball hrR hy.1, (heq y (ball_subset_ball hrR hy.1)).2 hy.2⟩
  have hsub : ∀ z ∈ NlsGge.GK38.Lib.zeroMultiset D (ball c R), z = x ∨ z = y := by
    intro z hz
    obtain ⟨hzb, hz0⟩ := hmemD.1 hz
    have hf0 := (heq z hzb).1 hz0
    have hzr := hout z hzb hf0
    have : z ∈ NlsGge.GK38.Lib.zeroMultiset f (ball c r) :=
      (mem_zeroMultiset_ball_iff hfan hfw).2 ⟨hzr, hf0⟩
    rw [hxy] at this
    simpa using this
  by_cases hne : x = y
  · subst hne
    have hrep := (Multiset.eq_replicate_card (a := x)
      (s := NlsGge.GK38.Lib.zeroMultiset D (ball c R))).2 (fun b hb => by
        rcases hsub b hb with h | h <;> exact h)
    rw [hcard] at hrep
    rw [hrep]
    simp [Multiset.replicate_succ]
  · have hnd : ({x, y} : Multiset ℂ).Nodup := by simp [hne]
    have hle : ({x, y} : Multiset ℂ) ≤ NlsGge.GK38.Lib.zeroMultiset D (ball c R) := by
      rw [Multiset.le_iff_subset hnd]
      intro z hz
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hxS
      · exact hyS
    exact (Multiset.eq_of_le_of_card_le hle (by rw [hcard]; simp)).symm

end
end NlsGge.Atomic.KST029Asm
end AsmSec


set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open NlsGge.Atomic.KST002 NlsGge.Atomic.KST004 NlsGge.Atomic.KST006
open NlsGge.GK38 NlsGge.Pilot

namespace NlsGge.ThirdConsultation.KST

abbrev periodicPair (φ : PhysicalPairLp) : PotPair := (φ true, φ false)

theorem dist_periodicPair_le (φ φ0 : PhysicalPairLp) :
    dist (periodicPair φ) (periodicPair φ0) ≤ ‖φ - φ0‖ := by
  rw [Prod.dist_eq]
  refine max_le ?_ ?_
  · rw [dist_eq_norm]
    have := PiLp.norm_apply_le (φ - φ0) true
    simpa [periodicPair] using this
  · rw [dist_eq_norm]
    have := PiLp.norm_apply_le (φ - φ0) false
    simpa [periodicPair] using this

/-- Local periodic labelling, uniform near a potential: the two labelled roots are exactly the zeros of the
periodic characteristic in the disc of radius `π/4`, there are no other zeros in the disc of radius `π/3`
and the characteristic is not identically zero. -/
theorem local_labelling (φ0 : PhysicalPairLp) :
    ∃ e : ℝ, 0 < e ∧ ∃ N : ℕ, 5 ≤ N ∧
    ∀ φ : PhysicalPairLp, ‖φ - φ0‖ < e → ∀ n : ℤ, N ≤ n.natAbs →
      (∃ w : ℂ, perChar (periodicPair φ) w ≠ 0) ∧
      Lib.zeroMultiset (perChar (periodicPair φ)) (Metric.ball ((n : ℂ) * Real.pi) (Real.pi / 4)) =
        {lamMinus (periodicPair φ) n, lamPlus (periodicPair φ) n} ∧
      (∀ z ∈ Metric.ball ((n : ℂ) * Real.pi) (Real.pi / 3), perChar (periodicPair φ) z = 0 →
        z ∈ Metric.ball ((n : ℂ) * Real.pi) (Real.pi / 4)) := by
  obtain ⟨U₁, hU₁, N₁, hN₁⟩ := simultaneous_counting_lemma38 (periodicPair φ0)
  obtain ⟨U₂, hU₂, N₂, -, h₂⟩ := labelling_local_multisets38 (periodicPair φ0)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hU₁ hU₂)
  refine ⟨ε, hε, max 5 (max (N₁ + 1) (N₂ + 1)), le_max_left _ _, ?_⟩
  intro φ hφ n hn
  have hmem : periodicPair φ ∈ U₁ ∩ U₂ := by
    apply hball
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (dist_periodicPair_le φ φ0) hφ
  have hn1 : N₁ + 1 ≤ n.natAbs :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn2 : N₂ + 1 ≤ n.natAbs :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have habs : |n| = (n.natAbs : ℤ) := Int.abs_eq_natAbs n
  obtain ⟨hc1, -⟩ := hN₁ _ hmem.1
  obtain ⟨hlab, -⟩ := (h₂ _ hmem.2).1 n (by rw [habs]; omega)
  refine ⟨hc1.2.2.1, ?_, ?_⟩
  · rw [← show countingCenter38 n = (n : ℂ) * Real.pi from rfl, ← hlab]
    simp
  · intro z hz h0
    obtain ⟨-, -, -, -, -, -, hno⟩ := hc1
    rcases hno z h0 with h | ⟨m, hm, hzm⟩
    · exfalso
      have h1 : ‖z‖ < countingRadius38 N₁ := by simpa using h
      have h2 : ((N₁ : ℝ) + 1) * Real.pi ≤ ‖countingCenter38 n‖ :=
        countingCenter_far_norm38 (by rw [habs]; omega)
      have h3 : ‖z - countingCenter38 n‖ < Real.pi / 3 := by
        simpa [dist_eq_norm, countingCenter38] using hz
      have h4 : ‖countingCenter38 n‖ ≤ ‖z‖ + ‖z - countingCenter38 n‖ := by
        calc ‖countingCenter38 n‖ = ‖z - (z - countingCenter38 n)‖ := by congr 1; ring
          _ ≤ ‖z‖ + ‖z - countingCenter38 n‖ := norm_sub_le _ _
      unfold countingRadius38 at h1
      nlinarith [Real.pi_pos]
    · by_cases hmn : m = n
      · subst hmn
        simpa [countingCenter38] using hzm
      · exfalso
        have hsep := countingCenter_separated38 hmn
        have h3 : ‖z - countingCenter38 n‖ < Real.pi / 3 := by
          simpa [dist_eq_norm, countingCenter38] using hz
        have h5 : ‖z - countingCenter38 m‖ < Real.pi / 4 := by
          simpa [dist_eq_norm, countingCenter38] using hzm
        have h4 : ‖countingCenter38 m - countingCenter38 n‖ ≤
            ‖z - countingCenter38 m‖ + ‖z - countingCenter38 n‖ := by
          calc ‖countingCenter38 m - countingCenter38 n‖
              = ‖(z - countingCenter38 n) - (z - countingCenter38 m)‖ := by congr 1; ring
            _ ≤ ‖z - countingCenter38 n‖ + ‖z - countingCenter38 m‖ := norm_sub_le _ _
            _ = _ := add_comm _ _
        have hsep' : Real.pi ≤ ‖countingCenter38 m - countingCenter38 n‖ := hsep
        nlinarith [Real.pi_pos]


/-- The packet head `kst029` (Pro round 10 `STATEMENTS/KST.md` `## KST-029`) as a Prop; `Potential` is written `PhysicalPairLp`. -/
def Kst029Head : Prop :=
  ∀ (φ0 : PhysicalPairLp),
  ∃ e : ℝ, 0 < e ∧ ∃ N : ℕ, 5 ≤ N ∧
  ∀ φ : PhysicalPairLp, ‖φ-φ0‖ < e → ∀ n : ℤ, N ≤ n.natAbs →
    SmallCoefficients n (a φ n) (b φ n) (c φ n) ∧
    Lib.zeroMultiset (determinant n (a φ n) (b φ n) (c φ n))
      (Metric.ball (center n) (Real.pi/3)) =
      {lamMinus (periodicPair φ) n, lamPlus (periodicPair φ) n} ∧
    (∀ z ∈ spectralStrip n, determinant n (a φ n) (b φ n) (c φ n) z = 0 ↔
      z = lamMinus (periodicPair φ) n ∨ z = lamPlus (periodicPair φ) n)

/-- Bridge support (statement): for a potential, a high index and a spectral point in the strip with the
small-square property, a zero of the determinant is the same as a zero of the periodic characteristic. -/
def OperatorPerCharBridge : Prop :=
  ∀ (φ : PhysicalPairLp) (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n),
    ‖qOperator φ n z hz ^ 2‖ ≤ (1/2 : ℝ) →
    (determinant n (a φ n) (b φ n) (c φ n) z = 0 ↔ perChar (periodicPair φ) z = 0)

open NlsGge.Atomic.KST029Asm in
/-- CONDITIONAL assembly: the packet head `kst029` from the operator / periodic-characteristic bridge. -/
theorem kst029_of_bridge (hB : OperatorPerCharBridge) : Kst029Head := by
  intro φ0
  obtain ⟨e1, he1, N1, hN1, hs⟩ := uniform_small_abc φ0
  obtain ⟨e2, he2, N2, hN2, hl⟩ := local_labelling φ0
  refine ⟨min e1 e2, lt_min he1 he2, max N1 N2, le_trans hN1 (le_max_left _ _), ?_⟩
  intro φ hφ n hn
  have hn1 : N1 ≤ n.natAbs := le_trans (le_max_left _ _) hn
  have hn2 : N2 ≤ n.natAbs := le_trans (le_max_right _ _) hn
  obtain ⟨hQ, hsmall⟩ := hs φ (lt_of_lt_of_le hφ (min_le_left _ _)) n hn1
  obtain ⟨hw, hmulti, hout⟩ := hl φ (lt_of_lt_of_le hφ (min_le_right _ _)) n hn2
  obtain ⟨hcard, hnz, -⟩ := kst019 n (a φ n) (b φ n) (c φ n) hsmall
  have hsub := closedBall_subset_strip n
  obtain ⟨ha, hb, hc, hbd⟩ := hsmall
  have hDan : AnalyticOnNhd ℂ (determinant n (a φ n) (b φ n) (c φ n))
      (Metric.closedBall (center n) (Real.pi / 3)) := fun z hz => by
    have hz' := hsub hz
    exact (((analyticAt_id.sub analyticAt_const).sub (ha z hz')).pow 2).sub
      ((hb z hz').mul (hc z hz'))
  have hπ : 0 < Real.pi / 3 := by positivity
  have hDw : ∃ w ∈ Metric.closedBall (center n) (Real.pi / 3),
      determinant n (a φ n) (b φ n) (c φ n) w ≠ 0 := by
    refine ⟨center n + ((Real.pi / 3 : ℝ) : ℂ), ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm]
      simp [abs_of_pos hπ]
    · apply hnz
      · apply hsub
        rw [Metric.mem_closedBall, dist_eq_norm]
        simp [abs_of_pos hπ]
      · simp [abs_of_pos hπ]
  have hcen : center n = (n : ℂ) * Real.pi := rfl
  have hmult : Lib.zeroMultiset (determinant n (a φ n) (b φ n) (c φ n))
      (Metric.ball (center n) (Real.pi / 3)) = {lamMinus (periodicPair φ) n, lamPlus (periodicPair φ) n} := by
    refine NlsGge.Atomic.KST029Asm.assemble (r := Real.pi / 4) hDan hDw hcard
      (analyticOnNhd_perChar_z (periodicPair φ)) hw _ _ ?_ (by linarith [Real.pi_pos]) ?_ ?_
    · rw [hcen]; exact hmulti
    · intro z hz h0
      rw [hcen]; exact hout z (by rw [← hcen]; exact hz) h0
    · intro z hz
      exact hB φ n z (hsub (Metric.ball_subset_closedBall hz)) (hQ z (hsub (Metric.ball_subset_closedBall hz)))
  refine ⟨⟨ha, hb, hc, hbd⟩, hmult, ?_⟩
  intro z hz
  constructor
  · intro h0
    by_cases hlt : ‖z - center n‖ < Real.pi / 3
    · have hz' : z ∈ Lib.zeroMultiset (determinant n (a φ n) (b φ n) (c φ n))
          (Metric.ball (center n) (Real.pi / 3)) := by
        rw [NlsGge.GK38.Lib.mem_zeroMultiset_iff_zero hDan Metric.ball_subset_closedBall hDw]
        exact ⟨by rw [Metric.mem_ball, dist_eq_norm]; exact hlt, h0⟩
      rw [hmult] at hz'
      simpa using hz'
    · exact absurd h0 (hnz z hz (not_lt.1 hlt))
  · intro h0
    have hz' : z ∈ Lib.zeroMultiset (determinant n (a φ n) (b φ n) (c φ n))
        (Metric.ball (center n) (Real.pi / 3)) := by
      rw [hmult]; simpa using h0
    rw [NlsGge.GK38.Lib.mem_zeroMultiset_iff_zero hDan Metric.ball_subset_closedBall hDw] at hz'
    exact hz'.2

end NlsGge.ThirdConsultation.KST
end
