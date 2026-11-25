import Mathlib
/- G2-021 PRODUCTION01 (proof development landing kit; HELD for landing). Source: proof development/G2021_FULL_01.lean (author proof development; independent review proof development/REVIEW_G2021_01.md), identical except this header and the removed `#print axioms` line. Target NlsGge/Atomic/G2/G2021.lean. -/
import NlsGge.GK38.XiSqKernel
import NlsGge.GK38.XiSqOmittedRoot
import NlsGge.GK38.StdRootBranchesLines
import NlsGge.GK38.GradEigenDefs
import NlsGge.GK38.F04AtOneSequenceTails

set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory SummationFilter
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section
namespace G2021Aux

/-- ℓ² tail of a nonnegative sequence, as a nonnegative indicator sum. -/
def tl (f : ℤ → ℝ) (N : ℕ) : ℝ := ∑' m : ℤ, if N < m.natAbs then f m else 0

theorem tl_summable {f : ℤ → ℝ} (hf : Summable f) (hnn : ∀ m, 0 ≤ f m) (N : ℕ) :
    Summable (fun m : ℤ => if N < m.natAbs then f m else 0) :=
  hf.of_nonneg_of_le (fun m => by split_ifs <;> simp [hnn m]) (fun m => by split_ifs <;> first | exact le_rfl | exact hnn m)

theorem tl_antitone {f : ℤ → ℝ} (hf : Summable f) (hnn : ∀ m, 0 ≤ f m) {N N' : ℕ}
    (h : N ≤ N') : tl f N' ≤ tl f N :=
  (tl_summable hf hnn N').tsum_le_tsum (fun m => by
    by_cases h1 : N' < m.natAbs
    · have : N < m.natAbs := lt_of_le_of_lt h h1
      simp [h1, this]
    · simp only [h1, if_false]
      split_ifs <;> simp [hnn m]) (tl_summable hf hnn N)

theorem tl_small {f : ℤ → ℝ} (hf : Summable f) (hnn : ∀ m, 0 ≤ f m) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, tl f N < ε := by
  obtain ⟨N, hN⟩ := summable_lattice_tails_small38 f hf (ε / 2) (by positivity)
  refine ⟨N, ?_⟩
  have : tl f N = tailSum38 f N := by
    unfold tl tailSum38
    refine tsum_congr (fun m => ?_)
    have h1 : ((N : ℤ) < |m|) ↔ N < m.natAbs := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast Iff.rfl
    by_cases h : N < m.natAbs
    · rw [if_pos h, if_pos (h1.2 h), abs_of_nonneg (hnn m)]
    · rw [if_neg h, if_neg (fun h' => h (h1.1 h'))]
  rw [this]
  linarith

theorem tl_mono {f g : ℤ → ℝ} (hf : Summable f) (hg : Summable g) (hfn : ∀ m, 0 ≤ f m)
    (hgn : ∀ m, 0 ≤ g m) (h : ∀ m, f m ≤ g m) (N : ℕ) : tl f N ≤ tl g N :=
  (tl_summable hf hfn N).tsum_le_tsum (fun m => by split_ifs <;> simp [h m, hgn m])
    (tl_summable hg hgn N)

theorem tl_le_tsum {f : ℤ → ℝ} (hf : Summable f) (hnn : ∀ m, 0 ≤ f m) (N : ℕ) :
    tl f N ≤ ∑' m, f m :=
  (tl_summable hf hnn N).tsum_le_tsum (fun m => by split_ifs <;> simp [hnn m]) hf

theorem lp2_hasSum (a : lp (fun _ : ℤ => ℂ) 2) : HasSum (fun n : ℤ => ‖a n‖ ^ 2) (‖a‖ ^ 2) := by
  have := lp.hasSum_norm (p := (2 : ENNReal)) (E := fun _ : ℤ => ℂ) (by norm_num) a
  simpa using this

theorem tl_lin {f g : ℤ → ℝ} (hf : Summable f) (hg : Summable g) (hfn : ∀ m, 0 ≤ f m)
    (hgn : ∀ m, 0 ≤ g m) (c₁ c₂ : ℝ) (N : ℕ) :
    tl (fun m => c₁ * f m + c₂ * g m) N = c₁ * tl f N + c₂ * tl g N := by
  unfold tl
  have h1 := tl_summable hf hfn N
  have h2 := tl_summable hg hgn N
  have : (fun m : ℤ => if N < m.natAbs then c₁ * f m + c₂ * g m else 0) =
      fun m => c₁ * (if N < m.natAbs then f m else 0) + c₂ * (if N < m.natAbs then g m else 0) := by
    funext m
    split_ifs <;> simp
  rw [this, (h1.mul_left c₁).tsum_add (h2.mul_left c₂), tsum_mul_left, tsum_mul_left]

theorem lp_tail_cont (A : PotPair → lp (fun _ : ℤ => ℂ) 2) (φ₀ : PotPair)
    (hA : ContinuousAt A φ₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ V ∈ 𝓝 φ₀, ∃ N : ℕ, ∀ φ ∈ V, tl (fun m => ‖A φ m‖ ^ 2) N < ε := by
  have hs0 := (lp2_hasSum (A φ₀)).summable
  obtain ⟨N, hN⟩ := tl_small hs0 (fun m => sq_nonneg _) (ε / 4) (by positivity)
  have hc : ContinuousAt (fun φ => ‖A φ - A φ₀‖ ^ 2) φ₀ :=
    ((hA.sub continuousAt_const).norm).pow 2
  have hlim : Tendsto (fun φ => ‖A φ - A φ₀‖ ^ 2) (𝓝 φ₀) (𝓝 0) := by
    have := hc.tendsto
    simpa using this
  have hev := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by positivity))
  refine ⟨_, hev, N, fun φ hφ => ?_⟩
  have hφ' : ‖A φ - A φ₀‖ ^ 2 < ε / 4 := hφ
  have hsφ := (lp2_hasSum (A φ)).summable
  have hsd := (lp2_hasSum (A φ - A φ₀)).summable
  have hdsum : ∑' m : ℤ, ‖(A φ - A φ₀) m‖ ^ 2 = ‖A φ - A φ₀‖ ^ 2 := (lp2_hasSum (A φ - A φ₀)).tsum_eq
  have hpt : ∀ m, ‖A φ m‖ ^ 2 ≤ 2 * ‖A φ₀ m‖ ^ 2 + 2 * ‖(A φ - A φ₀) m‖ ^ 2 := by
    intro m
    have h1 : (A φ - A φ₀) m = A φ m - A φ₀ m := rfl
    rw [h1]
    have h2 : ‖A φ m‖ ≤ ‖A φ₀ m‖ + ‖A φ m - A φ₀ m‖ := by
      calc ‖A φ m‖ = ‖A φ₀ m + (A φ m - A φ₀ m)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    nlinarith [sq_nonneg (‖A φ₀ m‖ - ‖A φ m - A φ₀ m‖), norm_nonneg (A φ m), norm_nonneg (A φ₀ m),
      norm_nonneg (A φ m - A φ₀ m)]
  have hnn : ∀ m : ℤ, 0 ≤ ‖A φ m‖ ^ 2 := fun m => sq_nonneg _
  have hnn0 : ∀ m : ℤ, 0 ≤ ‖A φ₀ m‖ ^ 2 := fun m => sq_nonneg _
  have hnnd : ∀ m : ℤ, 0 ≤ ‖(A φ - A φ₀) m‖ ^ 2 := fun m => sq_nonneg _
  have hmono := tl_mono hsφ ((hs0.mul_left 2).add (hsd.mul_left 2)) hnn
    (fun m => add_nonneg (mul_nonneg (by norm_num) (hnn0 m)) (mul_nonneg (by norm_num) (hnnd m)))
    hpt N
  have hlin := tl_lin hs0 hsd hnn0 hnnd 2 2 N
  have hd : tl (fun m => ‖(A φ - A φ₀) m‖ ^ 2) N ≤ ‖A φ - A φ₀‖ ^ 2 := by
    rw [← hdsum]; exact tl_le_tsum hsd hnnd N
  have hmono' : tl (fun m => ‖A φ m‖ ^ 2) N ≤
      tl (fun m => 2 * ‖A φ₀ m‖ ^ 2 + 2 * ‖(A φ - A φ₀) m‖ ^ 2) N := by
    simpa using hmono
  rw [hlin] at hmono'
  linarith

/-- difference of the symmetric product and its finite symmetric partial product -/
theorem prod_diff_bound (f : ℤ → ℂ) (h : Summable fun m : ℕ => ‖Lib.pairDev f m‖) (N : ℕ) :
    ‖(∏'[symmetricIcc ℤ] m, f m) - ∏ n ∈ Finset.Icc (-(N : ℤ)) N, f n‖ ≤
      ‖f 0‖ * Real.exp (∑' m : ℕ, ‖Lib.pairDev f m‖) *
        (Real.exp (∑' m : ℕ, ‖Lib.pairDev f (m + N)‖) - 1) := by
  have hsplit := Lib.tprod_symm_eq_prod_mul_tail h N
  set PN := ∏ n ∈ Finset.Icc (-(N : ℤ)) N, f n with hPN
  set T := ∏' m : ℕ, (1 + Lib.pairDev f (m + N)) with hT
  have hTb : ‖T - 1‖ ≤ Real.exp (∑' m : ℕ, ‖Lib.pairDev f (m + N)‖) - 1 :=
    Lib.norm_tprod_one_add_sub_one_le ((summable_nat_add_iff N).mpr h)
  have hPNb : ‖PN‖ ≤ ‖f 0‖ * Real.exp (∑' m : ℕ, ‖Lib.pairDev f m‖) := by
    rw [hPN, Lib.prod_Icc_symm_eq, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have e : ∀ m ∈ Finset.range N, f ((m : ℤ) + 1) * f (-((m : ℤ) + 1)) = 1 + Lib.pairDev f m :=
      fun m _ => (Lib.one_add_pairDev f m).symm
    rw [Finset.prod_congr rfl e, norm_prod]
    calc ∏ m ∈ Finset.range N, ‖1 + Lib.pairDev f m‖
        ≤ ∏ m ∈ Finset.range N, Real.exp ‖Lib.pairDev f m‖ := by
          gcongr with m hm
          calc ‖1 + Lib.pairDev f m‖ ≤ ‖(1 : ℂ)‖ + ‖Lib.pairDev f m‖ := norm_add_le _ _
            _ = ‖Lib.pairDev f m‖ + 1 := by rw [norm_one]; ring
            _ ≤ Real.exp ‖Lib.pairDev f m‖ := Real.add_one_le_exp _
      _ = Real.exp (∑ m ∈ Finset.range N, ‖Lib.pairDev f m‖) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (∑' m : ℕ, ‖Lib.pairDev f m‖) :=
          Real.exp_le_exp.mpr (h.sum_le_tsum _ (fun m _ => norm_nonneg _))
  rw [hsplit]
  calc ‖PN * T - PN‖ = ‖PN * (T - 1)‖ := by ring_nf
    _ = ‖PN‖ * ‖T - 1‖ := norm_mul _ _
    _ ≤ (‖f 0‖ * Real.exp (∑' m : ℕ, ‖Lib.pairDev f m‖)) *
          (Real.exp (∑' m : ℕ, ‖Lib.pairDev f (m + N)‖) - 1) :=
        mul_le_mul hPNb hTb (norm_nonneg _) (by positivity)


theorem pairMaj_tail (d : ℤ → ℝ) (hd : Summable d) (hd0 : ∀ n, 0 ≤ d n) (R : ℝ) (N : ℕ) :
    ∑' m : ℕ, Lib.pairMaj d R (m + N) ≤
      2 * Lib.majC1 * tl d N +
        Lib.majC2 R * ∑' m : ℕ, 1 / (((m + N : ℕ) : ℝ) + 1) ^ 2 := by
  have s1 : Summable fun m : ℕ => d (((m + N : ℕ) : ℤ) + 1) :=
    hd.comp_injective (i := fun m : ℕ => ((m + N : ℕ) : ℤ) + 1) (fun a b h => by simpa using h)
  have s2 : Summable fun m : ℕ => d (-(((m + N : ℕ) : ℤ) + 1)) :=
    hd.comp_injective (i := fun m : ℕ => -(((m + N : ℕ) : ℤ) + 1)) (fun a b h => by simpa using h)
  have s3 : Summable fun m : ℕ => 1 / (((m + N : ℕ) : ℝ) + 1) ^ 2 :=
    (summable_nat_add_iff (f := fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) N).mpr Lib.summable_inv_sq_succ
  have hg := tl_summable hd hd0 N
  have key : ∀ i : ℕ → ℤ, Function.Injective i → (∀ m, N < (i m).natAbs) →
      ∑' m : ℕ, d (i m) ≤ tl d N := by
    intro i hi hN
    have := tsum_comp_le_tsum_of_inj (f := fun k : ℤ => if N < k.natAbs then d k else 0) hg
      (fun k => by split_ifs <;> simp [hd0 k]) hi
    refine le_trans (le_of_eq ?_) this
    refine tsum_congr fun m => ?_
    simp [hN m]
  have e1 := key (fun m : ℕ => ((m + N : ℕ) : ℤ) + 1) (fun a b h => by simpa using h)
    (fun m => by simp <;> omega)
  have e2 := key (fun m : ℕ => -(((m + N : ℕ) : ℤ) + 1)) (fun a b h => by simpa using h)
    (fun m => by simp <;> omega)
  have hsum : ∑' m : ℕ, Lib.pairMaj d R (m + N) =
      Lib.majC1 * (∑' m : ℕ, d (((m + N : ℕ) : ℤ) + 1) + ∑' m : ℕ, d (-(((m + N : ℕ) : ℤ) + 1))) +
        Lib.majC2 R * ∑' m : ℕ, 1 / (((m + N : ℕ) : ℝ) + 1) ^ 2 := by
    unfold Lib.pairMaj
    rw [Summable.tsum_add ((s1.add s2).mul_left _) (s3.mul_left _), tsum_mul_left,
      Summable.tsum_add s1 s2, tsum_mul_left]
  rw [hsum]
  have hc1 := Lib.majC1_nonneg
  nlinarith

end G2021Aux

open G2021Aux

def rootProduct (n : ℤ) (p : PotPair × ℂ) : ℂ :=
  (Lib.piN n : ℂ)⁻¹ * a5OmittedRootProduct38 n p

theorem G2_021 (n : ℤ) :
    TendstoLocallyUniformlyOn
      (fun N : ℕ => fun p : PotPair × ℂ => (Lib.piN n : ℂ)⁻¹ *
        ∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a5OmittedRootFactor38 n m p)
      (rootProduct n) atTop (a5OmittedRootDomain38 n) ∧
    AnalyticOnNhd ℂ (rootProduct n) (a5OmittedRootDomain38 n) ∧
    (∀ p ∈ a5OmittedRootDomain38 n, rootProduct n p ≠ 0) := by
  have hpi : ((Lib.piN n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Lib.piN_ne_zero n
  refine ⟨?_, ?_, ?_⟩
  · rw [Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε x hx
    obtain ⟨r1, hr1, B, hB⟩ := a5Omitted_local_mass38 n x hx
    obtain ⟨r2, hr2, R, hbnd⟩ := a5Omitted_pair_local_bound38 n x hx
    obtain ⟨A, hAv, hAa⟩ := rootTau_l2_analytic38
    have hAc : ContinuousAt A x.1 := (hAa x.1 hx.1).continuousAt
    have hf0 : ContinuousAt (a5OmittedRootFactor38 n 0) x :=
      (a5OmittedRootFactor_analytic38 n 0 x hx).continuousAt
    set K : ℝ := ‖a5OmittedRootFactor38 n 0 x‖ + 1 with hK
    obtain ⟨r3, hr3, h3⟩ : ∃ r3 : ℝ, 0 < r3 ∧ ∀ q ∈ ball x r3,
        ‖a5OmittedRootFactor38 n 0 q‖ ≤ K := by
      have := hf0.norm.eventually (gt_mem_nhds (lt_add_one ‖a5OmittedRootFactor38 n 0 x‖))
      obtain ⟨r3, hr3, h⟩ := Metric.mem_nhds_iff.1 this
      exact ⟨r3, hr3, fun q hq => (h hq).le⟩
    set c : ℝ := ‖((Lib.piN n : ℝ) : ℂ)⁻¹‖ with hc
    have hc0 : 0 ≤ c := norm_nonneg _
    have hK0 : 0 ≤ K := by positivity
    set M : ℝ := c * K * Real.exp B with hM
    have hM0 : 0 ≤ M := by positivity
    set η : ℝ := ε / (2 * (M + 1)) with hη
    have hηpos : 0 < η := by positivity
    set s : ℝ := Real.log (1 + η) with hs
    have hspos : 0 < s := Real.log_pos (by linarith)
    have hexp : Real.exp s - 1 = η := by
      rw [hs, Real.exp_log (by linarith)]; ring
    have hMη : M * η < ε := by
      rw [hη]
      have : M * (ε / (2 * (M + 1))) = ε * (M / (2 * (M + 1))) := by ring
      rw [this]
      have h1 : M / (2 * (M + 1)) < 1 := by
        rw [div_lt_one (by positivity)]; linarith
      nlinarith
    set c1 : ℝ := Lib.majC1 with hc1
    have hc1n : 0 ≤ c1 := Lib.majC1_nonneg
    set c2 : ℝ := Lib.majC2 R with hc2
    have hc2n : 0 ≤ c2 := Lib.majC2_nonneg R
    set δ : ℝ := s / (4 * (c1 + 1)) with hδ
    have hδpos : 0 < δ := by positivity
    obtain ⟨V, hV, N1, hN1⟩ := lp_tail_cont A x.1 hAc δ hδpos
    have hT := tendsto_sum_nat_add (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2)
    have hT' := hT.const_mul c2
    rw [mul_zero] at hT'
    have hTev := hT'.eventually (gt_mem_nhds (show (0 : ℝ) < s / 2 by positivity))
    obtain ⟨N2, hN2⟩ := eventually_atTop.1 hTev
    refine ⟨a5OmittedRootDomain38 n ∩ (ball x (min r1 (min r2 r3)) ∩ {q | q.1 ∈ V}),
      inter_mem_nhdsWithin _ (inter_mem (ball_mem_nhds _ (lt_min hr1 (lt_min hr2 hr3)))
        (continuous_fst.continuousAt.preimage_mem_nhds hV)), ?_⟩
    refine eventually_atTop.2 ⟨max N1 N2, fun N hN q hq => ?_⟩
    obtain ⟨hqD, hqB, hqV⟩ := hq
    have hq1 : q ∈ ball x r1 := ball_subset_ball (min_le_left _ _) hqB
    have hq2 : q ∈ ball x r2 := ball_subset_ball ((min_le_left _ _).trans' (min_le_right _ _)) hqB
    have hq3 : q ∈ ball x r3 := ball_subset_ball ((min_le_right _ _).trans' (min_le_right _ _)) hqB
    obtain ⟨hSsum, hSle⟩ := hB q hq1 hqD
    -- the density d = rootTauQ38 q
    have hdeq : (fun m : ℤ => rootTauQ38 q m) = fun m : ℤ => ‖A q.1 m‖ ^ 2 := by
      funext m
      simp only [rootTauQ38]
      rw [hAv q.1 hqD.1 m]
    have hdsum : Summable (fun m : ℤ => rootTauQ38 q m) := by
      rw [hdeq]; exact (lp2_hasSum (A q.1)).summable
    have hd0 : ∀ m, 0 ≤ rootTauQ38 q m := rootTauQ_nonneg38 q
    have hN1N : N1 ≤ N := le_trans (le_max_left _ _) hN
    have hN2N : N2 ≤ N := le_trans (le_max_right _ _) hN
    have htl : tl (fun m => rootTauQ38 q m) N < δ := by
      refine lt_of_le_of_lt (tl_antitone hdsum hd0 hN1N) ?_
      rw [hdeq]; exact hN1 q.1 hqV
    have hmaj : Summable fun m : ℕ => Lib.pairMaj (rootTauQ38 q) R (m + N) :=
      (summable_nat_add_iff (f := Lib.pairMaj (rootTauQ38 q) R) N).mpr (Lib.summable_pairMaj hdsum R)
    have hSN : ∑' m : ℕ, ‖Lib.pairDev (fun j => a5OmittedRootFactor38 n j q) (m + N)‖ ≤ s := by
      have h1 : ∑' m : ℕ, ‖Lib.pairDev (fun j => a5OmittedRootFactor38 n j q) (m + N)‖ ≤
          ∑' m : ℕ, Lib.pairMaj (rootTauQ38 q) R (m + N) :=
        Summable.tsum_le_tsum (fun m => hbnd q (ball_subset_ball (min_le_right _ _ |>.trans (min_le_left _ _)) hqB |> fun h => by
            simpa using h) hqD (m + N)) ((summable_nat_add_iff N).mpr hSsum) hmaj
      have h2 := pairMaj_tail (rootTauQ38 q) hdsum hd0 R N
      have h3 : c2 * ∑' m : ℕ, 1 / (((m + N : ℕ) : ℝ) + 1) ^ 2 < s / 2 := by
        have := hN2 N hN2N
        simpa only [add_comm] using this
      have h4 : 2 * c1 * tl (fun m => rootTauQ38 q m) N ≤ s / 2 := by
        have : 2 * c1 * tl (fun m => rootTauQ38 q m) N ≤ 2 * c1 * δ :=
          mul_le_mul_of_nonneg_left htl.le (by positivity)
        refine this.trans ?_
        rw [hδ]
        have : 2 * c1 * (s / (4 * (c1 + 1))) = s / 2 * (c1 / (c1 + 1)) := by
          field_simp; ring
        rw [this]
        have h5 : c1 / (c1 + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
        nlinarith
      linarith
    have hdiff := prod_diff_bound (fun j => a5OmittedRootFactor38 n j q) hSsum N
    rw [dist_eq_norm]
    have e : rootProduct n q - (Lib.piN n : ℂ)⁻¹ *
        ∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a5OmittedRootFactor38 n m q =
        ((Lib.piN n : ℝ) : ℂ)⁻¹ * ((∏'[symmetricIcc ℤ] m, a5OmittedRootFactor38 n m q) -
          ∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a5OmittedRootFactor38 n m q) := by
      simp only [rootProduct, a5OmittedRootProduct38]
      ring
    rw [e, norm_mul]
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left hdiff hc0) ?_
    have hf0q : ‖a5OmittedRootFactor38 n 0 q‖ ≤ K := h3 q hq3
    have hexpB : Real.exp (∑' m : ℕ, ‖Lib.pairDev (fun j => a5OmittedRootFactor38 n j q) m‖) ≤
        Real.exp B := Real.exp_le_exp.mpr hSle
    have hexpS : Real.exp (∑' m : ℕ, ‖Lib.pairDev (fun j => a5OmittedRootFactor38 n j q) (m + N)‖)
        - 1 ≤ η := by
      rw [← hexp]; linarith [Real.exp_le_exp.mpr hSN]
    have hbig : ‖a5OmittedRootFactor38 n 0 q‖ *
        Real.exp (∑' m : ℕ, ‖Lib.pairDev (fun j => a5OmittedRootFactor38 n j q) m‖) *
        (Real.exp (∑' m : ℕ, ‖Lib.pairDev (fun j => a5OmittedRootFactor38 n j q) (m + N)‖) - 1)
        ≤ K * Real.exp B * η := by
      have hz : 0 ≤ Real.exp (∑' m : ℕ, ‖Lib.pairDev (fun j => a5OmittedRootFactor38 n j q) (m + N)‖) - 1 := by
        have := Real.add_one_le_exp (∑' m : ℕ, ‖Lib.pairDev (fun j => a5OmittedRootFactor38 n j q) (m + N)‖)
        have h0 : 0 ≤ ∑' m : ℕ, ‖Lib.pairDev (fun j => a5OmittedRootFactor38 n j q) (m + N)‖ :=
          tsum_nonneg fun _ => norm_nonneg _
        linarith
      calc _ ≤ (K * Real.exp B) * (Real.exp (∑' m : ℕ, ‖Lib.pairDev (fun j => a5OmittedRootFactor38 n j q) (m + N)‖) - 1) :=
            mul_le_mul_of_nonneg_right (mul_le_mul hf0q hexpB (Real.exp_nonneg _) hK0) hz
        _ ≤ K * Real.exp B * η := mul_le_mul_of_nonneg_left hexpS (by positivity)
    calc c * (‖a5OmittedRootFactor38 n 0 q‖ *
        Real.exp (∑' m : ℕ, ‖Lib.pairDev (fun j => a5OmittedRootFactor38 n j q) m‖) *
        (Real.exp (∑' m : ℕ, ‖Lib.pairDev (fun j => a5OmittedRootFactor38 n j q) (m + N)‖) - 1))
        ≤ c * (K * Real.exp B * η) := mul_le_mul_of_nonneg_left hbig hc0
      _ = M * η := by rw [hM]; ring
      _ < ε := hMη
  · have h := a5OmittedRoot_analytic38 n
    exact analyticOnNhd_const.mul h
  · intro p hp
    exact mul_ne_zero (inv_ne_zero hpi) (a5OmittedRoot_ne_zero38 n p hp)

end
end NlsGge.GKDefinitionDesign
