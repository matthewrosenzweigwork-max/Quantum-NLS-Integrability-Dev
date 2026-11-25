import Mathlib
import NlsGge.Atomic.G2.G2019
import NlsGge.Atomic.G2.G2021
import NlsGge.GK38.AbelianRatio

                                                                                                                                                                                                                                               

set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory SummationFilter
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section
namespace G2022Aux
open G2021Aux

theorem lp_tail_cont_gen {X : Type*} [TopologicalSpace X] (A : X → lp (fun _ : ℤ => ℂ) 2) (φ₀ : X)
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

theorem continuous_coord (n : ℤ) : Continuous (fun s : Lib.L2Seq => s n) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun s t => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  exact Lib.norm_coord_le (s - t) n

theorem continuous_shat (n : ℤ) :
    Continuous (fun x : ℂ × Lib.L2Seq => Lib.sOmit n x.2 x.1) := by
  unfold Lib.sOmit
  have hc : Continuous (fun x : ℂ × Lib.L2Seq =>
      x.1 + ((Lib.piN n : ℂ) - (n : ℂ) * (Real.pi : ℂ)) - x.2 n) :=
    (continuous_fst.add continuous_const).sub ((continuous_coord n).comp continuous_snd)
  exact continuous_snd.add (hc.smul continuous_const)

theorem continuous_F0 (n : ℤ) :
    Continuous (fun x : ℂ × Lib.L2Seq => Lib.omitFactor n x.2 x.1 0) := by
  unfold Lib.omitFactor
  by_cases h : (0 : ℤ) = n
  · simp only [h, ite_true]; exact continuous_const
  · simp only [h, ite_false, Lib.prodFactor, Lib.sigmaOf]
    refine Continuous.div_const ?_ _
    exact (continuous_const.add ((continuous_coord 0).comp continuous_snd)).sub continuous_fst

theorem num_tlu (n : ℤ) :
    TendstoLocallyUniformlyOn
      (fun N : ℕ => fun x : ℂ × Lib.L2Seq =>
        ∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), Lib.omitFactor n x.2 x.1 m)
      (fun x : ℂ × Lib.L2Seq => ∏'[symmetricIcc ℤ] m : ℤ, Lib.omitFactor n x.2 x.1 m)
      atTop univ := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  set d : ℂ × Lib.L2Seq → ℤ → ℝ := fun y m => ‖Lib.sOmit n y.2 y.1 m‖ ^ 2 with hdd
  have hdsum : ∀ y, Summable (d y) := fun y => (Lib.hasSum_sq_l2 (Lib.sOmit n y.2 y.1)).summable
  have hdtsum : ∀ y, ∑' m, d y m = ‖Lib.sOmit n y.2 y.1‖ ^ 2 :=
    fun y => (Lib.hasSum_sq_l2 (Lib.sOmit n y.2 y.1)).tsum_eq
  have hd0 : ∀ y m, 0 ≤ d y m := fun y m => sq_nonneg _
  have hfac : ∀ y : ℂ × Lib.L2Seq, (fun j => Lib.omitFactor n y.2 y.1 j) =
      Lib.prodFactor (Lib.sigmaOf (Lib.sOmit n y.2 y.1)) y.1 := fun y => by
    funext j; exact (Lib.prodFactor_sOmit n y.2 y.1 j).symm
  set R : ℝ := ‖x.1‖ + 1 with hR
  have hR0 : 0 ≤ R := by positivity
  set Bd : ℝ := ‖Lib.sOmit n x.2 x.1‖ ^ 2 + 1 with hBd
  set K : ℝ := ‖Lib.omitFactor n x.2 x.1 0‖ + 1 with hK
  have hK0 : 0 ≤ K := by positivity
  have hpb : ∀ y : ℂ × Lib.L2Seq, ‖y.1‖ ≤ R → ∀ m : ℕ,
      ‖Lib.pairDev (fun j => Lib.omitFactor n y.2 y.1 j) m‖ ≤ Lib.pairMaj (d y) R m := by
    intro y hy m
    rw [hfac y]
    exact Lib.pairTerm_le_maj hy (fun j => by
      rw [Lib.dev_sigmaOf]) m
  have hsum : ∀ y : ℂ × Lib.L2Seq, ‖y.1‖ ≤ R →
      Summable (fun m : ℕ => ‖Lib.pairDev (fun j => Lib.omitFactor n y.2 y.1 j) m‖) :=
    fun y hy => (Lib.summable_pairMaj (hdsum y) R).of_nonneg_of_le (fun _ => norm_nonneg _) (hpb y hy)
  have hnbd : ∀ᶠ y in 𝓝 x, ‖y.1‖ < R ∧ ‖Lib.sOmit n y.2 y.1‖ ^ 2 < Bd ∧
      ‖Lib.omitFactor n y.2 y.1 0‖ < K := by
    refine (continuous_fst.norm.continuousAt.eventually_lt_const (by rw [hR]; linarith)).and
      (Filter.Eventually.and ?_ ?_)
    · have hc2 : Continuous (fun y : ℂ × Lib.L2Seq => ‖Lib.sOmit n y.2 y.1‖ ^ 2) :=
        (continuous_shat n).norm.pow 2
      exact hc2.continuousAt.eventually_lt_const (by rw [hBd]; linarith)
    · exact ((continuous_F0 n).norm.continuousAt).eventually_lt_const (by rw [hK]; linarith)
  set c1 : ℝ := Lib.majC1 with hc1
  have hc1n : 0 ≤ c1 := Lib.majC1_nonneg
  set c2 : ℝ := Lib.majC2 R with hc2
  have hc2n : 0 ≤ c2 := Lib.majC2_nonneg R
  set Bm : ℝ := 2 * c1 * Bd + c2 * Lib.sumInvSq with hBm
  have hmass : ∀ y : ℂ × Lib.L2Seq, ‖y.1‖ ≤ R → ‖Lib.sOmit n y.2 y.1‖ ^ 2 < Bd →
      ∑' m : ℕ, ‖Lib.pairDev (fun j => Lib.omitFactor n y.2 y.1 j) m‖ ≤ Bm := by
    intro y hy hyB
    refine (Summable.tsum_le_tsum (hpb y hy) (hsum y hy) (Lib.summable_pairMaj (hdsum y) R)).trans ?_
    refine (Lib.tsum_pairMaj_le (hdsum y) (hd0 y) R).trans ?_
    rw [hdtsum y]
    have := Lib.sumInvSq_nonneg
    nlinarith
  set M : ℝ := K * Real.exp Bm with hM
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
  set δ : ℝ := s / (4 * (c1 + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨V, hV, N1, hN1⟩ := lp_tail_cont_gen (fun y : ℂ × Lib.L2Seq => Lib.sOmit n y.2 y.1) x
    (continuous_shat n).continuousAt δ hδpos
  have hT := tendsto_sum_nat_add (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2)
  have hT' := hT.const_mul c2
  rw [mul_zero] at hT'
  have hTev := hT'.eventually (gt_mem_nhds (show (0 : ℝ) < s / 2 by positivity))
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 hTev
  refine ⟨{y | ‖y.1‖ < R ∧ ‖Lib.sOmit n y.2 y.1‖ ^ 2 < Bd ∧
      ‖Lib.omitFactor n y.2 y.1 0‖ < K} ∩ V, ?_, ?_⟩
  · rw [nhdsWithin_univ]
    exact Filter.inter_mem hnbd hV
  refine eventually_atTop.2 ⟨max N1 N2, fun N hN y hy => ?_⟩
  obtain ⟨⟨hyR, hyB, hyK⟩, hyV⟩ := hy
  have hN1N : N1 ≤ N := le_trans (le_max_left _ _) hN
  have hN2N : N2 ≤ N := le_trans (le_max_right _ _) hN
  have hSsum := hsum y hyR.le
  have htl : tl (d y) N < δ :=
    lt_of_le_of_lt (tl_antitone (hdsum y) (hd0 y) hN1N) (hN1 y hyV)
  have hmaj : Summable fun m : ℕ => Lib.pairMaj (d y) R (m + N) :=
    (summable_nat_add_iff (f := Lib.pairMaj (d y) R) N).mpr (Lib.summable_pairMaj (hdsum y) R)
  have hSN : ∑' m : ℕ, ‖Lib.pairDev (fun j => Lib.omitFactor n y.2 y.1 j) (m + N)‖ ≤ s := by
    have h1 : ∑' m : ℕ, ‖Lib.pairDev (fun j => Lib.omitFactor n y.2 y.1 j) (m + N)‖ ≤
        ∑' m : ℕ, Lib.pairMaj (d y) R (m + N) :=
      Summable.tsum_le_tsum (fun m => hpb y hyR.le (m + N)) ((summable_nat_add_iff N).mpr hSsum) hmaj
    have h2 := pairMaj_tail (d y) (hdsum y) (hd0 y) R N
    have h3 : c2 * ∑' m : ℕ, 1 / (((m + N : ℕ) : ℝ) + 1) ^ 2 < s / 2 := by
      have := hN2 N hN2N
      simpa only [add_comm] using this
    have h4 : 2 * c1 * tl (d y) N ≤ s / 2 := by
      have : 2 * c1 * tl (d y) N ≤ 2 * c1 * δ :=
        mul_le_mul_of_nonneg_left htl.le (by positivity)
      refine this.trans ?_
      rw [hδ]
      have : 2 * c1 * (s / (4 * (c1 + 1))) = s / 2 * (c1 / (c1 + 1)) := by
        field_simp; ring
      rw [this]
      have h5 : c1 / (c1 + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
      nlinarith
    linarith
  have hdiff := prod_diff_bound (fun j => Lib.omitFactor n y.2 y.1 j) hSsum N
  rw [dist_eq_norm]
  refine lt_of_le_of_lt hdiff ?_
  have hexpB : Real.exp (∑' m : ℕ, ‖Lib.pairDev (fun j => Lib.omitFactor n y.2 y.1 j) m‖) ≤
      Real.exp Bm := Real.exp_le_exp.mpr (hmass y hyR.le hyB)
  have hexpS : Real.exp (∑' m : ℕ, ‖Lib.pairDev (fun j => Lib.omitFactor n y.2 y.1 j) (m + N)‖)
      - 1 ≤ η := by
    rw [← hexp]; linarith [Real.exp_le_exp.mpr hSN]
  have hz : 0 ≤ Real.exp (∑' m : ℕ, ‖Lib.pairDev (fun j => Lib.omitFactor n y.2 y.1 j) (m + N)‖) - 1 := by
    have := Real.add_one_le_exp (∑' m : ℕ, ‖Lib.pairDev (fun j => Lib.omitFactor n y.2 y.1 j) (m + N)‖)
    have h0 : 0 ≤ ∑' m : ℕ, ‖Lib.pairDev (fun j => Lib.omitFactor n y.2 y.1 j) (m + N)‖ :=
      tsum_nonneg fun _ => norm_nonneg _
    linarith
  calc ‖Lib.omitFactor n y.2 y.1 0‖ *
        Real.exp (∑' m : ℕ, ‖Lib.pairDev (fun j => Lib.omitFactor n y.2 y.1 j) m‖) *
        (Real.exp (∑' m : ℕ, ‖Lib.pairDev (fun j => Lib.omitFactor n y.2 y.1 j) (m + N)‖) - 1)
      ≤ (K * Real.exp Bm) * (Real.exp (∑' m : ℕ, ‖Lib.pairDev (fun j => Lib.omitFactor n y.2 y.1 j) (m + N)‖) - 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hyK.le hexpB (Real.exp_nonneg _) hK0) hz
    _ ≤ M * η := mul_le_mul_of_nonneg_left hexpS hM0
    _ < ε := hMη

theorem ratio_eq (n : ℤ) (p : (PotPair × Lib.L2Seq) × ℂ) :
    p2OmittedRatio38 n p =
      (∏'[symmetricIcc ℤ] m : ℤ, Lib.omitFactor n p.1.2 p.2 m) /
        a5OmittedRootProduct38 n (p.1.1, p.2) := by
  have hpi : (Lib.piN n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero n)
  unfold p2OmittedRatio38 Lib.omitProd
  have : (∏'[symmetricIcc ℤ] m : ℤ, (if m = n then (1 : ℂ) else Lib.prodFactor (Lib.sigmaOf p.1.2) p.2 m))
      = ∏'[symmetricIcc ℤ] m : ℤ, Lib.omitFactor n p.1.2 p.2 m := rfl
  rw [this, ← mul_assoc, mul_one_div_cancel hpi, one_mul]

theorem fin_eq (n : ℤ) (N : ℕ) (p : (PotPair × Lib.L2Seq) × ℂ) :
    (∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        if m = n then (1 : ℂ) else
          (Lib.sigmaOf p.1.2 m - p.2) / standardRoot p.1.1 m p.2) =
      (∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), Lib.omitFactor n p.1.2 p.2 m) /
        ∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a5OmittedRootFactor38 n m (p.1.1, p.2) := by
  rw [← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun m _ => ?_
  by_cases h : m = n
  · simp [Lib.omitFactor, a5OmittedRootFactor38, h]
  · have hc : (Lib.piN m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero m)
    simp only [Lib.omitFactor, a5OmittedRootFactor38, h, ite_false, Lib.prodFactor, rootFactor38,
      standardRoot]
    have hcs : (Lib.piN m : ℂ) * (stdRoot38 (tauN p.1.1 m) (gamma2 p.1.1 m) p.2 / (Lib.piN m : ℂ)) =
        stdRoot38 (tauN p.1.1 m) (gamma2 p.1.1 m) p.2 := by field_simp
    rw [div_div, hcs]

/-- the omitted-gap domain pulled back to the triple space -/
def Sdom (n : ℤ) : Set ((PotPair × Lib.L2Seq) × ℂ) :=
  {p | (p.1.1,p.2) ∈ a5OmittedRootDomain38 n}

theorem hPc : Continuous (fun p : (PotPair × Lib.L2Seq) × ℂ => ((p.2, p.1.2) : ℂ × Lib.L2Seq)) :=
  continuous_snd.prodMk (continuous_snd.comp continuous_fst)

theorem hQc : Continuous (fun p : (PotPair × Lib.L2Seq) × ℂ => ((p.1.1, p.2) : PotPair × ℂ)) :=
  (continuous_fst.comp continuous_fst).prodMk continuous_snd

theorem hQS (n : ℤ) : MapsTo (fun p : (PotPair × Lib.L2Seq) × ℂ => ((p.1.1, p.2) : PotPair × ℂ))
    (Sdom n) (a5OmittedRootDomain38 n) := fun _ hp => hp

theorem num_tlu_S (n : ℤ) :
    TendstoLocallyUniformlyOn
      (fun (N : ℕ) (p : (PotPair × Lib.L2Seq) × ℂ) =>
        ∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), Lib.omitFactor n p.1.2 p.2 m)
      (fun p : (PotPair × Lib.L2Seq) × ℂ =>
        ∏'[symmetricIcc ℤ] m : ℤ, Lib.omitFactor n p.1.2 p.2 m) atTop (Sdom n) :=
  (num_tlu n).comp (fun p : (PotPair × Lib.L2Seq) × ℂ => ((p.2, p.1.2) : ℂ × Lib.L2Seq))
    (t := Sdom n) (mapsTo_univ _ _) hPc.continuousOn

theorem den_tlu_S (n : ℤ) :
    TendstoLocallyUniformlyOn
      (fun N : ℕ => fun p : (PotPair × Lib.L2Seq) × ℂ =>
        ∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a5OmittedRootFactor38 n m (p.1.1, p.2))
      (fun p => a5OmittedRootProduct38 n (p.1.1, p.2)) atTop (Sdom n) := by
  have hpi : (Lib.piN n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero n)
  have hG21 := (G2_021 n).1
  have hg : UniformContinuous (fun w : ℂ => (Lib.piN n : ℂ) * w) :=
    uniformContinuous_const_smul (Lib.piN n : ℂ)
  have hDen0 := (hg.comp_tendstoLocallyUniformlyOn hG21).comp
    (fun p : (PotPair × Lib.L2Seq) × ℂ => ((p.1.1, p.2) : PotPair × ℂ)) (t := Sdom n)
    (hQS n) hQc.continuousOn
  refine (hDen0.congr (fun N p _ => ?_)).congr_right (fun p _ => ?_)
  · simp only [Function.comp]
    rw [← mul_assoc, mul_inv_cancel₀ hpi, one_mul]
  · simp only [Function.comp, rootProduct]
    rw [← mul_assoc, mul_inv_cancel₀ hpi, one_mul]

theorem pd_cont (n : ℤ) : ContinuousOn
    (fun p : (PotPair × Lib.L2Seq) × ℂ => a5OmittedRootProduct38 n (p.1.1, p.2)) (Sdom n) :=
  ((a5OmittedRoot_analytic38 n).continuousOn).comp hQc.continuousOn (hQS n)

theorem pd_ne (n : ℤ) : ∀ p ∈ Sdom n, a5OmittedRootProduct38 n (p.1.1, p.2) ≠ 0 :=
  fun p hp => a5OmittedRoot_ne_zero38 n (p.1.1, p.2) hp

theorem pn_eq (n : ℤ) (p : (PotPair × Lib.L2Seq) × ℂ) :
    (∏'[symmetricIcc ℤ] m : ℤ, Lib.omitFactor n p.1.2 p.2 m) =
      (Lib.piN n : ℂ) * Lib.omitProd n p.1.2 p.2 := by
  have hpi : (Lib.piN n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero n)
  have : (∏'[symmetricIcc ℤ] m : ℤ, (if m = n then (1 : ℂ) else Lib.prodFactor (Lib.sigmaOf p.1.2) p.2 m))
      = ∏'[symmetricIcc ℤ] m : ℤ, Lib.omitFactor n p.1.2 p.2 m := rfl
  unfold Lib.omitProd
  rw [this, ← mul_assoc, mul_one_div_cancel hpi, one_mul]

theorem omitProd_cont (n : ℤ) :
    Continuous (fun q : ℂ × Lib.L2Seq => Lib.omitProd n q.2 q.1) :=
  continuousOn_univ.1 (Lib.analyticOnNhd_omitProd n).continuousOn

theorem omitProd_cont3 (n : ℤ) :
    Continuous (fun p : (PotPair × Lib.L2Seq) × ℂ => Lib.omitProd n p.1.2 p.2) := by
  have h := (omitProd_cont n).comp hPc
  exact h

theorem pn_cont (n : ℤ) : ContinuousOn (fun p : (PotPair × Lib.L2Seq) × ℂ =>
      ∏'[symmetricIcc ℤ] m : ℤ, Lib.omitFactor n p.1.2 p.2 m) (Sdom n) := by
  have e : (fun p : (PotPair × Lib.L2Seq) × ℂ =>
      ∏'[symmetricIcc ℤ] m : ℤ, Lib.omitFactor n p.1.2 p.2 m) =
      fun p => (Lib.piN n : ℂ) * Lib.omitProd n p.1.2 p.2 := funext (pn_eq n)
  rw [e]
  exact (continuous_const.mul (omitProd_cont3 n)).continuousOn

theorem mul_tlu_S (n : ℤ) :
    TendstoLocallyUniformlyOn
      (fun (N : ℕ) (p : (PotPair × Lib.L2Seq) × ℂ) =>
        (∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), Lib.omitFactor n p.1.2 p.2 m) *
          (∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a5OmittedRootFactor38 n m (p.1.1, p.2))⁻¹)
      (fun p : (PotPair × Lib.L2Seq) × ℂ =>
        (∏'[symmetricIcc ℤ] m : ℤ, Lib.omitFactor n p.1.2 p.2 m) *
          (a5OmittedRootProduct38 n (p.1.1, p.2))⁻¹) atTop (Sdom n) := by
  have hinv := (den_tlu_S n).inv₀_of_disjoint (fun x hx => by
    have h1 := (pd_cont n x hx).tendsto
    exact (disjoint_nhds_nhds.2 (pd_ne n x hx)).mono_left h1)
  exact (num_tlu_S n).mul₀ hinv (pn_cont n) ((pd_cont n).inv₀ (pd_ne n))

end G2022Aux

open G2022Aux

theorem G2_022 (n : ℤ) :
    AnalyticOnNhd ℂ (p2OmittedRatio38 n)
      {p : (PotPair × Lib.L2Seq) × ℂ |
        (p.1.1,p.2) ∈ a5OmittedRootDomain38 n} ∧
    TendstoLocallyUniformlyOn
      (fun N : ℕ => fun p : (PotPair × Lib.L2Seq) × ℂ =>
        ∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          if m=n then (1 : ℂ) else
            (Lib.sigmaOf p.1.2 m-p.2)/standardRoot p.1.1 m p.2)
      (p2OmittedRatio38 n) atTop
      {p : (PotPair × Lib.L2Seq) × ℂ |
        (p.1.1,p.2) ∈ a5OmittedRootDomain38 n} := by
  refine ⟨p2OmittedRatio_analytic38 n, ?_⟩
  refine ((mul_tlu_S n).congr (fun N p _ => ?_)).congr_right (fun p _ => ?_)
  · rw [fin_eq, div_eq_mul_inv]
  · rw [ratio_eq, div_eq_mul_inv]

end
end NlsGge.GKDefinitionDesign
