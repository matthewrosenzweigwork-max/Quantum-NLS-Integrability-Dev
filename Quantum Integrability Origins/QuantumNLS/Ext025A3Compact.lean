import QuantumNLS.Ext025A2Fourier
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Finite symmetric cutoffs and compact lower-weight inclusions.
DEF-002 and F04 are kept as distinct weights. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Set Filter Topology
open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
namespace QuantumNLS.Ext025A3

/-- A finite coordinate projection in the declared weighted Hilbert norm. -/
def head (W : PosWeight) (s : Finset ℤ) : WSeq W →L[ℂ] WSeq W :=
  (toL2ᵢ W).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((∑ n ∈ s, (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 n).comp
      (lp.evalCLM (𝕜 := ℂ) (E := fun _ : ℤ => ℂ) (p := 2) n)).comp
      (toL2ᵢ W).toContinuousLinearEquiv.toContinuousLinearMap)

theorem head_val (W : PosWeight) (s : Finset ℤ) (x : WSeq W) (n : ℤ) :
    (head W s x).val n = if n ∈ s then x.val n else 0 := by
  have he := congrArg (fun z : lp (fun _ : ℤ => ℂ) 2 => z n)
    ((toL2ᵢ W).apply_symm_apply
      (∑ j ∈ s, lp.single 2 j ((toL2ᵢ W x) j)))
  have hh : head W s x = (toL2ᵢ W).symm
      (∑ j ∈ s, lp.single 2 j ((toL2ᵢ W x) j)) := by
    simp only [head, ContinuousLinearMap.comp_apply, sum_apply,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
      lp.singleContinuousLinearMap_apply]
    rfl
  rw [← hh] at he
  change (Real.sqrt (W.w n) : ℂ) * (head W s x).val n = _ at he
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single] at he
  change (Real.sqrt (W.w n) : ℂ) * (head W s x).val n =
    if n ∈ s then (Real.sqrt (W.w n) : ℂ) * x.val n else 0 at he
  split_ifs with hn
  · rw [ite_eq_left hn] at he
    exact mul_left_cancel₀ (sqrt_ne_zero' W n) he
  · rw [ite_eq_right hn] at he
    exact (mul_eq_zero.mp he).resolve_left (sqrt_ne_zero' W n)

theorem head_compact (W : PosWeight) (s : Finset ℤ) : IsCompactOperator (head W s) := by
  have hi : ∀ n : ℤ, IsCompactOperator
      ((lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 n).comp
        (lp.evalCLM (𝕜 := ℂ) (E := fun _ : ℤ => ℂ) (p := 2) n)) := by
    intro n
    exact (isCompactOperator_of_locallyCompactSpace_rng
      (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 n)).comp_clm _
  have hs : IsCompactOperator
      ((∑ n ∈ s, (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 n).comp
        (lp.evalCLM (𝕜 := ℂ) (E := fun _ : ℤ => ℂ) (p := 2) n)) :
        lp (fun _ : ℤ => ℂ) 2 →L[ℂ] lp (fun _ : ℤ => ℂ) 2) := by
    induction s using Finset.induction_on with
    | empty => simpa using (isCompactOperator_zero :
        IsCompactOperator (0 : lp (fun _ : ℤ => ℂ) 2 → lp (fun _ : ℤ => ℂ) 2))
    | @insert n s hn ih =>
      rw [Finset.sum_insert hn]
      convert (hi n).add ih using 1
  exact (hs.comp_clm (toL2ᵢ W).toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
    (toL2ᵢ W).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- The weighted tail estimate in the actual target norm, uniformly on the source ball. -/
theorem head_error {W V : PosWeight} {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (h : ∀ n, W.w n ≤ C * V.w n) (s : Finset ℤ)
    (ht : ∀ n ∉ s, W.w n ≤ δ ^ 2 * V.w n) (x : WSeq V) :
    ‖incl W V hC h x - head W s (incl W V hC h x)‖ ≤ δ * ‖x‖ := by
  have hb : ‖incl W V hC h x - head W s (incl W V hC h x)‖ ^ 2 ≤ δ ^ 2 * ‖x‖ ^ 2 := by
    rw [norm_sq_eq_tsum, norm_sq_eq_tsum, ← tsum_mul_left]
    apply Summable.tsum_le_tsum _ (WSeq.summable _) (x.summable.mul_left _)
    intro n
    simp only [WSeq.val_sub, Pi.sub_apply, head_val, incl_val]
    split_ifs with hn
    · simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, mul_zero]
      exact mul_nonneg (sq_nonneg _) (mul_nonneg (V.pos n).le (sq_nonneg _))
    · simp only [sub_zero]
      nlinarith [mul_le_mul_of_nonneg_right (ht n hn) (sq_nonneg ‖x.val n‖)]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hδ (norm_nonneg _))).mp
    (by simpa only [mul_pow] using hb)

/-- A finite head and a uniform vanishing tail prove compactness without a
minimum exponent gap: every strictly positive gap will supply this condition. -/
theorem compact_incl {W V : PosWeight} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n, W.w n ≤ C * V.w n)
    (ht : ∀ δ > 0, ∃ s : Finset ℤ, ∀ n ∉ s, W.w n ≤ δ ^ 2 * V.w n) :
    IsCompactOperator (incl W V hC h) := by
  have hc : IsClosed {T : WSeq V →L[ℂ] WSeq W | IsCompactOperator T} :=
    isClosed_setOfPred_isCompactOperator
  apply hc.closure_subset
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨s, hs⟩ := ht (ε / 2) (by positivity)
  refine ⟨(head W s).comp (incl W V hC h), (head_compact W s).comp_clm _, ?_⟩
  have hn : ‖incl W V hC h - (head W s).comp (incl W V hC h)‖ ≤ ε / 2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x
    exact head_error hC (by positivity) h s hs x
  rw [dist_eq_norm]
  exact hn.trans_lt (by linarith)

/-- The report's symmetric frequency set, including both endpoints. -/
def symmetricCut (K : ℕ) : Finset ℤ := Finset.Icc (-(K : ℤ)) K

theorem outside_symmetricCut {K : ℕ} {n : ℤ} (hn : n ∉ symmetricCut K) :
    (K : ℝ) < |(n : ℝ)| := by
  by_contra h
  have hle := abs_le.mp (le_of_not_gt h)
  apply hn
  simp only [symmetricCut, Finset.mem_Icc]
  constructor
  · exact_mod_cast hle.1
  · exact_mod_cast hle.2

/-- Growth of either declared base follows from its linear frequency lower bound. -/
theorem frequency_growth {q : ℤ → ℝ} {c : ℝ} (hc : 0 < c)
    (hq : ∀ n : ℤ, c * |(n : ℝ)| ≤ q n) (b : ℝ) :
    ∃ K : ℕ, ∀ n ∉ symmetricCut K, b ≤ q n := by
  obtain ⟨K, hK⟩ := exists_nat_gt (b / c)
  refine ⟨K, fun n hn => ?_⟩
  have hn' := outside_symmetricCut hn
  have hb : b < c * K := by
    have := (div_lt_iff₀ hc).mp hK
    nlinarith
  exact (hb.le.trans (mul_le_mul_of_nonneg_left hn'.le hc.le)).trans (hq n)

/-- Every strict power difference gives a vanishing uniform tail. -/
theorem power_tail {q : ℤ → ℝ} (hq : ∀ n, 0 < q n)
    (hgrowth : ∀ b : ℝ, ∃ K : ℕ, ∀ n ∉ symmetricCut K, b ≤ q n)
    {s t : ℝ} (hst : t < s) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℕ, ∀ n ∉ symmetricCut K, (q n) ^ t ≤ δ ^ 2 * (q n) ^ s := by
  have hz := tendsto_rpow_neg_atTop (sub_pos.mpr hst)
  have hev : ∀ᶠ b : ℝ in atTop, b ^ (t - s) < δ ^ 2 := by
    simpa only [neg_sub] using hz.eventually (gt_mem_nhds (sq_pos_of_pos hδ))
  obtain ⟨b, hb⟩ := (eventually_atTop.1 hev)
  obtain ⟨K, hK⟩ := hgrowth (max 1 b)
  refine ⟨K, fun n hn => ?_⟩
  have hn' := hK n hn
  have hpow := hb (q n) ((le_max_right 1 b).trans hn')
  calc
    (q n) ^ t = (q n) ^ (t - s) * (q n) ^ s := by
      rw [← Real.rpow_add (hq n)]; congr 1; ring
    _ ≤ δ ^ 2 * (q n) ^ s :=
      mul_le_mul_of_nonneg_right hpow.le (Real.rpow_nonneg (hq n).le _)

/-- ROOT-01 compactness at every strict exponent difference in DEF-002. -/
theorem root01_def002_compact {L s t : ℝ} (hL : 0 < L) (hst : t < s) :
    IsCompactOperator (h02_mono L hst.le) := by
  apply compact_incl (C := 1) zero_le_one (def002_le_of_le L hst.le)
  intro δ hδ
  let q : ℤ → ℝ := fun n => 1 + |2 * Real.pi * (n : ℝ) / L|
  have he : ∀ n : ℤ, |2 * Real.pi * (n : ℝ) / L| =
      (2 * Real.pi / L) * |(n : ℝ)| := by
    intro n
    rw [abs_div, abs_mul, abs_of_pos (mul_pos (by norm_num) Real.pi_pos), abs_of_pos hL]
    ring
  have hg := frequency_growth (q := q) (c := 2 * Real.pi / L) (by positivity)
    (fun n => by dsimp [q]; rw [he]; linarith)
  obtain ⟨K, hK⟩ := power_tail (q := q) (fun n => by dsimp [q]; positivity)
    hg (s := 2*s) (t := 2*t) (by linarith) hδ
  exact ⟨symmetricCut K, hK⟩

/-- ROOT-01 compactness for the distinct F04 bracket norm. -/
theorem root01_f04_compact {L s t : ℝ} (hL : 0 < L) (hst : t < s) :
    IsCompactOperator (h04_mono L hst.le) := by
  apply compact_incl (C := 1) zero_le_one (f04W_le_of_le L hst.le)
  intro δ hδ
  let c : ℝ := 2 * Real.pi / L
  let q : ℤ → ℝ := fun n => 1 + (QuantumNLS.Fourier.freq L n) ^ 2
  have hc : 0 < c := by dsimp [c]; positivity
  have he : ∀ n : ℤ, (QuantumNLS.Fourier.freq L n) ^ 2 = (c * |(n : ℝ)|) ^ 2 := by
    intro n
    dsimp [QuantumNLS.Fourier.freq, c]
    rw [mul_pow, sq_abs]
    ring
  have hg := frequency_growth (q := q) hc (fun n => by
    dsimp [q]; rw [he]; nlinarith [sq_nonneg (c * |(n : ℝ)| - 1/2)])
  obtain ⟨K, hK⟩ := power_tail (q := q) (fun n => by dsimp [q]; positivity) hg hst hδ
  exact ⟨symmetricCut K, hK⟩

/-- The coordinate projection used above is precisely the source symmetric cutoff. -/
theorem symmetric_cutoff_val (W : PosWeight) (K : ℕ) (x : WSeq W) (n : ℤ) :
    (head W (symmetricCut K) x).val n =
      if -(K : ℤ) ≤ n ∧ n ≤ K then x.val n else 0 := by
  simp only [head_val, symmetricCut, Finset.mem_Icc]

end QuantumNLS.Ext025A3
#print axioms QuantumNLS.Ext025A3.head_val
#print axioms QuantumNLS.Ext025A3.head_compact
#print axioms QuantumNLS.Ext025A3.head_error
#print axioms QuantumNLS.Ext025A3.compact_incl
#print axioms QuantumNLS.Ext025A3.power_tail
#print axioms QuantumNLS.Ext025A3.root01_def002_compact
#print axioms QuantumNLS.Ext025A3.root01_f04_compact
#print axioms QuantumNLS.Ext025A3.symmetric_cutoff_val
