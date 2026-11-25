import Mathlib
import QuantumNLS.LocalHeight

/-!
# CC:F04:local-height, uniform in the index (for the separation clause of CC:F04:selection, R-F4C3E5BE)

Source: `F04.tex`, Lemma `CC:F04:local-height` and its proof, and the last paragraph of the proof of `CC:F04:selection`:
"If (CC:F04:separation) failed, a subsequence would have another root `q_{j_N,N}(s_N(λ)) → x(λ)`. Lemma CC:F04:local-height, applied to these interpolated arrays, would force its real label to tend to `λ`."

`LocalHeight.local_height` is stated for one index sequence `i_N` along the full sequence of arrays. The separation argument needs the statement for index sequences defined only along a subsequence.
`local_height_uniform` is the equivalent uniform form: the same hypotheses (`RealBethe`, weak convergence of the empirical measures, `x ∉ supp μ`) give, for every `η > 0`, an `ε₀ > 0` such that for all large `N` and **all** indices `j` with `|q_{j,N} − x| ≤ ε₀`, `|ν_{j,N} − θ(x)/π| ≤ η`.
The proof is the printed one (cluster `[x − 2ε, x + 2ε]` with `K_N/N → 0`, the cluster comparison `LocalHeight.cluster_bound`, the deterministic external-limit estimate `LocalHeight.force_approx`), with the error terms tracked uniformly in `j`.
`LocalHeight` is read-only; its lemmas are reused.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section
open scoped BigOperators Topology BoundedContinuousFunction
open Finset Filter MeasureTheory

namespace QuantumNLS.LocalHeightUniform

open QuantumNLS.LocalHeight

theorem local_height_uniform {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {q ν : (N : ℕ) → Fin (N + 1) → ℝ}
    (hB : ∀ N, RealBethe L κ N (q N) (ν N)) (hw : EmpiricalWeakConv q μ)
    {x : ℝ} (hsupp : x ∉ μ.support) {η : ℝ} (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ᶠ N : ℕ in atTop, ∀ j : Fin (N + 1), |q N j - x| ≤ ε₀ →
      |ν N j - theta L κ μ x / Real.pi| ≤ η := by
  -- (A) a `μ`-null neighbourhood of `x`
  obtain ⟨U, hU, hU0⟩ := Measure.notMem_support_iff_exists.mp hsupp
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = r / 8 := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hnull : μ (Set.Icc (x - 4 * ε) (x + 4 * ε)) = 0 := by
    refine measure_mono_null (fun y hy => hball ?_) hU0
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  have hae : ∀ᵐ y ∂μ, 4 * ε < |y - x| := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with y hy
    by_contra h
    push Not at h
    exact hy ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩
  have hab : x - 2 * ε ≤ x + 2 * ε := by linarith
  -- (B) `K_N / N → 0`
  set f1 : ℝ → ℝ := fun y => max 0 (min 1 (3 - |y - x| / ε)) with hf1
  have hf1c : Continuous f1 :=
    continuous_const.max (continuous_const.min (continuous_const.sub
      ((continuous_id.sub continuous_const).abs.div_const ε)))
  have hf1b : ∀ y, ‖f1 y‖ ≤ 1 := by
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    exact max_le zero_le_one (min_le_left _ _)
  have hf1int : ∫ y, (BoundedContinuousFunction.ofNormedAddCommGroup f1 hf1c 1 hf1b) y ∂μ = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hae] with y hy
    simp only [BoundedContinuousFunction.coe_ofNormedAddCommGroup, hf1, Pi.zero_apply]
    have : 3 - |y - x| / ε < 0 := by
      rw [sub_neg, lt_div_iff₀ hε]; linarith
    rw [min_eq_right (by linarith), max_eq_left this.le]
  have hK : Tendsto (fun N : ℕ =>
      ((cluster (x - 2 * ε) (x + 2 * ε) (q N)).card : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    have h := hw (BoundedContinuousFunction.ofNormedAddCommGroup f1 hf1c 1 hf1b)
    rw [hf1int] at h
    refine squeeze_zero (fun N => by positivity) (fun N => ?_) h
    simp only [BoundedContinuousFunction.coe_ofNormedAddCommGroup]
    rw [div_eq_mul_inv, mul_comm, one_div]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h1 : ((cluster (x - 2 * ε) (x + 2 * ε) (q N)).card : ℝ) =
        ∑ j ∈ cluster (x - 2 * ε) (x + 2 * ε) (q N), f1 (q N j) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := (Finset.mem_filter.mp hj).2
      have : |q N j - x| ≤ 2 * ε := abs_le.mpr ⟨by linarith [hj'.1], by linarith [hj'.2]⟩
      have h3 : 1 ≤ 3 - |q N j - x| / ε := by
        rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hε]; linarith
      simp only [hf1]
      rw [min_eq_left h3, max_eq_right zero_le_one]
    rw [h1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => le_max_left _ _)
  -- (C) the kernel
  have hgint : ∫ y, (gBCF x ε hε) y ∂μ = ∫ y, 1 / (x - y) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    show gK x ε y = 1 / (x - y)
    exact gK_eq hε (by rw [abs_sub_comm]; linarith)
  have hA : Tendsto (fun N : ℕ => (1 / ((N : ℝ) + 1)) * ∑ j, gK x ε (q N j)) atTop
      (𝓝 (∫ y, 1 / (x - y) ∂μ)) := by
    rw [← hgint]; exact hw (gBCF x ε hε)
  -- (D) the choice of `ε₀`
  have hC : 0 < 4 * κ / ε ^ 2 + 2 * L := by positivity
  set ε₀ : ℝ := min (ε / 2) (Real.pi * η / (4 * κ / ε ^ 2 + 2 * L)) with hε₀
  have hε₀pos : 0 < ε₀ := lt_min (by positivity) (by have := Real.pi_pos; positivity)
  have hε₀1 : ε₀ ≤ ε / 2 := min_le_left _ _
  have hε₀2 : (4 * κ / ε ^ 2 + 2 * L) * ε₀ ≤ Real.pi * η := by
    have : ε₀ ≤ Real.pi * η / (4 * κ / ε ^ 2 + 2 * L) := min_le_right _ _
    rwa [le_div_iff₀ hC, mul_comm] at this
  refine ⟨ε₀, hε₀pos, ?_⟩
  -- (E) the uniform eventual estimates
  have hbd : Tendsto (fun N : ℕ => 4 * Real.sqrt (κ / L *
      (((cluster (x - 2 * ε) (x + 2 * ε) (q N)).card : ℝ) / ((N : ℝ) + 1)))) atTop (𝓝 0) := by
    have h0 := hK.const_mul (κ / L)
    rw [mul_zero] at h0
    have := ((Real.continuous_sqrt.tendsto 0).comp h0).const_mul 4
    simpa using this
  have hev1 : ∀ᶠ N : ℕ in atTop, 4 * Real.sqrt (κ / L *
      (((cluster (x - 2 * ε) (x + 2 * ε) (q N)).card : ℝ) / ((N : ℝ) + 1))) < ε₀ :=
    hbd.eventually (gt_mem_nhds hε₀pos)
  have hres : Tendsto (fun N : ℕ => 2 * (κ ^ 3 / ε ^ 3 * (1 / ((N : ℝ) + 1)) ^ 2 +
      κ / ε * (((cluster (x - 2 * ε) (x + 2 * ε) (q N)).card : ℝ) / ((N : ℝ) + 1))) +
      2 * κ * |(1 / ((N : ℝ) + 1)) * ∑ j, gK x ε (q N j) - ∫ y, 1 / (x - y) ∂μ|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (1 / ((N : ℝ) + 1)) ^ 2) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
      simpa using this
    have h2 : Tendsto (fun N : ℕ => |(1 / ((N : ℝ) + 1)) * ∑ j, gK x ε (q N j) -
        ∫ y, 1 / (x - y) ∂μ|) atTop (𝓝 0) := by
      have h0 : Tendsto (fun N : ℕ => (1 / ((N : ℝ) + 1)) * ∑ j, gK x ε (q N j) -
          ∫ y, 1 / (x - y) ∂μ) atTop (𝓝 0) := by
        simpa using hA.sub_const (∫ y, 1 / (x - y) ∂μ)
      simpa using h0.abs
    have := ((((h1.const_mul (κ ^ 3 / ε ^ 3)).add (hK.const_mul (κ / ε))).const_mul 2).add
      (h2.const_mul (2 * κ)))
    simpa using this
  have hev2 : ∀ᶠ N : ℕ in atTop, 2 * (κ ^ 3 / ε ^ 3 * (1 / ((N : ℝ) + 1)) ^ 2 +
      κ / ε * (((cluster (x - 2 * ε) (x + 2 * ε) (q N)).card : ℝ) / ((N : ℝ) + 1))) +
      2 * κ * |(1 / ((N : ℝ) + 1)) * ∑ j, gK x ε (q N j) - ∫ y, 1 / (x - y) ∂μ| <
        Real.pi * η :=
    hres.eventually (gt_mem_nhds (by have := Real.pi_pos; positivity))
  filter_upwards [hev1, hev2] with N hN1 hN2 j hj
  have hcN : 0 < κ / ((N : ℝ) + 1) := by positivity
  have hsurj : Function.Surjective
      (extForce L (κ / ((N : ℝ) + 1)) (x - 2 * ε) (x + 2 * ε) (q N)) :=
    ExternalConfinement.H_surjective hL (extForce_continuous hab _)
      (extForce_slope hcN.le hab _)
  set p : ℝ := Function.surjInv hsurj (2 * Real.pi * ν N j) with hpdef
  have hp : extForce L (κ / ((N : ℝ) + 1)) (x - 2 * ε) (x + 2 * ε) (q N) p = 2 * Real.pi * ν N j :=
    Function.surjInv_eq hsurj _
  have hjc : j ∈ cluster (x - 2 * ε) (x + 2 * ε) (q N) :=
    Finset.mem_filter.mpr ⟨mem_univ _, by
      constructor <;> linarith [(abs_le.mp hj).1, (abs_le.mp hj).2]⟩
  have hcb := cluster_bound hL hcN hab (hB N).sorted (hB N).labels (hB N).eqn hjc hp
  have hcb' : |q N j - p| ≤ ε₀ := by
    refine hcb.trans ?_
    refine le_trans (le_of_eq ?_) hN1.le
    congr 2
    field_simp
  have hpx : |p - x| ≤ 2 * ε₀ := by
    calc |p - x| = |(p - q N j) + (q N j - x)| := by ring_nf
      _ ≤ |p - q N j| + |q N j - x| := abs_add_le _ _
      _ ≤ ε₀ + ε₀ := by rw [abs_sub_comm]; exact add_le_add hcb' hj
      _ = 2 * ε₀ := by ring
  have hpε : |p - x| ≤ ε := by linarith
  have hmem : p ∈ Set.Icc (x - 2 * ε) (x + 2 * ε) :=
    ⟨by linarith [(abs_le.mp hpε).1], by linarith [(abs_le.mp hpε).2]⟩
  have hap := force_approx (n := N + 1) (L := L) hcN.le hε (q N) hpε
  rw [extForce_of_mem hmem] at hp
  rw [hp] at hap
  have e1 : 2 * (κ / ((N : ℝ) + 1)) * ∑ i, gK x ε (q N i) =
      2 * κ * ((1 / ((N : ℝ) + 1)) * ∑ i, gK x ε (q N i)) := by field_simp
  have e2 : 2 * ((((N + 1 : ℕ) : ℝ)) * (κ / ((N : ℝ) + 1) / ε) ^ 3 +
      κ / ((N : ℝ) + 1) * (((N + 1 : ℕ) : ℝ) * (|x - p| / ε ^ 2)) +
      κ / ((N : ℝ) + 1) * ((cluster (x - 2 * ε) (x + 2 * ε) (q N)).card * (1 / ε))) =
      2 * (κ ^ 3 / ε ^ 3 * (1 / ((N : ℝ) + 1)) ^ 2 + κ * (|x - p| / ε ^ 2) + κ / ε *
        (((cluster (x - 2 * ε) (x + 2 * ε) (q N)).card : ℝ) / ((N : ℝ) + 1))) := by
    push_cast
    field_simp
  rw [e1, e2] at hap
  -- assemble: `|2πν_j − 2θ(x)| ≤ 2πη`
  set A := (1 / ((N : ℝ) + 1)) * ∑ i, gK x ε (q N i) with hAdef
  set I := ∫ y, 1 / (x - y) ∂μ with hI
  have hθ : 2 * theta L κ μ x = L * x - 2 * κ * I := by unfold theta; ring
  have h3 : |2 * Real.pi * ν N j - 2 * theta L κ μ x| ≤ 2 * Real.pi * η := by
    have hdiff : 2 * Real.pi * ν N j - 2 * theta L κ μ x =
        (2 * Real.pi * ν N j - (L * p - 2 * κ * A)) + (L * (p - x) - 2 * κ * (A - I)) := by
      rw [hθ]; ring
    rw [hdiff]
    have hxp : |x - p| = |p - x| := abs_sub_comm _ _
    have t1 : |L * (p - x)| ≤ L * (2 * ε₀) := by
      rw [abs_mul, abs_of_pos hL]; exact mul_le_mul_of_nonneg_left hpx hL.le
    have t2 : |2 * κ * (A - I)| = 2 * κ * |A - I| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * κ)]
    have t3 : κ * (|x - p| / ε ^ 2) ≤ κ * (2 * ε₀ / ε ^ 2) := by
      rw [hxp]; gcongr
    have habs : |L * (p - x) - 2 * κ * (A - I)| ≤ |L * (p - x)| + |2 * κ * (A - I)| := by
      have := abs_sub (L * (p - x)) (2 * κ * (A - I)); linarith
    have hsum := abs_add_le (2 * Real.pi * ν N j - (L * p - 2 * κ * A))
      (L * (p - x) - 2 * κ * (A - I))
    have hC2 : 2 * (κ * (2 * ε₀ / ε ^ 2)) + L * (2 * ε₀) = (4 * κ / ε ^ 2 + 2 * L) * ε₀ := by
      field_simp; ring
    have hsq : 2 * (κ ^ 3 / ε ^ 3 * (1 / ((N : ℝ) + 1)) ^ 2 + κ * (|x - p| / ε ^ 2) + κ / ε *
        (((cluster (x - 2 * ε) (x + 2 * ε) (q N)).card : ℝ) / ((N : ℝ) + 1))) ≤
        2 * (κ ^ 3 / ε ^ 3 * (1 / ((N : ℝ) + 1)) ^ 2 + κ * (2 * ε₀ / ε ^ 2) + κ / ε *
        (((cluster (x - 2 * ε) (x + 2 * ε) (q N)).card : ℝ) / ((N : ℝ) + 1))) := by
      linarith
    nlinarith [abs_nonneg (A - I), hap, hN2, hε₀2, hsum, habs, t1, t2, hC2, hsq]
  have h4 : |ν N j - theta L κ μ x / Real.pi| ≤ η := by
    have hpi := Real.pi_pos
    have e : 2 * Real.pi * ν N j - 2 * theta L κ μ x = 2 * Real.pi * (ν N j - theta L κ μ x / Real.pi) := by
      field_simp
    rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h3
    nlinarith
  exact h4

end QuantumNLS.LocalHeightUniform

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.LocalHeightUniform.local_height_uniform
