/-
QuantumNLS.Fidelity — R-828C5F7E `lem:fidelity` and R-849FDB99 `lem:uniform-upgrade`
(owner: opus_tensor).  The second (projective_reconstruction.tex:134–181) is at the end of the file and
follows the source proof step by step: (eq:finite-fidelity) via `one_sub_re_inner_le`, then
`lem:fidelity`.  The source's real `inf`/`sup` hypotheses are used literally; the families are
bounded (proved inside), so the real suprema are the true suprema.

Source (pinned report 3b1f701a): chapters/core/projective_reconstruction.tex:107–132,
packet statement_sha256 18aa9bd92ce249b2d90ca3afacd7c8fa22fcf908f1c0e66ed37b94efcc7b8f7c:
  "If A ≥ 0 is trace class, Tr A = 1, and ‖z‖ = 1, then ‖A − |z⟩⟨z|‖₁ ≤ 2√(1 − ⟨z, Az⟩)."

Imports the frozen `QuantumNLS.TraceClass` (checkpoint TC6, sha256 e6a8fdd7…aef33) read-only.
Any trace API extension needed here is proved in this file.

Source proof → Lean map (deviations are logged; no premise is added):
(S1) "For unit v, z, |v⟩⟨v| − |z⟩⟨z| … trace norm is 2√(1 − |⟨v,z⟩|²)."
     Lean: `traceNorm_rankOne_sub_le` (scaled form, any `w`) and `traceNorm_unit_sub_le`.
     DEVIATION: only the needed `≤` is proved, and the proof does not use eigenvalues.  It uses
     the identity `|w⟩⟨w| − |y⟩⟨y| = ½(|w+y⟩⟨w−y| + |w−y⟩⟨w+y|)` with `y = ‖w‖ ω z` and the
     phase `ω` chosen so that `⟨w, y⟩ ≥ 0`, then the rank-one bound `‖|a⟩⟨b|‖₁ ≤ ‖a‖‖b‖` and
     `‖w+y‖‖w−y‖ = 2‖w‖√(‖w‖² − |⟨z,w⟩|²)`.
(S2) "By the spectral theorem write A = Σ λⱼ |vⱼ⟩⟨vⱼ| … λⱼ ≥ 0, Σ λⱼ = 1, vⱼ unit."
     DEVIATION: the pinned mathlib has no spectral theorem for compact operators in infinite
     dimension.  We use the decomposition `A = Σᵢ |wᵢ⟩⟨wᵢ|` with `wᵢ = √A bᵢ` over a Hilbert
     basis `b`, i.e. `λᵢ = ‖wᵢ‖²`, `vᵢ = wᵢ/‖wᵢ‖`.  The source argument uses only `λᵢ ≥ 0`,
     `Σ λᵢ = Tr A = 1`, unit `vᵢ`, convergence, and `Σ λᵢ |⟨vᵢ,z⟩|² = ⟨z,Az⟩`.  All of these hold
     for this decomposition (`hasSum_norm_sq_frame`, `hasSum_norm_inner_frame`,
     `hasSum_frame_apply`).  Orthogonality of the `vⱼ` is never used.
(S3) "The series converges in trace norm. The triangle inequality …"  DEVIATION in the limit
     step: finite partial sums are bounded by the triangle inequality (`traceNorm_sum_le`); the
     limit is taken through the duality bound (`traceNorm_le_of_forall`) applied to
     strongly convergent partial sums, i.e. lower semicontinuity, instead of trace-norm
     convergence of the series.
(S4) "… and Cauchy–Schwarz yield … ≤ 2√(Σ λⱼ (1 − |⟨vⱼ,z⟩|²)) = 2√(1 − ⟨z,Az⟩)."  Kept: finite
     Cauchy–Schwarz `Finset.sum_mul_sq_le_sq_mul_sq`, with `Σ λᵢ ≤ 1` and
     `Σ λᵢ(1 − |⟨vᵢ,z⟩|²) ≤ 1 − ⟨z,Az⟩`.
-/
import QuantumNLS.TraceClass
import Mathlib.Algebra.Order.Chebyshev

open scoped InnerProductSpace ENNReal
open QuantumNLS.TraceClass

noncomputable section

namespace QuantumNLS.Fidelity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## Trace-norm API extensions (proved here; TraceClass is frozen) -/

theorem traceNorm_zero : traceNorm (0 : E →L[ℂ] E) = 0 :=
  (traceNorm_eq_zero_iff 0).mpr rfl

/-- Finite triangle inequality. -/
theorem traceNorm_sum_le {ι : Type*} (s : Finset ι) (T : ι → E →L[ℂ] E) :
    traceNorm (∑ i ∈ s, T i) ≤ ∑ i ∈ s, traceNorm (T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [traceNorm_zero]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (traceNorm_add_le _ _).trans (add_le_add le_rfl ih)

/-- Rank-one bound `‖|a⟩⟨c|‖₁ ≤ ‖a‖ ‖c‖`. -/
theorem traceNorm_rankOne_le (a c : E) :
    traceNorm (InnerProductSpace.rankOne ℂ a c) ≤ ENNReal.ofReal (‖a‖ * ‖c‖) := by
  refine traceNorm_le_of_forall (refBasis E) _ fun X hX s => ?_
  set b := refBasis E
  have e : ∑ i ∈ s, ⟪X (b i), InnerProductSpace.rankOne ℂ a c (b i)⟫_ℂ =
      ⟪X (∑ i ∈ s, ⟪b i, c⟫_ℂ • b i), a⟫_ℂ := by
    rw [map_sum, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [InnerProductSpace.rankOne_apply, inner_smul_right, map_smul, inner_smul_left,
      inner_conj_symm, mul_comm]
  rw [e]
  refine (RCLike.re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
  have h1 : ‖X (∑ i ∈ s, ⟪b i, c⟫_ℂ • b i)‖ ≤ ‖c‖ :=
    (X.le_opNorm _).trans ((mul_le_mul hX (norm_sum_inner_smul_le b s c) (norm_nonneg _)
      zero_le_one).trans (by rw [one_mul]))
  nlinarith [norm_nonneg a, norm_nonneg (X (∑ i ∈ s, ⟪b i, c⟫_ℂ • b i))]

/-! ## (S1) The rank-two estimate -/

omit [CompleteSpace E] in
/-- `|w⟩⟨w| − |y⟩⟨y| = ½(|w+y⟩⟨w−y| + |w−y⟩⟨w+y|)`. -/
theorem rankOne_sub_rankOne (w y : E) :
    InnerProductSpace.rankOne ℂ w w - InnerProductSpace.rankOne ℂ y y =
      (2 : ℂ)⁻¹ • (InnerProductSpace.rankOne ℂ (w + y) (w - y) +
        InnerProductSpace.rankOne ℂ (w - y) (w + y)) := by
  ext x
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, InnerProductSpace.rankOne_apply, inner_add_left,
    inner_sub_left, add_smul, sub_smul, smul_add, smul_sub]
  module

/-- **(S1), scaled.** For `‖z‖ = 1` and any `w`,
`‖|w⟩⟨w| − ‖w‖²|z⟩⟨z|‖₁ ≤ 2‖w‖√(‖w‖² − |⟨z,w⟩|²)`. -/
theorem traceNorm_rankOne_sub_le (w z : E) (hz : ‖z‖ = 1) :
    traceNorm (InnerProductSpace.rankOne ℂ w w -
        ((‖w‖ ^ 2 : ℝ) : ℂ) • InnerProductSpace.rankOne ℂ z z) ≤
      ENNReal.ofReal (2 * ‖w‖ * √(‖w‖ ^ 2 - ‖⟪z, w⟫_ℂ‖ ^ 2)) := by
  set c := ⟪z, w⟫_ℂ with hc
  obtain ⟨ω, hω1, hωc⟩ : ∃ ω : ℂ, ‖ω‖ = 1 ∧ ω * (starRingEnd ℂ) c = (‖c‖ : ℂ) := by
    by_cases h0 : c = 0
    · exact ⟨1, by simp, by simp [h0]⟩
    · have hn : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr h0).ne'
      refine ⟨c / (‖c‖ : ℂ), ?_, ?_⟩
      · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
          div_self (norm_pos_iff.mpr h0).ne']
      · rw [div_mul_eq_mul_div, RCLike.mul_conj]
        field_simp
        rfl
  set r : ℂ := (‖w‖ : ℂ) * ω with hr
  set y : E := r • z with hy
  have hrn : ‖r‖ = ‖w‖ := by rw [hr, norm_mul, hω1, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_norm]
  have hyn : ‖y‖ = ‖w‖ := by rw [hy, norm_smul, hrn, hz, mul_one]
  have hyy : InnerProductSpace.rankOne ℂ y y = ((‖w‖ ^ 2 : ℝ) : ℂ) • InnerProductSpace.rankOne ℂ z z := by
    have hr2 : (starRingEnd ℂ) r * r = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.conj_mul, hrn]; push_cast; rfl
    ext x
    rw [ContinuousLinearMap.smul_apply, InnerProductSpace.rankOne_apply,
      InnerProductSpace.rankOne_apply, hy, inner_smul_left, smul_smul, smul_smul]
    congr 1
    linear_combination ⟪z, x⟫_ℂ * hr2
  have hwy : RCLike.re ⟪w, y⟫_ℂ = ‖w‖ * ‖c‖ := by
    rw [hy, inner_smul_right, ← inner_conj_symm w z, ← hc, hr, mul_assoc, hωc]
    simp
  have hcw : ‖c‖ ≤ ‖w‖ := by
    have := norm_inner_le_norm (𝕜 := ℂ) z w
    rwa [hz, one_mul] at this
  have hp : ‖w + y‖ * ‖w - y‖ = 2 * ‖w‖ * √(‖w‖ ^ 2 - ‖c‖ ^ 2) := by
    have h1 : ‖w + y‖ ^ 2 = 2 * ‖w‖ ^ 2 + 2 * (‖w‖ * ‖c‖) := by
      rw [norm_add_sq (𝕜 := ℂ), hwy, hyn]; ring
    have h2 : ‖w - y‖ ^ 2 = 2 * ‖w‖ ^ 2 - 2 * (‖w‖ * ‖c‖) := by
      rw [norm_sub_sq (𝕜 := ℂ), hwy, hyn]; ring
    have hnn : 0 ≤ ‖w‖ ^ 2 - ‖c‖ ^ 2 := by nlinarith [norm_nonneg c]
    rw [← sq_eq_sq₀ (by positivity) (by positivity), mul_pow, h1, h2, mul_pow, mul_pow,
      Real.sq_sqrt hnn]
    ring
  rw [← hyy, rankOne_sub_rankOne, traceNorm_smul]
  calc ENNReal.ofReal ‖(2 : ℂ)⁻¹‖ * traceNorm (InnerProductSpace.rankOne ℂ (w + y) (w - y) +
        InnerProductSpace.rankOne ℂ (w - y) (w + y))
      ≤ ENNReal.ofReal ‖(2 : ℂ)⁻¹‖ * (ENNReal.ofReal (‖w + y‖ * ‖w - y‖) +
          ENNReal.ofReal (‖w + y‖ * ‖w - y‖)) := by
        gcongr
        refine (traceNorm_add_le _ _).trans (add_le_add (traceNorm_rankOne_le _ _) ?_)
        rw [mul_comm ‖w + y‖]
        exact traceNorm_rankOne_le _ _
    _ = ENNReal.ofReal (‖w + y‖ * ‖w - y‖) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (norm_nonneg _)]
        congr 1
        rw [norm_inv, Complex.norm_ofNat]
        ring
    _ = ENNReal.ofReal (2 * ‖w‖ * √(‖w‖ ^ 2 - ‖c‖ ^ 2)) := by rw [hp]

/-- **(S1)** for unit vectors: `‖|v⟩⟨v| − |z⟩⟨z|‖₁ ≤ 2√(1 − |⟨v,z⟩|²)`. -/
theorem traceNorm_unit_sub_le (v z : E) (hv : ‖v‖ = 1) (hz : ‖z‖ = 1) :
    traceNorm (InnerProductSpace.rankOne ℂ v v - InnerProductSpace.rankOne ℂ z z) ≤
      ENNReal.ofReal (2 * √(1 - ‖⟪v, z⟫_ℂ‖ ^ 2)) := by
  have h := traceNorm_rankOne_sub_le v z hz
  rw [hv, norm_inner_symm] at h
  simpa using h

/-! ## (S2) The decomposition `A = Σᵢ |√A bᵢ⟩⟨√A bᵢ|` -/

omit [CompleteSpace E] in
/-- A nonnegative real family whose `ofReal`-sum is `ofReal c` has real sum `c`. -/
theorem hasSum_of_tsum_ofReal {ι : Type*} {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) {c : ℝ} (hc : 0 ≤ c)
    (h : ∑' i, ENNReal.ofReal (f i) = ENNReal.ofReal c) : HasSum f c := by
  have hs : Summable f := by
    refine summable_of_sum_le (c := c) (fun i => hf i) fun u => ?_
    have h1 : ENNReal.ofReal (∑ i ∈ u, f i) ≤ ENNReal.ofReal c := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hf i), ← h]
      exact ENNReal.sum_le_tsum u
    exact (ENNReal.ofReal_le_ofReal_iff hc).mp h1
  have h2 : ENNReal.ofReal (∑' i, f i) = ENNReal.ofReal c := by
    rw [ENNReal.ofReal_tsum_of_nonneg hf hs, h]
  rw [ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg hf) hc] at h2
  exact h2 ▸ hs.hasSum

section Frame

variable {ι : Type*} (b : HilbertBasis ι ℂ E) {A : E →L[ℂ] E} (hA : A.IsPositive)

theorem sqrt_isSelfAdjoint : IsSelfAdjoint (CFC.sqrt A) := (CFC.sqrt_nonneg A).isSelfAdjoint

include hA in
theorem sqrt_mul_sqrt : CFC.sqrt A * CFC.sqrt A = A :=
  CFC.sqrt_mul_sqrt_self A (ContinuousLinearMap.nonneg_iff_isPositive.mpr hA)

include hA in
theorem inner_sqrt_left (x y : E) : ⟪CFC.sqrt A x, y⟫_ℂ = ⟪x, CFC.sqrt A y⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, (sqrt_isSelfAdjoint (A := A)).adjoint_eq]

include hA in
/-- `Σᵢ λᵢ = Tr A` with `λᵢ = ‖√A bᵢ‖²`. -/
theorem hasSum_norm_sq_frame (hTr : posTrace A = 1) :
    HasSum (fun i => ‖CFC.sqrt A (b i)‖ ^ 2) 1 := by
  refine hasSum_of_tsum_ofReal (fun i => by positivity) zero_le_one ?_
  have : hsSq b (CFC.sqrt A) = 1 := by
    rw [← traceIn_eq_hsSq_sqrt b hA, ← posTrace_eq b hA, hTr]
  rw [ENNReal.ofReal_one, ← this]
  rfl

include hA in
/-- `Σᵢ λᵢ |⟨vᵢ, z⟩|² = Σᵢ |⟨z, √A bᵢ⟩|² = ⟨z, A z⟩`. -/
theorem hasSum_norm_inner_frame (z : E) :
    HasSum (fun i => ‖⟪z, CFC.sqrt A (b i)⟫_ℂ‖ ^ 2) (RCLike.re ⟪z, A z⟫_ℂ) := by
  have h := hasSum_norm_inner_sq b (CFC.sqrt A z)
  have e1 : ∀ i, ‖⟪z, CFC.sqrt A (b i)⟫_ℂ‖ = ‖⟪b i, CFC.sqrt A z⟫_ℂ‖ := by
    intro i; rw [← inner_sqrt_left hA, norm_inner_symm]
  have e2 : ‖CFC.sqrt A z‖ ^ 2 = RCLike.re ⟪z, A z⟫_ℂ := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_sqrt_left hA, ← ContinuousLinearMap.mul_apply,
      sqrt_mul_sqrt hA]
  simp_rw [e1]
  rw [← e2]
  exact h

include hA in
/-- `A x = Σᵢ ⟨√A bᵢ, x⟩ √A bᵢ`. -/
theorem hasSum_frame_apply (x : E) :
    HasSum (fun i => ⟪CFC.sqrt A (b i), x⟫_ℂ • CFC.sqrt A (b i)) (A x) := by
  have h := (b.hasSum_repr (CFC.sqrt A x)).mapL (CFC.sqrt A)
  rw [← ContinuousLinearMap.mul_apply, sqrt_mul_sqrt hA] at h
  convert h using 1
  ext i
  rw [map_smul, b.repr_apply_apply, inner_sqrt_left hA]

end Frame

/-! ## (S3)+(S4) Main theorem -/

/-- **R-828C5F7E `lem:fidelity`.** If `A ≥ 0` is trace class, `Tr A = 1`, and `‖z‖ = 1`, then
`‖A − |z⟩⟨z|‖₁ ≤ 2√(1 − ⟨z, A z⟩)`.  (`⟨z, Az⟩` is real for `A ≥ 0`; its real part is used.) -/
theorem fidelity (A : E →L[ℂ] E) (hA : A.IsPositive) (_hAtc : IsTraceClass A)
    (hTr : posTrace A = 1) (z : E) (hz : ‖z‖ = 1) :
    traceNorm (A - InnerProductSpace.rankOne ℂ z z) ≤
      ENNReal.ofReal (2 * √(1 - RCLike.re ⟪z, A z⟫_ℂ)) := by
  set b := refBasis E
  set S := CFC.sqrt A with hS
  set a := RCLike.re ⟪z, A z⟫_ℂ with ha
  set w : RefIndex E → E := fun i => S (b i) with hw
  have hF1 := hasSum_norm_sq_frame b hA hTr
  have hF2 := hasSum_norm_inner_frame b hA z
  have hF3 := hasSum_frame_apply b hA
  -- partial sums `D_s = Σ_{i∈s} (|wᵢ⟩⟨wᵢ| − ‖wᵢ‖² |z⟩⟨z|)`
  set D : Finset (RefIndex E) → E →L[ℂ] E := fun s => ∑ i ∈ s,
    (InnerProductSpace.rankOne ℂ (w i) (w i) -
      ((‖w i‖ ^ 2 : ℝ) : ℂ) • InnerProductSpace.rankOne ℂ z z) with hD
  have hg0 : ∀ i, 0 ≤ ‖w i‖ ^ 2 - ‖⟪z, w i⟫_ℂ‖ ^ 2 := by
    intro i
    have := norm_inner_le_norm (𝕜 := ℂ) z (w i)
    rw [hz, one_mul] at this
    nlinarith [norm_nonneg ⟪z, w i⟫_ℂ]
  -- (S4) uniform bound on the partial sums
  have hbound : ∀ s, traceNorm (D s) ≤ ENNReal.ofReal (2 * √(1 - a)) := by
    intro s
    refine (traceNorm_sum_le s _).trans ?_
    refine (Finset.sum_le_sum fun i _ => traceNorm_rankOne_sub_le (w i) z hz).trans ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hs1 : ∑ i ∈ s, ‖w i‖ ^ 2 ≤ 1 := sum_le_hasSum s (fun i _ => by positivity) hF1
    have hs2 : ∑ i ∈ s, (‖w i‖ ^ 2 - ‖⟪z, w i⟫_ℂ‖ ^ 2) ≤ 1 - a :=
      sum_le_hasSum s (fun i _ => hg0 i) (hF1.sub hF2)
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖w i‖)
      (fun i => √(‖w i‖ ^ 2 - ‖⟪z, w i⟫_ℂ‖ ^ 2))
    simp_rw [Real.sq_sqrt (hg0 _)] at hcs
    have hnn : 0 ≤ ∑ i ∈ s, ‖w i‖ * √(‖w i‖ ^ 2 - ‖⟪z, w i⟫_ℂ‖ ^ 2) :=
      Finset.sum_nonneg fun i _ => by positivity
    have hsq : (∑ i ∈ s, ‖w i‖ * √(‖w i‖ ^ 2 - ‖⟪z, w i⟫_ℂ‖ ^ 2)) ^ 2 ≤ 1 - a :=
      hcs.trans ((mul_le_mul hs1 hs2 (Finset.sum_nonneg fun i _ => hg0 i) zero_le_one).trans
        (by rw [one_mul]))
    have hle : ∑ i ∈ s, ‖w i‖ * √(‖w i‖ ^ 2 - ‖⟪z, w i⟫_ℂ‖ ^ 2) ≤ √(1 - a) := by
      rw [← Real.sqrt_sq hnn]
      exact Real.sqrt_le_sqrt hsq
    calc ∑ i ∈ s, 2 * ‖w i‖ * √(‖w i‖ ^ 2 - ‖⟪z, w i⟫_ℂ‖ ^ 2)
        = 2 * ∑ i ∈ s, ‖w i‖ * √(‖w i‖ ^ 2 - ‖⟪z, w i⟫_ℂ‖ ^ 2) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
      _ ≤ 2 * √(1 - a) := by linarith
  -- (S3) strong convergence of the partial sums
  have hconv : ∀ x, Filter.Tendsto (fun s => D s x) Filter.atTop
      (nhds ((A - InnerProductSpace.rankOne ℂ z z) x)) := by
    intro x
    have h1 : HasSum (fun i => ((‖w i‖ ^ 2 : ℝ) : ℂ) • (⟪z, x⟫_ℂ • z))
        (((1 : ℝ) : ℂ) • (⟪z, x⟫_ℂ • z)) :=
      ((RCLike.hasSum_ofReal (𝕜 := ℂ)).mpr hF1).smul_const _
    have h2 := (hF3 x).sub h1
    have e : ∀ s, D s x = ∑ i ∈ s, (⟪w i, x⟫_ℂ • w i -
        ((‖w i‖ ^ 2 : ℝ) : ℂ) • (⟪z, x⟫_ℂ • z)) := by
      intro s
      rw [hD]
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, InnerProductSpace.rankOne_apply]
    simp_rw [e]
    have e2 : (A - InnerProductSpace.rankOne ℂ z z) x =
        A x - ((1 : ℝ) : ℂ) • (⟪z, x⟫_ℂ • z) := by
      rw [ContinuousLinearMap.sub_apply, InnerProductSpace.rankOne_apply]
      simp
    rw [e2]
    exact h2
  refine traceNorm_le_of_forall b _ fun X hX t => ?_
  have hlim : Filter.Tendsto (fun s => RCLike.re (∑ k ∈ t, ⟪X (b k), D s (b k)⟫_ℂ))
      Filter.atTop (nhds (RCLike.re (∑ k ∈ t,
        ⟪X (b k), (A - InnerProductSpace.rankOne ℂ z z) (b k)⟫_ℂ))) := by
    refine (RCLike.continuous_re.tendsto _).comp ?_
    exact tendsto_finset_sum t fun k _ => tendsto_const_nhds.inner (hconv (b k))
  refine le_of_tendsto' hlim fun s => ?_
  have hfin : traceNorm (D s) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound s)
  refine (RCLike.re_le_norm _).trans ((norm_sum_inner_le_traceNorm b (D s) X hX hfin t).trans ?_)
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hbound s)

/-! ## Non-vacuity and instantiation on the source carrier `h = ℓ²(ℤ)` -/

/-- `Tr |z⟩⟨z| = ‖z‖²`. -/
theorem posTrace_rankOne_self (z : E) :
    posTrace (InnerProductSpace.rankOne ℂ z z) = ENNReal.ofReal (‖z‖ ^ 2) := by
  unfold posTrace traceIn
  rw [← tsum_ofReal_norm_inner_sq (refBasis E) z]
  congr 1; ext i; congr 1
  rw [InnerProductSpace.rankOne_apply, inner_smul_right, ← inner_conj_symm z (refBasis E i),
    RCLike.conj_mul]
  norm_cast

/-- The hypotheses of `fidelity` are jointly satisfiable (`A = |z⟩⟨z|`, `‖z‖ = 1`), and then
the bound reads `‖0‖₁ ≤ 0`. -/
theorem fidelity_hypotheses_satisfiable (z : E) (hz : ‖z‖ = 1) :
    (InnerProductSpace.rankOne ℂ z z).IsPositive ∧
      IsTraceClass (InnerProductSpace.rankOne ℂ z z) ∧
      posTrace (InnerProductSpace.rankOne ℂ z z) = 1 := by
  have hpos : (InnerProductSpace.rankOne ℂ z z).IsPositive :=
    InnerProductSpace.isPositive_rankOne_self z
  have htr : posTrace (InnerProductSpace.rankOne ℂ z z) = 1 := by
    rw [posTrace_rankOne_self, hz]; simp
  refine ⟨hpos, ?_, htr⟩
  rw [IsTraceClass, traceNorm_of_isPositive hpos, htr]
  exact ENNReal.one_lt_top

/-- `lem:fidelity` on the source's auxiliary label space `h = ℓ²(ℤ)` (projective_reconstruction.tex,
"Put h = ℓ²(ℤ)"). -/
theorem fidelity_l2 (A : lp (fun _ : ℤ => ℂ) 2 →L[ℂ] lp (fun _ : ℤ => ℂ) 2) (hA : A.IsPositive) (hAtc : IsTraceClass A)
    (hTr : posTrace A = 1) (z : lp (fun _ : ℤ => ℂ) 2) (hz : ‖z‖ = 1) :
    traceNorm (A - InnerProductSpace.rankOne ℂ z z) ≤
      ENNReal.ofReal (2 * √(1 - RCLike.re ⟪z, A z⟫_ℂ)) :=
  fidelity A hA hAtc hTr z hz

/-! ## Deviation classification after the FD3 repair (for independent review; not a fidelity claim)

* (S3) REPAIRED in `fidelity_series`: the bound is passed to the limit through ACTUAL trace-norm
  convergence of the countable positive rank-one series (`tendsto_traceNorm_sub_frameSum`, proved
  from the positive trace tail), with the triangle inequality on the partial sums, as in the source.
  `fidelity` (FD2 route via strong convergence and lower semicontinuity) is kept unchanged for
  existing consumers.
* (S2) REMAINS a deviation: the series is the `√A`-frame series `Σᵢ |√A bᵢ⟩⟨√A bᵢ|`, not the
  spectral (eigenvector) decomposition.  The pinned mathlib has no compact spectral theorem in
  infinite dimension.  The source argument uses only `λᵢ ≥ 0`, `Σλᵢ = 1`, unit `vᵢ`, trace-norm
  convergence and `Σλᵢ|⟨vᵢ,z⟩|² = ⟨z,Az⟩`, all proved for the frame series; orthogonality of the
  `vᵢ` is not used.
* (S1) REMAINS a deviation: only the needed `≤` for the rank-two trace norm is proved (polarization
  identity plus the rank-one bound), not the source's eigenvalue computation of the equality.
* (S4) Cauchy–Schwarz on the weighted sum is kept.
-/

/-! ## (S3, source route) Trace-norm convergence of the countable positive rank-one frame series

Source (projective_reconstruction.tex:126–127): "The series converges in trace norm. The
triangle inequality and Cauchy–Schwarz yield …".  Here the series is the frame series
`A = Σᵢ |√A bᵢ⟩⟨√A bᵢ|` of (S2).  We prove ACTUAL trace-norm convergence
`‖A − Σ_{i∈s} |√A bᵢ⟩⟨√A bᵢ|‖₁ → 0` from the positive trace tail:
`A − A_s` is positive (Bessel), so `‖A − A_s‖₁ = Tr(A − A_s) = Tr A − Σ_{i∈s} λᵢ = 1 − Σ_{i∈s} λᵢ`
(additivity of the trace on the positive cone), and `Σᵢ λᵢ = 1`.
`fidelity_series` then follows the source's limit route: triangle inequality with the partial sum,
the per-term rank-two bound with Cauchy–Schwarz on the finite partial sum, and passage to the
limit IN TRACE NORM.  No strong convergence or lower semicontinuity is used in this proof. -/

section FrameSeries

variable {ι : Type*} (b : HilbertBasis ι ℂ E)

/-- Partial frame sum `A_s = Σ_{i∈s} |√A bᵢ⟩⟨√A bᵢ|`. -/
def frameSum (A : E →L[ℂ] E) (s : Finset ι) : E →L[ℂ] E :=
  ∑ i ∈ s, InnerProductSpace.rankOne ℂ (CFC.sqrt A (b i)) (CFC.sqrt A (b i))

theorem isPositive_frameSum (A : E →L[ℂ] E) (s : Finset ι) : (frameSum b A s).IsPositive :=
  ContinuousLinearMap.isPositive_sum s fun _ _ => InnerProductSpace.isPositive_rankOne_self _

variable {A : E →L[ℂ] E} (hA : A.IsPositive)

include hA in
/-- Bessel: `⟨x, A_s x⟩ ≤ ⟨x, A x⟩`. -/
theorem re_inner_frameSum_le (s : Finset ι) (x : E) :
    RCLike.re ⟪frameSum b A s x, x⟫_ℂ ≤ RCLike.re ⟪A x, x⟫_ℂ := by
  have h1 : RCLike.re ⟪frameSum b A s x, x⟫_ℂ = ∑ i ∈ s, ‖⟪b i, CFC.sqrt A x⟫_ℂ‖ ^ 2 := by
    rw [frameSum, ContinuousLinearMap.sum_apply, sum_inner, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [InnerProductSpace.rankOne_apply, inner_smul_left, inner_sqrt_left hA, RCLike.conj_mul,
      ← RCLike.ofReal_pow, RCLike.ofReal_re]
  have hAx : A x = CFC.sqrt A (CFC.sqrt A x) := by
    rw [← ContinuousLinearMap.mul_apply, sqrt_mul_sqrt hA]
  have h2 : RCLike.re ⟪A x, x⟫_ℂ = ‖CFC.sqrt A x‖ ^ 2 := by
    rw [hAx, inner_sqrt_left hA, inner_self_eq_norm_sq]
  rw [h1, h2]
  exact Orthonormal.sum_inner_products_le (CFC.sqrt A x) b.orthonormal

include hA in
/-- The tail `A − A_s = Σ_{i∉s} |√A bᵢ⟩⟨√A bᵢ|` is a positive operator. -/
theorem isPositive_sub_frameSum (s : Finset ι) : (A - frameSum b A s).IsPositive := by
  rw [ContinuousLinearMap.isPositive_def]
  refine ⟨hA.isSymmetric.sub (isPositive_frameSum b A s).isSymmetric, fun x => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, ContinuousLinearMap.sub_apply, inner_sub_left,
    map_sub]
  linarith [re_inner_frameSum_le b hA s x]

theorem posTrace_zero : posTrace (0 : E →L[ℂ] E) = 0 := by
  simp [posTrace, traceIn]

/-- `Tr A_s = Σ_{i∈s} ‖√A bᵢ‖²`. -/
theorem posTrace_frameSum (s : Finset ι) :
    posTrace (frameSum b A s) = ENNReal.ofReal (∑ i ∈ s, ‖CFC.sqrt A (b i)‖ ^ 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [frameSum, posTrace_zero]
  | insert j s hj ih =>
    have e : frameSum b A (insert j s) =
        InnerProductSpace.rankOne ℂ (CFC.sqrt A (b j)) (CFC.sqrt A (b j)) + frameSum b A s := by
      rw [frameSum, Finset.sum_insert hj]; rfl
    rw [e, posTrace_add (InnerProductSpace.isPositive_rankOne_self _) (isPositive_frameSum b A s),
      posTrace_rankOne_self, ih, Finset.sum_insert hj,
      ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun i _ => by positivity)]

include hA in
/-- **Positive trace tail.** `‖A − A_s‖₁ = 1 − Σ_{i∈s} λᵢ` when `Tr A = 1`. -/
theorem traceNorm_sub_frameSum (hTr : posTrace A = 1) (s : Finset ι) :
    traceNorm (A - frameSum b A s) =
      ENNReal.ofReal (1 - ∑ i ∈ s, ‖CFC.sqrt A (b i)‖ ^ 2) := by
  have hpos := isPositive_sub_frameSum b hA s
  have hadd := posTrace_add (isPositive_frameSum b A s) hpos
  rw [add_sub_cancel, hTr, posTrace_frameSum] at hadd
  have hX : posTrace (A - frameSum b A s) =
      1 - ENNReal.ofReal (∑ i ∈ s, ‖CFC.sqrt A (b i)‖ ^ 2) :=
    ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top (by rw [add_comm]; exact hadd.symm)
  rw [traceNorm_of_isPositive hpos, hX,
    ENNReal.ofReal_sub 1 (Finset.sum_nonneg fun i _ => by positivity), ENNReal.ofReal_one]

include hA in
/-- **Trace-norm convergence of the frame series**: `‖A − A_s‖₁ → 0`. -/
theorem tendsto_traceNorm_sub_frameSum (hTr : posTrace A = 1) :
    Filter.Tendsto (fun s : Finset ι => traceNorm (A - frameSum b A s)) Filter.atTop
      (nhds 0) := by
  simp_rw [traceNorm_sub_frameSum b hA hTr]
  have h : Filter.Tendsto (fun s : Finset ι => ∑ i ∈ s, ‖CFC.sqrt A (b i)‖ ^ 2) Filter.atTop
      (nhds 1) := hasSum_norm_sq_frame b hA hTr
  have h2 := ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := (1 : ℝ))).sub h)
  rwa [sub_self, ENNReal.ofReal_zero] at h2

end FrameSeries

/-- **R-828C5F7E via the source's series route (S3 repaired).**  Same statement as `fidelity`;
the limit is taken in TRACE NORM using `tendsto_traceNorm_sub_frameSum`. -/
theorem fidelity_series (A : E →L[ℂ] E) (hA : A.IsPositive) (_hAtc : IsTraceClass A)
    (hTr : posTrace A = 1) (z : E) (hz : ‖z‖ = 1) :
    traceNorm (A - InnerProductSpace.rankOne ℂ z z) ≤
      ENNReal.ofReal (2 * √(1 - RCLike.re ⟪z, A z⟫_ℂ)) := by
  set b := refBasis E
  set a := RCLike.re ⟪z, A z⟫_ℂ with ha
  set w : RefIndex E → E := fun i => CFC.sqrt A (b i) with hw
  set P := InnerProductSpace.rankOne ℂ z z with hP
  have hF1 := hasSum_norm_sq_frame b hA hTr
  have hF2 := hasSum_norm_inner_frame b hA z
  set lam : Finset (RefIndex E) → ℝ := fun s => ∑ i ∈ s, ‖w i‖ ^ 2 with hlam
  have hlam1 : ∀ s, lam s ≤ 1 := fun s => sum_le_hasSum s (fun i _ => by positivity) hF1
  have hg0 : ∀ i, 0 ≤ ‖w i‖ ^ 2 - ‖⟪z, w i⟫_ℂ‖ ^ 2 := by
    intro i
    have := norm_inner_le_norm (𝕜 := ℂ) z (w i)
    rw [hz, one_mul] at this
    nlinarith [norm_nonneg ⟪z, w i⟫_ℂ]
  -- per-term rank-two bound + triangle + Cauchy–Schwarz on finite partial sums
  set D : Finset (RefIndex E) → E →L[ℂ] E := fun s => ∑ i ∈ s,
    (InnerProductSpace.rankOne ℂ (w i) (w i) - ((‖w i‖ ^ 2 : ℝ) : ℂ) • P) with hD
  have hbound : ∀ s, traceNorm (D s) ≤ ENNReal.ofReal (2 * √(1 - a)) := by
    intro s
    refine (traceNorm_sum_le s _).trans ?_
    refine (Finset.sum_le_sum fun i _ => traceNorm_rankOne_sub_le (w i) z hz).trans ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hs2 : ∑ i ∈ s, (‖w i‖ ^ 2 - ‖⟪z, w i⟫_ℂ‖ ^ 2) ≤ 1 - a :=
      sum_le_hasSum s (fun i _ => hg0 i) (hF1.sub hF2)
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖w i‖)
      (fun i => √(‖w i‖ ^ 2 - ‖⟪z, w i⟫_ℂ‖ ^ 2))
    simp_rw [Real.sq_sqrt (hg0 _)] at hcs
    have hnn : 0 ≤ ∑ i ∈ s, ‖w i‖ * √(‖w i‖ ^ 2 - ‖⟪z, w i⟫_ℂ‖ ^ 2) :=
      Finset.sum_nonneg fun i _ => by positivity
    have hsq : (∑ i ∈ s, ‖w i‖ * √(‖w i‖ ^ 2 - ‖⟪z, w i⟫_ℂ‖ ^ 2)) ^ 2 ≤ 1 - a :=
      hcs.trans ((mul_le_mul (hlam1 s) hs2 (Finset.sum_nonneg fun i _ => hg0 i)
        zero_le_one).trans (by rw [one_mul]))
    have hle : ∑ i ∈ s, ‖w i‖ * √(‖w i‖ ^ 2 - ‖⟪z, w i⟫_ℂ‖ ^ 2) ≤ √(1 - a) := by
      rw [← Real.sqrt_sq hnn]
      exact Real.sqrt_le_sqrt hsq
    calc ∑ i ∈ s, 2 * ‖w i‖ * √(‖w i‖ ^ 2 - ‖⟪z, w i⟫_ℂ‖ ^ 2)
        = 2 * ∑ i ∈ s, ‖w i‖ * √(‖w i‖ ^ 2 - ‖⟪z, w i⟫_ℂ‖ ^ 2) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
      _ ≤ 2 * √(1 - a) := by linarith
  -- decomposition `A − P = (A − A_s) + D_s + (λ_s − 1) P`
  have hdecomp : ∀ s, A - P = (A - frameSum b A s) + D s + (((lam s - 1 : ℝ)) : ℂ) • P := by
    intro s
    have e1 : D s = frameSum b A s - ((lam s : ℝ) : ℂ) • P := by
      show (∑ i ∈ s, (InnerProductSpace.rankOne ℂ (w i) (w i) - ((‖w i‖ ^ 2 : ℝ) : ℂ) • P)) =
        frameSum b A s - ((lam s : ℝ) : ℂ) • P
      rw [Finset.sum_sub_distrib, ← Finset.sum_smul, frameSum, hlam]
      push_cast
      rfl
    rw [e1]
    push_cast
    rw [sub_smul, one_smul]
    abel
  have hPnorm : traceNorm P = 1 := by
    rw [hP, traceNorm_of_isPositive (InnerProductSpace.isPositive_rankOne_self z),
      posTrace_rankOne_self, hz]
    simp
  -- uniform bound for every partial sum
  have hstep : ∀ s, traceNorm (A - P) ≤
      traceNorm (A - frameSum b A s) + ENNReal.ofReal (2 * √(1 - a)) +
        traceNorm (A - frameSum b A s) := by
    intro s
    rw [hdecomp s]
    refine (traceNorm_add_le _ _).trans (add_le_add ((traceNorm_add_le _ _).trans
      (add_le_add le_rfl (hbound s))) ?_)
    rw [traceNorm_smul, hPnorm, mul_one, traceNorm_sub_frameSum b hA hTr s, Complex.norm_real,
      Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (by linarith [hlam1 s])]
  -- pass to the limit in trace norm
  have hlim := tendsto_traceNorm_sub_frameSum b hA hTr
  have hlim2 : Filter.Tendsto (fun s => traceNorm (A - frameSum b A s) +
      ENNReal.ofReal (2 * √(1 - a)) + traceNorm (A - frameSum b A s)) Filter.atTop
      (nhds (0 + ENNReal.ofReal (2 * √(1 - a)) + 0)) :=
    (hlim.add tendsto_const_nhds).add hlim
  rw [zero_add, add_zero] at hlim2
  exact ge_of_tendsto' hlim2 hstep

end QuantumNLS.Fidelity

/-! ## R-849FDB99 `lem:uniform-upgrade` (projective_reconstruction.tex:134–181)

"Let T be any parameter set. Suppose A_N(t) ≥ 0, Tr A_N(t) = 1, and z(t) ∈ ℓ²(ℤ) is a unit
vector for every t. Suppose inf_{F⋐ℤ} sup_t ‖(1−P_F) z(t)‖ = 0 … and that for every fixed a, b,
sup_t |(A_N(t))_{ab} − z_a(t) conj z_b(t)| → 0. Then sup_t ‖A_N(t) − |z(t)⟩⟨z(t)|‖₁ → 0."

Proof follows the source: the finite-block fidelity estimate `eq:finite-fidelity`
`1 − ⟨z, A z⟩ ≤ 2ρ_F + 2ρ_F² + |F| δ_{N,F}` (`one_sub_re_inner_le`), then `lem:fidelity`. -/

namespace QuantumNLS.Fidelity

/-- The source's auxiliary label space `h = ℓ²(ℤ)`. -/
abbrev L2Z : Type := lp (fun _ : ℤ => ℂ) 2

/-- Canonical basis vector `e_a`. -/
def ev (a : ℤ) : L2Z := lp.single 2 a (1 : ℂ)

/-- The canonical Hilbert basis `(e_a)` of `ℓ²(ℤ)`. -/
def stdBasis : HilbertBasis ℤ ℂ L2Z := default

theorem stdBasis_apply (a : ℤ) : stdBasis a = ev a := by
  rw [← HilbertBasis.repr_symm_single]
  rfl

theorem inner_ev_left (a : ℤ) (f : L2Z) : ⟪ev a, f⟫_ℂ = f a := by
  classical
  rw [ev, lp.inner_single_left]
  simp

/-- Matrix entry `(A)_{ab} = ⟨e_a, A e_b⟩`. -/
def entry (A : L2Z →L[ℂ] L2Z) (a b : ℤ) : ℂ := ⟪ev a, A (ev b)⟫_ℂ

/-- Coordinate projection `P_F z = Σ_{a∈F} z_a e_a`. -/
def coordProj (F : Finset ℤ) (z : L2Z) : L2Z := ∑ a ∈ F, z a • ev a

theorem inner_ev_coordProj (F : Finset ℤ) (z : L2Z) {b : ℤ} (hb : b ∈ F) :
    ⟪ev b, coordProj F z⟫_ℂ = z b := by
  have := stdBasis.orthonormal.inner_right_sum (fun a => z a) hb
  simpa [coordProj, stdBasis_apply] using this

theorem inner_coordProj_left (F : Finset ℤ) (z y : L2Z) :
    ⟪coordProj F z, y⟫_ℂ = ∑ a ∈ F, (starRingEnd ℂ) (z a) * ⟪ev a, y⟫_ℂ := by
  rw [coordProj, sum_inner]
  simp_rw [inner_smul_left]

theorem inner_coordProj_self (F : Finset ℤ) (z : L2Z) :
    ⟪coordProj F z, coordProj F z⟫_ℂ = ⟪coordProj F z, z⟫_ℂ := by
  rw [inner_coordProj_left, inner_coordProj_left]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [inner_ev_coordProj F z ha, inner_ev_left]

theorem norm_coordProj_le (F : Finset ℤ) (z : L2Z) : ‖coordProj F z‖ ≤ ‖z‖ := by
  have h := norm_sum_inner_smul_le stdBasis F z
  simpa [coordProj, stdBasis_apply, inner_ev_left] using h

theorem norm_sub_coordProj_sq (F : Finset ℤ) (z : L2Z) :
    ‖z - coordProj F z‖ ^ 2 = ‖z‖ ^ 2 - ‖coordProj F z‖ ^ 2 := by
  have h1 : RCLike.re ⟪z, coordProj F z⟫_ℂ = ‖coordProj F z‖ ^ 2 := by
    rw [← inner_conj_symm, RCLike.conj_re, ← inner_coordProj_self, inner_self_eq_norm_sq]
  rw [norm_sub_sq (𝕜 := ℂ), h1]
  ring

/-- A positive trace-one operator is a contraction (via `‖A‖ ≤ ‖A‖₁ = Tr A`). -/
theorem norm_le_one_of_trace_one {A : L2Z →L[ℂ] L2Z} (hA : A.IsPositive)
    (hTr : posTrace A = 1) : ‖A‖ ≤ 1 := by
  have h := norm_le_traceNorm A
  rw [traceNorm_of_isPositive hA, hTr] at h
  exact ENNReal.ofReal_le_one.mp h

/-- **`eq:finite-fidelity`.** For a unit `z`, a positive trace-one `A`, a finite `F` with
`‖(1−P_F) z‖ ≤ ρ` and entry errors `≤ δ` on `F × F`:
`1 − ⟨z, A z⟩ ≤ 2ρ + 2ρ² + |F| δ`. -/
theorem one_sub_re_inner_le {A : L2Z →L[ℂ] L2Z} (hA : A.IsPositive) (hTr : posTrace A = 1)
    {z : L2Z} (hz : ‖z‖ = 1) (F : Finset ℤ) {ρ δ : ℝ} (hρ : ‖z - coordProj F z‖ ≤ ρ)
    (hδ : ∀ a ∈ F, ∀ b ∈ F, ‖entry A a b - z a * (starRingEnd ℂ) (z b)‖ ≤ δ) :
    1 - RCLike.re ⟪z, A z⟫_ℂ ≤ 2 * ρ + 2 * ρ ^ 2 + F.card * δ := by
  set x := coordProj F z with hxdef
  have hAn := norm_le_one_of_trace_one hA hTr
  have hxn : ‖x‖ ≤ 1 := hz ▸ norm_coordProj_le F z
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hρ
  have hx2 : 1 - ρ ^ 2 ≤ ‖x‖ ^ 2 := by
    have := norm_sub_coordProj_sq F z
    rw [hz] at this
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) hρ 2]
  -- (ii) replacing `z` by `x = P_F z` costs at most `2ρ`
  have hii : RCLike.re ⟪x, A x⟫_ℂ - RCLike.re ⟪z, A z⟫_ℂ ≤ 2 * ρ := by
    have e : ⟪z, A z⟫_ℂ - ⟪x, A x⟫_ℂ = ⟪z - x, A z⟫_ℂ + ⟪x, A (z - x)⟫_ℂ := by
      rw [inner_sub_left, map_sub, inner_sub_right]; ring
    have h1 : ‖⟪z - x, A z⟫_ℂ‖ ≤ ρ := by
      refine (norm_inner_le_norm _ _).trans ?_
      have : ‖A z‖ ≤ 1 := (A.le_opNorm z).trans (by rw [hz, mul_one]; exact hAn)
      nlinarith [norm_nonneg (z - x), norm_nonneg (A z)]
    have h2 : ‖⟪x, A (z - x)⟫_ℂ‖ ≤ ρ := by
      refine (norm_inner_le_norm _ _).trans ?_
      have : ‖A (z - x)‖ ≤ ‖z - x‖ :=
        (A.le_opNorm _).trans (by nlinarith [norm_nonneg (z - x)])
      nlinarith [norm_nonneg x, norm_nonneg (A (z - x)), norm_nonneg (z - x)]
    have e' : ⟪x, A x⟫_ℂ - ⟪z, A z⟫_ℂ = -(⟪z - x, A z⟫_ℂ + ⟪x, A (z - x)⟫_ℂ) := by
      rw [← e]; ring
    have h3 : RCLike.re (⟪x, A x⟫_ℂ - ⟪z, A z⟫_ℂ) ≤ ρ + ρ := by
      rw [e']
      refine (RCLike.re_le_norm _).trans ?_
      rw [norm_neg]
      exact (norm_add_le _ _).trans (add_le_add h1 h2)
    rw [map_sub] at h3
    linarith
  -- (iii) the finite block
  have hiii : -(F.card * δ) ≤ RCLike.re ⟪x, (A - InnerProductSpace.rankOne ℂ z z) x⟫_ℂ := by
    have e : ⟪x, (A - InnerProductSpace.rankOne ℂ z z) x⟫_ℂ = ∑ a ∈ F, ∑ b ∈ F,
        (starRingEnd ℂ) (z a) * z b * (entry A a b - z a * (starRingEnd ℂ) (z b)) := by
      rw [inner_coordProj_left]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hxdef, coordProj, map_sum, inner_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_smul, inner_smul_right, ContinuousLinearMap.sub_apply, inner_sub_right,
        InnerProductSpace.rankOne_apply, inner_smul_right, ← inner_conj_symm z (ev b)]
      simp only [entry, inner_ev_left]
      ring
    have hbound : ‖⟪x, (A - InnerProductSpace.rankOne ℂ z z) x⟫_ℂ‖ ≤ F.card * δ := by
      rw [e]
      have hsum : ∑ a ∈ F, ‖z a‖ ^ 2 ≤ 1 := by
        have := stdBasis.orthonormal.sum_inner_products_le (x := z) (s := F)
        simpa [stdBasis_apply, inner_ev_left, hz] using this
      have hcs : (∑ a ∈ F, ‖z a‖) ^ 2 ≤ F.card * ∑ a ∈ F, ‖z a‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq
      have hδ0 : F.Nonempty → 0 ≤ δ := fun ⟨a, ha⟩ => (norm_nonneg _).trans (hδ a ha a ha)
      calc ‖∑ a ∈ F, ∑ b ∈ F, (starRingEnd ℂ) (z a) * z b *
            (entry A a b - z a * (starRingEnd ℂ) (z b))‖
          ≤ ∑ a ∈ F, ∑ b ∈ F, ‖z a‖ * ‖z b‖ * δ := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a ha => ?_)
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b hb => ?_)
            rw [norm_mul, norm_mul, RCLike.norm_conj]
            exact mul_le_mul_of_nonneg_left (hδ a ha b hb) (by positivity)
        _ = δ * (∑ a ∈ F, ‖z a‖) ^ 2 := by
            rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun b _ => ?_
            ring
        _ ≤ F.card * δ := by
            rcases F.eq_empty_or_nonempty with hF | hF
            · simp [hF]
            · have := hδ0 hF
              have h4 : (∑ a ∈ F, ‖z a‖) ^ 2 ≤ F.card := by nlinarith [hcs, hsum]
              nlinarith
    have := RCLike.re_le_norm (-⟪x, (A - InnerProductSpace.rankOne ℂ z z) x⟫_ℂ)
    rw [map_neg, norm_neg] at this
    linarith
  -- (iv) `⟨x, |z⟩⟨z| x⟩ = ‖x‖⁴`
  have hiv : RCLike.re ⟪x, InnerProductSpace.rankOne ℂ z z x⟫_ℂ = ‖x‖ ^ 4 := by
    have hxz : ⟪x, z⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
      rw [← inner_coordProj_self, inner_self_eq_norm_sq_to_K]; push_cast; rfl
    rw [InnerProductSpace.rankOne_apply, inner_smul_right, ← inner_conj_symm z x, hxz]
    have e : (starRingEnd ℂ) ((‖x‖ ^ 2 : ℝ) : ℂ) * ((‖x‖ ^ 2 : ℝ) : ℂ) = ((‖x‖ ^ 4 : ℝ) : ℂ) := by
      rw [Complex.conj_ofReal, ← Complex.ofReal_mul]; congr 1; ring
    rw [e]
    exact Complex.ofReal_re _
  have hsplit : RCLike.re ⟪x, A x⟫_ℂ = RCLike.re ⟪x, (A - InnerProductSpace.rankOne ℂ z z) x⟫_ℂ +
      RCLike.re ⟪x, InnerProductSpace.rankOne ℂ z z x⟫_ℂ := by
    rw [ContinuousLinearMap.sub_apply, inner_sub_right, map_sub]; ring
  have hx4 : 1 - 2 * ρ ^ 2 ≤ ‖x‖ ^ 4 := by
    rcases le_total 0 (1 - ρ ^ 2) with h | h
    · nlinarith [pow_le_pow_left₀ h hx2 2]
    · nlinarith [sq_nonneg (‖x‖ ^ 2)]
  nlinarith

/-- **R-849FDB99 `lem:uniform-upgrade`.** -/
theorem uniform_upgrade {T : Type*} (A : ℕ → T → L2Z →L[ℂ] L2Z) (z : T → L2Z)
    (hA : ∀ N t, (A N t).IsPositive) (hTr : ∀ N t, posTrace (A N t) = 1)
    (hz : ∀ t, ‖z t‖ = 1)
    (htight : ⨅ F : Finset ℤ, ⨆ t, ‖z t - coordProj F (z t)‖ = 0)
    (hent : ∀ a b, Filter.Tendsto
      (fun N => ⨆ t, ‖entry (A N t) a b - z t a * (starRingEnd ℂ) (z t b)‖)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun N => ⨆ t, traceNorm (A N t - InnerProductSpace.rankOne ℂ (z t) (z t)))
      Filter.atTop (nhds 0) := by
  -- boundedness for the real suprema
  have hbddz : ∀ F : Finset ℤ, BddAbove (Set.range fun t => ‖z t - coordProj F (z t)‖) := by
    intro F
    refine ⟨1, ?_⟩
    rintro _ ⟨t, rfl⟩
    have h := norm_sub_coordProj_sq F (z t)
    rw [hz] at h
    nlinarith [norm_nonneg (z t - coordProj F (z t)), norm_nonneg (coordProj F (z t))]
  have hcoord : ∀ t a, ‖z t a‖ ≤ 1 := by
    intro t a
    rw [← inner_ev_left]
    refine (norm_inner_le_norm _ _).trans ?_
    rw [hz, ev, lp.norm_single, norm_one, one_mul]
    norm_num
  have hbdde : ∀ N a b, BddAbove (Set.range fun t =>
      ‖entry (A N t) a b - z t a * (starRingEnd ℂ) (z t b)‖) := by
    intro N a b
    refine ⟨2, ?_⟩
    rintro _ ⟨t, rfl⟩
    have hev : ∀ c, ‖ev c‖ = 1 := fun c => by rw [ev, lp.norm_single, norm_one]; norm_num
    have h1 : ‖entry (A N t) a b‖ ≤ 1 := by
      refine (norm_inner_le_norm _ _).trans ?_
      rw [hev, one_mul]
      have hA1 := norm_le_one_of_trace_one (hA N t) (hTr N t)
      exact ((A N t).le_opNorm _).trans (by rw [hev, mul_one]; exact hA1)
    have h2 : ‖z t a * (starRingEnd ℂ) (z t b)‖ ≤ 1 := by
      rw [norm_mul, RCLike.norm_conj]
      nlinarith [hcoord t a, hcoord t b, norm_nonneg (z t a), norm_nonneg (z t b)]
    linarith [norm_sub_le (entry (A N t) a b) (z t a * (starRingEnd ℂ) (z t b))]
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨r, -, hr0, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  have hr : 0 < r := ENNReal.ofReal_pos.mp hr0
  set η : ℝ := (r / 2) ^ 2 with hη
  have hηpos : 0 < η := by positivity
  set ρ : ℝ := min 1 (η / 8) with hρdef
  have hρpos : 0 < ρ := lt_min one_pos (by positivity)
  obtain ⟨F, hF⟩ : ∃ F : Finset ℤ, (⨆ t, ‖z t - coordProj F (z t)‖) < ρ :=
    exists_lt_of_ciInf_lt (by rw [htight]; exact hρpos)
  set δ : ℝ := η / (2 * (F.card + 1)) with hδdef
  have hδpos : 0 < δ := by positivity
  have hev : ∀ᶠ N in Filter.atTop, ∀ a ∈ F, ∀ b ∈ F,
      (⨆ t, ‖entry (A N t) a b - z t a * (starRingEnd ℂ) (z t b)‖) < δ := by
    rw [Filter.eventually_all_finset]
    intro a _
    rw [Filter.eventually_all_finset]
    intro b _
    exact (hent a b).eventually (gt_mem_nhds hδpos)
  filter_upwards [hev] with N hN
  refine iSup_le fun t => ?_
  have hρt : ‖z t - coordProj F (z t)‖ ≤ ρ := (le_ciSup (hbddz F) t).trans hF.le
  have hδt : ∀ a ∈ F, ∀ b ∈ F,
      ‖entry (A N t) a b - z t a * (starRingEnd ℂ) (z t b)‖ ≤ δ :=
    fun a ha b hb => (le_ciSup (hbdde N a b) t).trans (hN a ha b hb).le
  have hfin := one_sub_re_inner_le (hA N t) (hTr N t) (hz t) F hρt hδt
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρη : ρ ≤ η / 8 := min_le_right _ _
  have hcard : (F.card : ℝ) * δ ≤ η / 2 := by
    have hc : (0 : ℝ) < 2 * (F.card + 1) := by positivity
    have e : δ * (2 * ((F.card : ℝ) + 1)) = η := div_mul_cancel₀ η hc.ne'
    nlinarith
  have hsmall : 1 - RCLike.re ⟪z t, A N t (z t)⟫_ℂ ≤ η := by
    nlinarith [mul_le_mul_of_nonneg_left hρ1 hρpos.le]
  have htc : IsTraceClass (A N t) := by
    rw [IsTraceClass, traceNorm_of_isPositive (hA N t), hTr N t]; exact ENNReal.one_lt_top
  refine (fidelity (A N t) (hA N t) htc (hTr N t) (z t) (hz t)).trans
    ((ENNReal.ofReal_le_ofReal ?_).trans hrε.le)
  have : √(1 - RCLike.re ⟪z t, A N t (z t)⟫_ℂ) ≤ r / 2 := by
    calc √(1 - RCLike.re ⟪z t, A N t (z t)⟫_ℂ) ≤ √η := Real.sqrt_le_sqrt hsmall
      _ = r / 2 := by rw [hη, Real.sqrt_sq (by positivity)]
  linarith

end QuantumNLS.Fidelity

#print axioms QuantumNLS.Fidelity.traceNorm_sum_le
#print axioms QuantumNLS.Fidelity.traceNorm_rankOne_le
#print axioms QuantumNLS.Fidelity.traceNorm_rankOne_sub_le
#print axioms QuantumNLS.Fidelity.traceNorm_unit_sub_le
#print axioms QuantumNLS.Fidelity.fidelity
#print axioms QuantumNLS.Fidelity.fidelity_hypotheses_satisfiable
#print axioms QuantumNLS.Fidelity.fidelity_l2
#print axioms QuantumNLS.Fidelity.one_sub_re_inner_le
#print axioms QuantumNLS.Fidelity.uniform_upgrade
#print axioms QuantumNLS.Fidelity.tendsto_traceNorm_sub_frameSum
#print axioms QuantumNLS.Fidelity.fidelity_series
