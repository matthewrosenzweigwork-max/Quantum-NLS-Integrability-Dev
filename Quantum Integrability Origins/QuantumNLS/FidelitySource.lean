/-
QuantumNLS.FidelitySource — R-828C5F7E `lem:fidelity` assembled along the SOURCE proof route
(owner: opus_tensor).

Frozen imports, read-only:
* RankTwoTrace RT1, sha256 06f5ee98…44bc2.  S1: rank-two trace-norm EQUALITY via eigenvalues on
  span{v,z}.
* Fidelity FD3, sha256 84f2a973…394ca.  S3: trace-norm convergence of the positive rank-one
  series from the positive trace tail.  Also the frame data of S2.

Source (projective_reconstruction.tex:113–132):
  (S1) ‖|v⟩⟨v| − |z⟩⟨z|‖₁ = 2√(1 − |⟨v,z⟩|²)                 → `RankTwoTrace.traceNorm_unit_sub_eq`
  (S2) A = Σⱼ λⱼ |vⱼ⟩⟨vⱼ|, λⱼ ≥ 0, Σλⱼ = 1, vⱼ unit          → FRAME series, see below (DEVIATION)
  (S3) "The series converges in trace norm. The triangle inequality …"
                                                            → `Fidelity.tendsto_traceNorm_sub_frameSum`
  (S4) "… and Cauchy–Schwarz yield ‖A − |z⟩⟨z|‖₁ ≤ 2Σλⱼ√(1−|⟨vⱼ,z⟩|²) ≤ 2√(Σλⱼ(1−|⟨vⱼ,z⟩|²))
        = 2√(1 − ⟨z,Az⟩)"                                   → weighted Cauchy–Schwarz below

(S2) REMAINS AN EXPLICIT DEVIATION pending owner/policy disposition.  The decomposition used is
`A = Σᵢ λᵢ |vᵢ⟩⟨vᵢ|` with `λᵢ = ‖√A bᵢ‖²` and `vᵢ = √A bᵢ / ‖√A bᵢ‖` over a Hilbert basis `b`.
It is not the spectral (eigenvector) decomposition: the `vᵢ` need not be orthogonal or
eigenvectors.  The pinned mathlib has no infinite-dimensional compact spectral theorem.  Every
property the source argument uses is proved for this decomposition: `λᵢ ≥ 0`, `Σλᵢ = 1`, unit
`vᵢ`, trace-norm convergence, and `Σλᵢ|⟨vᵢ,z⟩|² = ⟨z,Az⟩`.  No orthogonality is used.
-/
import QuantumNLS.RankTwoTrace

open scoped InnerProductSpace ENNReal
open QuantumNLS.TraceClass QuantumNLS.Fidelity QuantumNLS.RankTwoTrace

noncomputable section

namespace QuantumNLS.FidelitySource

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## Normalizing the frame vectors: `wᵢ = ‖wᵢ‖ vᵢ` with `vᵢ` unit -/

open Classical in
/-- `w / ‖w‖` (and `z` when `w = 0`, where the term carries weight zero). -/
def unitOf (z w : E) : E := if w = 0 then z else ((‖w‖⁻¹ : ℝ) : ℂ) • w

omit [CompleteSpace E] in
theorem norm_unitOf {z : E} (hz : ‖z‖ = 1) (w : E) : ‖unitOf z w‖ = 1 := by
  unfold unitOf
  split_ifs with h
  · exact hz
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

omit [CompleteSpace E] in
theorem smul_unitOf (z w : E) : ((‖w‖ : ℝ) : ℂ) • unitOf z w = w := by
  unfold unitOf
  split_ifs with h
  · simp [h]
  · rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr h),
      Complex.ofReal_one, one_smul]

omit [CompleteSpace E] in
theorem rankOne_smul_self (r : ℂ) (v : E) :
    InnerProductSpace.rankOne ℂ (r • v) (r • v) =
      (r * (starRingEnd ℂ) r) • InnerProductSpace.rankOne ℂ v v := by
  ext x
  simp only [ContinuousLinearMap.smul_apply, InnerProductSpace.rankOne_apply, inner_smul_left,
    smul_smul]
  congr 1
  ring

omit [CompleteSpace E] in
/-- `|w⟩⟨w| − ‖w‖²|z⟩⟨z| = ‖w‖² (|v⟩⟨v| − |z⟩⟨z|)` with `v = unitOf z w`. -/
theorem term_eq (z w : E) :
    InnerProductSpace.rankOne ℂ w w - ((‖w‖ ^ 2 : ℝ) : ℂ) • InnerProductSpace.rankOne ℂ z z =
      ((‖w‖ ^ 2 : ℝ) : ℂ) • (InnerProductSpace.rankOne ℂ (unitOf z w) (unitOf z w) -
        InnerProductSpace.rankOne ℂ z z) := by
  have h1 : InnerProductSpace.rankOne ℂ w w =
      ((‖w‖ ^ 2 : ℝ) : ℂ) • InnerProductSpace.rankOne ℂ (unitOf z w) (unitOf z w) := by
    conv_lhs => rw [← smul_unitOf z w]
    rw [rankOne_smul_self, Complex.conj_ofReal]
    congr 1
    push_cast
    ring
  rw [h1, smul_sub]

omit [CompleteSpace E] in
/-- `λ |⟨v, z⟩|² = |⟨z, w⟩|²` with `λ = ‖w‖²`. -/
theorem weight_inner_sq (z w : E) :
    ‖w‖ ^ 2 * ‖⟪unitOf z w, z⟫_ℂ‖ ^ 2 = ‖⟪z, w⟫_ℂ‖ ^ 2 := by
  have h : ⟪w, z⟫_ℂ = (starRingEnd ℂ) ((‖w‖ : ℝ) : ℂ) * ⟪unitOf z w, z⟫_ℂ := by
    conv_lhs => rw [← smul_unitOf z w]
    rw [inner_smul_left]
  rw [norm_inner_symm z w, h, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_norm, mul_pow]

/-! ## (S4) Weighted Cauchy–Schwarz: `Σ λᵢ √xᵢ ≤ √(Σ λᵢ) √(Σ λᵢ xᵢ)` -/

theorem weighted_cauchy_schwarz {ι : Type*} (s : Finset ι) (lam x : ι → ℝ)
    (hl : ∀ i, 0 ≤ lam i) (hx : ∀ i, 0 ≤ x i) :
    (∑ i ∈ s, lam i * √(x i)) ^ 2 ≤ (∑ i ∈ s, lam i) * ∑ i ∈ s, lam i * x i := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => √(lam i)) (fun i => √(lam i) * √(x i))
  have e1 : ∀ i, √(lam i) * (√(lam i) * √(x i)) = lam i * √(x i) := by
    intro i; rw [← mul_assoc, Real.mul_self_sqrt (hl i)]
  have e2 : ∀ i, √(lam i) ^ 2 = lam i := fun i => Real.sq_sqrt (hl i)
  have e3 : ∀ i, (√(lam i) * √(x i)) ^ 2 = lam i * x i := by
    intro i; rw [mul_pow, Real.sq_sqrt (hl i), Real.sq_sqrt (hx i)]
  simp only [e1, e2, e3] at h
  exact h

/-! ## Assembly along the source route -/

/-- **R-828C5F7E `lem:fidelity`, source-route assembly.**  If `A ≥ 0` is trace class,
`Tr A = 1` and `‖z‖ = 1`, then `‖A − |z⟩⟨z|‖₁ ≤ 2√(1 − ⟨z, A z⟩)`.  S1 comes from the eigenvalue
equality (RankTwoTrace), S3 from trace-norm convergence of the series (FD3), S4 from the
weighted Cauchy–Schwarz.  S2 is the frame decomposition (explicit deviation, see header). -/
theorem fidelity_source (A : E →L[ℂ] E) (hA : A.IsPositive) (_hAtc : IsTraceClass A)
    (hTr : posTrace A = 1) (z : E) (hz : ‖z‖ = 1) :
    traceNorm (A - InnerProductSpace.rankOne ℂ z z) ≤
      ENNReal.ofReal (2 * √(1 - RCLike.re ⟪z, A z⟫_ℂ)) := by
  set b := refBasis E
  set a := RCLike.re ⟪z, A z⟫_ℂ with ha
  set P := InnerProductSpace.rankOne ℂ z z with hP
  -- (S2, frame) weights and unit vectors
  set w : RefIndex E → E := fun i => CFC.sqrt A (b i) with hw
  set lam : RefIndex E → ℝ := fun i => ‖w i‖ ^ 2 with hlam
  set v : RefIndex E → E := fun i => unitOf z (w i) with hv
  set x : RefIndex E → ℝ := fun i => 1 - ‖⟪v i, z⟫_ℂ‖ ^ 2 with hx
  have hF1 : HasSum lam 1 := hasSum_norm_sq_frame b hA hTr
  have hF2 := hasSum_norm_inner_frame b hA z
  have hl0 : ∀ i, 0 ≤ lam i := fun i => by positivity
  have hvn : ∀ i, ‖v i‖ = 1 := fun i => norm_unitOf hz (w i)
  have hx0 : ∀ i, 0 ≤ x i := by
    intro i
    have := norm_inner_le_norm (𝕜 := ℂ) (v i) z
    rw [hvn i, hz, one_mul] at this
    simp only [hx]
    nlinarith [norm_nonneg ⟪v i, z⟫_ℂ]
  have hlx : ∀ i, lam i * x i = lam i - ‖⟪z, w i⟫_ℂ‖ ^ 2 := by
    intro i
    simp only [hx, hlam]
    rw [mul_sub, mul_one, weight_inner_sq z (w i)]
  -- `D_s = Σ_{i∈s} λᵢ (|vᵢ⟩⟨vᵢ| − |z⟩⟨z|)`
  set D : Finset (RefIndex E) → E →L[ℂ] E := fun s => ∑ i ∈ s,
    ((lam i : ℝ) : ℂ) • (InnerProductSpace.rankOne ℂ (v i) (v i) - P) with hD
  -- (S1) + triangle + (S4): uniform bound on the partial sums
  have hbound : ∀ s, traceNorm (D s) ≤ ENNReal.ofReal (2 * √(1 - a)) := by
    intro s
    refine (traceNorm_sum_le s _).trans ?_
    have hterm : ∀ i, traceNorm (((lam i : ℝ) : ℂ) • (InnerProductSpace.rankOne ℂ (v i) (v i) - P))
        = ENNReal.ofReal (lam i * (2 * √(x i))) := by
      intro i
      rw [traceNorm_smul, hP, traceNorm_unit_sub_eq (v i) z (hvn i) hz, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (hl0 i), ← ENNReal.ofReal_mul (hl0 i)]
    simp_rw [hterm]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by have := hl0 i; positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hs1 : ∑ i ∈ s, lam i ≤ 1 := sum_le_hasSum s (fun i _ => hl0 i) hF1
    have hs2 : ∑ i ∈ s, lam i * x i ≤ 1 - a := by
      simp_rw [hlx]
      exact sum_le_hasSum s (fun i _ => by rw [← hlx]; exact mul_nonneg (hl0 i) (hx0 i))
        (hF1.sub hF2)
    have hcs := weighted_cauchy_schwarz s lam x hl0 hx0
    have hnn : 0 ≤ ∑ i ∈ s, lam i * √(x i) := Finset.sum_nonneg fun i _ => by
      have := hl0 i; positivity
    have hsq : (∑ i ∈ s, lam i * √(x i)) ^ 2 ≤ 1 - a :=
      hcs.trans ((mul_le_mul hs1 hs2 (Finset.sum_nonneg fun i _ =>
        mul_nonneg (hl0 i) (hx0 i)) zero_le_one).trans (by rw [one_mul]))
    have hle : ∑ i ∈ s, lam i * √(x i) ≤ √(1 - a) := by
      rw [← Real.sqrt_sq hnn]; exact Real.sqrt_le_sqrt hsq
    calc ∑ i ∈ s, lam i * (2 * √(x i)) = 2 * ∑ i ∈ s, lam i * √(x i) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
      _ ≤ 2 * √(1 - a) := by linarith
  -- decomposition `A − P = (A − A_s) + D_s + (λ_s − 1) P`
  have hD_eq : ∀ s, D s = frameSum b A s - ((∑ i ∈ s, lam i : ℝ) : ℂ) • P := by
    intro s
    show (∑ i ∈ s, ((lam i : ℝ) : ℂ) • (InnerProductSpace.rankOne ℂ (v i) (v i) - P)) = _
    rw [frameSum]
    simp_rw [hP, hv, hlam, ← term_eq z (w _)]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
    push_cast
    rfl
  have hdecomp : ∀ s, A - P = (A - frameSum b A s) + D s +
      (((∑ i ∈ s, lam i) - 1 : ℝ) : ℂ) • P := by
    intro s
    rw [hD_eq s]
    push_cast
    rw [sub_smul, one_smul]
    abel
  have hPnorm : traceNorm P = 1 := by
    rw [hP, traceNorm_of_isPositive (InnerProductSpace.isPositive_rankOne_self z),
      posTrace_rankOne_self, hz]
    simp
  have hlam1 : ∀ s, ∑ i ∈ s, lam i ≤ 1 := fun s => sum_le_hasSum s (fun i _ => hl0 i) hF1
  have hstep : ∀ s, traceNorm (A - P) ≤
      traceNorm (A - frameSum b A s) + ENNReal.ofReal (2 * √(1 - a)) +
        traceNorm (A - frameSum b A s) := by
    intro s
    rw [hdecomp s]
    refine (traceNorm_add_le _ _).trans (add_le_add ((traceNorm_add_le _ _).trans
      (add_le_add le_rfl (hbound s))) ?_)
    rw [traceNorm_smul, hPnorm, mul_one, traceNorm_sub_frameSum b hA hTr s, Complex.norm_real,
      Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (by linarith [hlam1 s])]
  -- (S3) the series converges in trace norm; pass to the limit
  have hlim := tendsto_traceNorm_sub_frameSum b hA hTr
  have hlim2 : Filter.Tendsto (fun s => traceNorm (A - frameSum b A s) +
      ENNReal.ofReal (2 * √(1 - a)) + traceNorm (A - frameSum b A s)) Filter.atTop
      (nhds (0 + ENNReal.ofReal (2 * √(1 - a)) + 0)) :=
    (hlim.add tendsto_const_nhds).add hlim
  rw [zero_add, add_zero] at hlim2
  exact ge_of_tendsto' hlim2 hstep

/-- Source-route instance on the auxiliary label space `h = ℓ²(ℤ)`. -/
theorem fidelity_source_l2 (A : lp (fun _ : ℤ => ℂ) 2 →L[ℂ] lp (fun _ : ℤ => ℂ) 2)
    (hA : A.IsPositive) (hAtc : IsTraceClass A) (hTr : posTrace A = 1)
    (z : lp (fun _ : ℤ => ℂ) 2) (hz : ‖z‖ = 1) :
    traceNorm (A - InnerProductSpace.rankOne ℂ z z) ≤
      ENNReal.ofReal (2 * √(1 - RCLike.re ⟪z, A z⟫_ℂ)) :=
  fidelity_source A hA hAtc hTr z hz

end QuantumNLS.FidelitySource

#print axioms QuantumNLS.FidelitySource.term_eq
#print axioms QuantumNLS.FidelitySource.weighted_cauchy_schwarz
#print axioms QuantumNLS.FidelitySource.fidelity_source
#print axioms QuantumNLS.FidelitySource.fidelity_source_l2
