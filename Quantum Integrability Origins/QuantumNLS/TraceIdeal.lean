/-
QuantumNLS.TraceIdeal — adjoint invariance and ideal bounds for the trace norm, and the
bounded-weight comparison interface for DEF-031 (owner: opus_tensor).

Frozen imports, read-only: TraceCompact TCP1 (sha256 8805dbae…ef1e33), which brings Fidelity FD3
and TraceClass TC6.  No unbounded-operator or form work here: `A_k = 1 − Σ∂²` and its form
realization belong to the formalization's EnergyMultiplier chain.  The comparison below is stated for an
arbitrary bounded weight `W`, to be instantiated with `A_k^{-1/2}` there.

* `norm_sum_inner_le_traceNorm₂`: `|Σ_{i∈s} ⟪X bᵢ, A (Z bᵢ)⟫| ≤ ‖A‖₁` for contractions `X, Z`.
  This is TC6's polar-free regularized bound with a right contraction inserted; the Hilbert–Schmidt
  sum of `√|A| Z` is controlled through the swap identity.
* `traceNorm_adjoint`: `‖T†‖₁ = ‖T‖₁`.
* `traceNorm_mul_right_le`: `‖T X‖₁ ≤ ‖T‖₁ ‖X‖`.  `traceNorm_mul_mul_le`: `‖W T W'‖₁ ≤ ‖W‖ ‖T‖₁ ‖W'‖`.
* DEF-031 interface: `D = W T W` gives `‖D‖₁ ≤ ‖W‖² ‖T‖₁`, and energy-trace-norm convergence
  `‖T_N − T‖₁ → 0` gives trace-norm convergence `‖W (T_N − T) W‖₁ → 0`.
-/
import QuantumNLS.TraceCompact

open scoped InnerProductSpace ENNReal
open QuantumNLS.TraceClass QuantumNLS.TraceCompact Filter Topology

noncomputable section

namespace QuantumNLS.TraceIdeal

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem norm_sum_inner_le_traceNorm₂ (b : HilbertBasis ι ℂ E) (A X Z : E →L[ℂ] E)
    (hX : ‖X‖ ≤ 1) (hZ : ‖Z‖ ≤ 1) (hA : traceNorm A ≠ ⊤) (s : Finset ι) :
    ‖∑ i ∈ s, ⟪X (b i), A (Z (b i))⟫_ℂ‖ ≤ (traceNorm A).toReal := by
  set T := (traceNorm A).toReal with hT
  set R := rootAbs A with hRdef
  have hR : IsSelfAdjoint R := (rootAbs_nonneg A).isSelfAdjoint
  have hTn : 0 ≤ T := ENNReal.toReal_nonneg
  have hHS : hsSq b R = traceNorm A := (traceNorm_eq_hsSq_rootAbs b A).symm
  have hRZ : hsSq b (R * Z) ≤ traceNorm A := by
    rw [hsSq_eq_hsSq_adjoint b b]
    have e : ContinuousLinearMap.adjoint (R * Z) = star Z ∘L R := by
      rw [← ContinuousLinearMap.star_eq_adjoint, star_mul, hR.star_eq]; rfl
    rw [e]
    exact (hsSq_comp_le b (by rwa [norm_star]) R).trans hHS.le
  have hRsum : ∑ i ∈ s, ‖R (Z (b i))‖ ^ 2 ≤ T :=
    (sum_norm_sq_le b (R * Z) (ne_top_of_le_ne_top hA hRZ) s).trans
      (ENNReal.toReal_mono hA hRZ)
  have hbn : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  have hXb : ∀ i, ‖X (b i)‖ ≤ 1 := fun i =>
    (X.le_opNorm _).trans (by rw [hbn, mul_one]; exact hX)
  have hZb : ∀ i, ‖Z (b i)‖ ≤ 1 := fun i =>
    (Z.le_opNorm _).trans (by rw [hbn, mul_one]; exact hZ)
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set δ' : ℝ := δ / (s.card + 1) with hδ'def
  have hδ' : 0 < δ' := by positivity
  have hden : ∀ t : ℝ, 0 < t * t + δ' := fun t => add_pos_of_nonneg_of_pos (mul_self_nonneg t) hδ'
  obtain ⟨h, hh⟩ : ∃ h : ℝ → ℝ, h = fun t => t / (t * t + δ') := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun t => δ' / (t * t + δ') := ⟨_, rfl⟩
  have hcont : Continuous h := by
    rw [hh]; exact continuous_id.div (by fun_prop) (fun t => (hden t).ne')
  have gcont : Continuous g := by
    rw [hg]; exact continuous_const.div (by fun_prop) (fun t => (hden t).ne')
  set Y := A * cfc h R with hYdef
  have hdecomp : A = Y * R + A * cfc g R := by
    have hRid : cfc (fun t : ℝ => t) R = R := cfc_id' ℝ R
    have e1 : Y * R = A * cfc (fun t => h t * t) R := by
      rw [hYdef, mul_assoc, cfc_mul h (fun t : ℝ => t) R, hRid]
    have e2 : (fun t => h t * t + g t) = fun _ : ℝ => (1 : ℝ) := by
      funext t
      rw [hh, hg]
      simp only
      rw [div_mul_eq_mul_div, ← add_div, div_self (hden t).ne']
    rw [e1, ← mul_add, ← cfc_add (a := R) (fun t => h t * t) g, e2, cfc_const_one ℝ R, mul_one]
  have hgnorm : ‖A * cfc g R‖ ≤ δ' := by
    refine norm_mul_cfc_le A g gcont hδ'.le fun t => ?_
    rw [hg]
    simp only
    rw [abs_of_pos (div_pos hδ' (hden t)), div_mul_eq_mul_div, div_le_iff₀ (hden t)]
    nlinarith [mul_self_nonneg t]
  have hle : cfc (fun t => h t * (t * t * (t * t)) * h t) R ≤ CFC.abs A := by
    rw [abs_eq_cfc_sq]
    refine cfc_mono (fun t _ => ?_) ((hcont.mul (by fun_prop)).mul hcont).continuousOn
      (by fun_prop)
    have hD := hden t
    have hq0 : 0 ≤ t * t / (t * t + δ') := div_nonneg (mul_self_nonneg t) hD.le
    have hq1 : t * t / (t * t + δ') ≤ 1 := (div_le_one hD).mpr (by linarith)
    have e : h t * (t * t * (t * t)) * h t = (t * t) * ((t * t / (t * t + δ')) *
        (t * t / (t * t + δ'))) := by
      rw [hh]; simp only; field_simp
    rw [e]
    have : (t * t / (t * t + δ')) * (t * t / (t * t + δ')) ≤ 1 := by nlinarith
    nlinarith [mul_self_nonneg t]
  have hHSY : hsSq b Y ≤ traceNorm A := by
    rw [← traceIn_adjoint_comp_self b Y, traceNorm_eq b A]
    have e : ContinuousLinearMap.adjoint Y ∘L Y = star Y * Y := by
      rw [ContinuousLinearMap.star_eq_adjoint]; rfl
    rw [e, hYdef, star_mul_cfc A h h hcont hcont]
    exact traceIn_mono b hle
  have hswap : hsSq b (star Y * X) ≤ traceNorm A := by
    rw [hsSq_eq_hsSq_adjoint b b]
    have e : ContinuousLinearMap.adjoint (star Y * X) = star X ∘L Y := by
      rw [← ContinuousLinearMap.star_eq_adjoint, star_mul, star_star]; rfl
    rw [e]
    exact (hsSq_comp_le b (by rwa [norm_star]) Y).trans hHSY
  have hYX : ∑ i ∈ s, ‖(star Y * X) (b i)‖ ^ 2 ≤ T :=
    (sum_norm_sq_le b (star Y * X) (ne_top_of_le_ne_top hA hswap) s).trans
      (ENNReal.toReal_mono hA hswap)
  have hsplit : ∀ i, ⟪X (b i), A (Z (b i))⟫_ℂ =
      ⟪(star Y * X) (b i), R (Z (b i))⟫_ℂ + ⟪X (b i), (A * cfc g R) (Z (b i))⟫_ℂ := by
    intro i
    conv_lhs => rw [hdecomp]
    rw [ContinuousLinearMap.add_apply, inner_add_right, ContinuousLinearMap.mul_apply Y R,
      ContinuousLinearMap.mul_apply (star Y) X, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
  have hA1 : ‖∑ i ∈ s, ⟪(star Y * X) (b i), R (Z (b i))⟫_ℂ‖ ≤ T := by
    have h1 : ‖∑ i ∈ s, ⟪(star Y * X) (b i), R (Z (b i))⟫_ℂ‖ ≤
        ∑ i ∈ s, ‖(star Y * X) (b i)‖ * ‖R (Z (b i))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_inner_le_norm _ _)
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖(star Y * X) (b i)‖)
      (fun i => ‖R (Z (b i))‖)
    have h3 : 0 ≤ ∑ i ∈ s, ‖(star Y * X) (b i)‖ * ‖R (Z (b i))‖ :=
      Finset.sum_nonneg fun i _ => by positivity
    have h4 : (∑ i ∈ s, ‖(star Y * X) (b i)‖ * ‖R (Z (b i))‖) ^ 2 ≤ T * T :=
      h2.trans (mul_le_mul hYX hRsum (Finset.sum_nonneg fun i _ => by positivity) hTn)
    nlinarith
  have hA2 : ‖∑ i ∈ s, ⟪X (b i), (A * cfc g R) (Z (b i))⟫_ℂ‖ ≤ s.card * δ' := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ i ∈ s, ‖⟪X (b i), (A * cfc g R) (Z (b i))⟫_ℂ‖ ≤ δ' := by
      intro i _
      refine (norm_inner_le_norm _ _).trans ?_
      have hb2 : ‖(A * cfc g R) (Z (b i))‖ ≤ δ' := by
        have h1 := (A * cfc g R).le_opNorm (Z (b i))
        nlinarith [hZb i, norm_nonneg (Z (b i)), norm_nonneg (A * cfc g R), hgnorm]
      nlinarith [hXb i, norm_nonneg (X (b i)), norm_nonneg ((A * cfc g R) (Z (b i)))]
    calc ∑ i ∈ s, ‖⟪X (b i), (A * cfc g R) (Z (b i))⟫_ℂ‖ ≤ ∑ _i ∈ s, δ' := Finset.sum_le_sum this
      _ = s.card * δ' := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (s.card : ℝ) * δ' ≤ δ := by
    have hc : (0 : ℝ) < s.card + 1 := by
      have := Nat.cast_nonneg (α := ℝ) s.card; linarith
    have e : δ' * ((s.card : ℝ) + 1) = δ := div_mul_cancel₀ δ hc.ne'
    nlinarith
  calc ‖∑ i ∈ s, ⟪X (b i), A (Z (b i))⟫_ℂ‖
      = ‖∑ i ∈ s, ⟪(star Y * X) (b i), R (Z (b i))⟫_ℂ +
          ∑ i ∈ s, ⟪X (b i), (A * cfc g R) (Z (b i))⟫_ℂ‖ := by
        rw [← Finset.sum_add_distrib]; exact congrArg _ (Finset.sum_congr rfl fun i _ => hsplit i)
    _ ≤ ‖∑ i ∈ s, ⟪(star Y * X) (b i), R (Z (b i))⟫_ℂ‖ +
          ‖∑ i ∈ s, ⟪X (b i), (A * cfc g R) (Z (b i))⟫_ℂ‖ := norm_add_le _ _
    _ ≤ T + δ := by linarith

/-- **Adjoint bound** `‖T†‖₁ ≤ ‖T‖₁`. -/
theorem traceNorm_adjoint_le (T : E →L[ℂ] E) :
    traceNorm (ContinuousLinearMap.adjoint T) ≤ traceNorm T := by
  by_cases hT : traceNorm T = ⊤
  · rw [hT]; exact le_top
  rw [← ENNReal.ofReal_toReal hT]
  refine traceNorm_le_of_forall (refBasis E) _ fun X hX s => ?_
  set b := refBasis E
  have e : ∑ i ∈ s, ⟪X (b i), ContinuousLinearMap.adjoint T (b i)⟫_ℂ =
      (starRingEnd ℂ) (∑ i ∈ s, ⟪ContinuousLinearMap.id ℂ E (b i), T (X (b i))⟫_ℂ) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← inner_conj_symm, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.id_apply]
  rw [e]
  refine (RCLike.re_le_norm _).trans ?_
  rw [RCLike.norm_conj]
  exact norm_sum_inner_le_traceNorm₂ b T _ X ContinuousLinearMap.norm_id_le hX hT s

/-- **Adjoint invariance** `‖T†‖₁ = ‖T‖₁`. -/
theorem traceNorm_adjoint (T : E →L[ℂ] E) :
    traceNorm (ContinuousLinearMap.adjoint T) = traceNorm T := by
  refine le_antisymm (traceNorm_adjoint_le T) ?_
  have h := traceNorm_adjoint_le (ContinuousLinearMap.adjoint T)
  rwa [ContinuousLinearMap.adjoint_adjoint] at h

theorem IsTraceClass.adjoint {T : E →L[ℂ] E} (hT : IsTraceClass T) :
    IsTraceClass (ContinuousLinearMap.adjoint T) := by
  rw [IsTraceClass, traceNorm_adjoint]; exact hT

/-- **Right ideal property** `‖T X‖₁ ≤ ‖T‖₁ ‖X‖`. -/
theorem traceNorm_mul_right_le (T X : E →L[ℂ] E) :
    traceNorm (T * X) ≤ traceNorm T * ENNReal.ofReal ‖X‖ := by
  have e : T * X = ContinuousLinearMap.adjoint
      (ContinuousLinearMap.adjoint X * ContinuousLinearMap.adjoint T) := by
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.adjoint_adjoint]
  rw [e, traceNorm_adjoint, mul_comm]
  have h := traceNorm_mul_left_le (ContinuousLinearMap.adjoint X) (ContinuousLinearMap.adjoint T)
  rwa [LinearIsometryEquiv.norm_map, traceNorm_adjoint] at h

/-- **Two-sided bounded-weight bound** `‖W T W'‖₁ ≤ ‖W‖ ‖T‖₁ ‖W'‖`. -/
theorem traceNorm_mul_mul_le (W T W' : E →L[ℂ] E) :
    traceNorm (W * T * W') ≤ ENNReal.ofReal ‖W‖ * traceNorm T * ENNReal.ofReal ‖W'‖ := by
  refine (traceNorm_mul_right_le (W * T) W').trans ?_
  gcongr
  exact traceNorm_mul_left_le W T

/-! ## DEF-031 bounded-weight comparison interface

DEF-031 (definitions.tex:187): the additive energy trace norm of `D` is `‖A_k^{1/2} D A_k^{1/2}‖₁`.
When `D = W T W` with the bounded weight `W = A_k^{-1/2}` and `T` the form realization of
`A_k^{1/2} D A_k^{1/2}` (constructed in the formalization's EnergyMultiplier chain, not here), the energy trace
norm dominates the trace norm up to `‖W‖²`. -/

/-- `D = W T W` gives `‖D‖₁ ≤ ‖W‖² ‖T‖₁`. -/
theorem traceNorm_le_weighted {W T D : E →L[ℂ] E} (hD : D = W * T * W) :
    traceNorm D ≤ ENNReal.ofReal (‖W‖ ^ 2) * traceNorm T := by
  rw [hD]
  refine (traceNorm_mul_mul_le W T W).trans (le_of_eq ?_)
  rw [mul_comm (ENNReal.ofReal ‖W‖ * traceNorm T), ← mul_assoc,
    ← ENNReal.ofReal_mul (norm_nonneg W), sq]

/-- Energy-trace-norm convergence implies trace-norm convergence: if `‖T_N − T‖₁ → 0` then
`‖W T_N W − W T W‖₁ → 0`. -/
theorem tendsto_traceNorm_weighted {α : Type*} {l : Filter α} (W : E →L[ℂ] E)
    {T : E →L[ℂ] E} {TN : α → E →L[ℂ] E} (h : Tendsto (fun n => traceNorm (TN n - T)) l (𝓝 0)) :
    Tendsto (fun n => traceNorm (W * TN n * W - W * T * W)) l (𝓝 0) := by
  have hc : Tendsto (fun n => ENNReal.ofReal (‖W‖ ^ 2) * traceNorm (TN n - T)) l (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (‖W‖ ^ 2)) h
      (Or.inr ENNReal.ofReal_ne_top)
    rwa [mul_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc (fun n => zero_le)
    fun n => ?_
  refine traceNorm_le_weighted ?_
  rw [mul_sub, sub_mul]

end QuantumNLS.TraceIdeal

#print axioms QuantumNLS.TraceIdeal.norm_sum_inner_le_traceNorm₂
#print axioms QuantumNLS.TraceIdeal.traceNorm_adjoint
#print axioms QuantumNLS.TraceIdeal.traceNorm_mul_right_le
#print axioms QuantumNLS.TraceIdeal.traceNorm_mul_mul_le
#print axioms QuantumNLS.TraceIdeal.traceNorm_le_weighted
#print axioms QuantumNLS.TraceIdeal.tendsto_traceNorm_weighted
