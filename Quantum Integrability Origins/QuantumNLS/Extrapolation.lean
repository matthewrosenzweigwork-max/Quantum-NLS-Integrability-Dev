import QuantumNLS.Interpolation

/-!
# Deterministic extrapolation core for PROP-016 (source `Q7A:lem:extrap`)

Source: `source/chapters/propagation/window_reconstruction.tex`, lemma `Q7A:lem:extrap`
(`\ReportID{PROP-016}`), with the nodes `z_j^± = ±a + i y_j`. This file is owned by `haiku_inventory`.
It imports the FROZEN module `QuantumNLS.Interpolation` (PROP-015) read-only and does not modify it.

What is proved here, all without probabilistic input:

* **Uniform Lagrange coefficient bound** (the source's "translation by `a` makes the Lagrange
  coefficients uniformly bounded"): nodes `a + c_j` and points `a + w` have
  `ℓ_k(a+w) = ℓ_k(w)` for the nodes `c_j`, so `∑_k ‖ℓ_k(a+w)‖ ≤ Λ(W)` for `‖w‖ ≤ W`, with
  `Λ(W)` independent of `a`.
* **Restricted Cauchy transform remainder**: for a finite measure `μ` on `ℝ`, with
  `G_μ^{Icc}(z) = ∫_{[-R,R]} dμ(q)/(z-q)`, the interpolation identity of PROP-015 integrates to
  `‖G_μ^{Icc}(z) - ∑_k ℓ_k(z) G_μ^{Icc}(z_k)‖ ≤ C_{m,H,H₁} R^{-m-2} μ([-R,R])`.

The probabilistic node-error event and the moment/tail term are handled in later sections
(see the review record). Nothing here assumes a conclusion of PROP-016.
-/

namespace QuantumNLS.Extrapolation

open MeasureTheory Set Finset QuantumNLS.Interpolation

noncomputable section

variable {m : ℕ}

/-! ## Uniform Lagrange coefficient bound -/

/-- Translation invariance of the Lagrange basis: nodes `a + c_j` evaluated at `a + w` give the
Lagrange coefficients of the nodes `c_j` at `w`. -/
theorem lagrangeValue_shift (a : ℂ) (c : Fin (m + 1) → ℂ) (k : Fin (m + 1)) (w : ℂ) :
    lagrangeValue (fun j => a + c j) k (a + w) = lagrangeValue c k w := by
  rw [lagrangeValue_eq_prod, lagrangeValue_eq_prod]
  refine prod_congr rfl (fun j _ => ?_)
  rw [show a + w - (a + c j) = w - c j by ring, show a + c k - (a + c j) = c k - c j by ring]

/-- Norm bound for one Lagrange coefficient, with `‖w‖ ≤ W`. -/
theorem norm_lagrangeValue_le (c : Fin (m + 1) → ℂ) (k : Fin (m + 1)) (w : ℂ) (W : ℝ)
    (hw : ‖w‖ ≤ W) :
    ‖lagrangeValue c k w‖ ≤ ∏ j ∈ univ.erase k, (W + ‖c j‖) / ‖c k - c j‖ := by
  rw [lagrangeValue_eq_prod, norm_prod]
  apply prod_le_prod₀ (fun j _ => norm_nonneg _)
  intro j _
  rw [norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc ‖w - c j‖ ≤ ‖w‖ + ‖c j‖ := norm_sub_le _ _
    _ ≤ W + ‖c j‖ := by linarith

/-- The constant `Λ(W) = ∑_k ∏_{j≠k} (W + ‖c_j‖)/‖c_k - c_j‖`, depending only on the nodes `c`
and on `W`. -/
def lagrangeNormSum (c : Fin (m + 1) → ℂ) (W : ℝ) : ℝ :=
  ∑ k : Fin (m + 1), ∏ j ∈ univ.erase k, (W + ‖c j‖) / ‖c k - c j‖

/-- Uniform bound on the sum of Lagrange coefficient moduli, `‖w‖ ≤ W`. -/
theorem sum_norm_lagrangeValue_le (c : Fin (m + 1) → ℂ) (w : ℂ) (W : ℝ) (hw : ‖w‖ ≤ W) :
    ∑ k : Fin (m + 1), ‖lagrangeValue c k w‖ ≤ lagrangeNormSum c W :=
  sum_le_sum fun k _ => norm_lagrangeValue_le c k w W hw

/-- **Uniform Lagrange bound on the rectangle.** For nodes `a + c_j` and any `z` with
`‖z - a‖ ≤ W`, the coefficient sum is at most `Λ(W)`, independently of `a`. -/
theorem sum_norm_lagrange_nodes_le (a : ℂ) (c : Fin (m + 1) → ℂ) (z : ℂ) (W : ℝ)
    (hz : ‖z - a‖ ≤ W) :
    ∑ k : Fin (m + 1), ‖lagrangeValue (fun j => a + c j) k z‖ ≤ lagrangeNormSum c W := by
  have hz' : z = a + (z - a) := by ring
  rw [hz']
  simp only [lagrangeValue_shift]
  exact sum_norm_lagrangeValue_le c (z - a) W hz

/-! ## The restricted Cauchy transform and its extrapolation remainder -/

/-- The restricted Cauchy transform `∫_{[-R,R]} dμ(q)/(z - q)` of a measure on `ℝ`. -/
def cauchyIcc (μ : Measure ℝ) (R : ℝ) (z : ℂ) : ℂ :=
  ∫ q in Icc (-R) R, 1 / (z - (q : ℂ)) ∂μ

/-- The pointwise remainder integrated over `[-R,R]`: for a finite measure `μ`, the Cauchy
transform restricted to `[-R,R]` satisfies the Lagrange node identity up to
`C_{m,H,H₁} R^{-m-2}` times `μ([-R,R])`. -/
theorem cauchyIcc_remainder (μ : Measure ℝ) [IsFiniteMeasure μ] (a z : ℂ) (c : Fin (m + 1) → ℂ)
    (hc : Function.Injective c) (R H H1 : ℝ) (hR : 0 < R) (hH : 2 * H ≤ R) (hH1 : 2 * H1 ≤ R)
    (hza : ‖z - a‖ ≤ H) (hcH1 : ∀ j, ‖c j‖ ≤ H1) (ha : 2 * R ≤ ‖a‖) :
    ‖cauchyIcc μ R z - ∑ k : Fin (m + 1), lagrangeValue (fun j => a + c j) k z *
        cauchyIcc μ R (a + c k)‖
      ≤ 2 ^ (m + 2) * (H + H1) ^ (m + 1) / R ^ (m + 2) * μ.real (Icc (-R) R) := by
  set zs : Fin (m + 1) → ℂ := fun j => a + c j with hzsdef
  have hz : Function.Injective zs := fun i j hij => hc (by simpa [hzsdef] using hij)
  have hzsa : ∀ j, ‖zs j - a‖ ≤ H1 := fun j => by
    simp only [hzsdef, add_sub_cancel_left]
    exact hcH1 j
  -- pointwise remainder on `[-R,R]`
  have hpt : ∀ q ∈ Icc (-R) R, ‖1 / (z - (q : ℂ))
      - ∑ k : Fin (m + 1), lagrangeValue zs k z / (zs k - (q : ℂ))‖
      ≤ 2 ^ (m + 2) * (H + H1) ^ (m + 1) / R ^ (m + 2) := by
    intro q hq
    have hqn : ‖(q : ℂ)‖ ≤ R := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      exact ⟨hq.1, hq.2⟩
    exact cauchy_remainder_sum_bound zs hz (q : ℂ) z a R H H1 hR hH hH1 hza hzsa hqn ha
  -- the remainder integrand is integrable and nonvanishing denominators hold on `[-R,R]`
  have hden : ∀ k : Fin (m + 1), ∀ q ∈ Icc (-R) R, zs k - (q : ℂ) ≠ 0 := by
    intro k q hq
    have hqn : ‖(q : ℂ)‖ ≤ R := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      exact ⟨hq.1, hq.2⟩
    have h := (distance_lower_bounds zs (q : ℂ) z a R H H1 hR hH hH1 hza hzsa hqn ha).1 k
    intro h0
    rw [h0, norm_zero] at h
    linarith
  have hdenz : ∀ q ∈ Icc (-R) R, z - (q : ℂ) ≠ 0 := by
    intro q hq
    have hqn : ‖(q : ℂ)‖ ≤ R := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      exact ⟨hq.1, hq.2⟩
    have h := (distance_lower_bounds zs (q : ℂ) z a R H H1 hR hH hH1 hza hzsa hqn ha).2
    intro h0
    rw [h0, norm_zero] at h
    linarith
  have hcont_int : ∀ w : ℂ, (∀ q ∈ Icc (-R) R, w - (q : ℂ) ≠ 0) →
      IntegrableOn (fun q : ℝ => 1 / (w - (q : ℂ))) (Icc (-R) R) μ := by
    intro w hw
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    refine ContinuousOn.div continuousOn_const (continuousOn_const.sub ?_) (fun q hq => hw q hq)
    exact Complex.continuous_ofReal.continuousOn
  -- the identity: difference of integrals equals integral of the remainder
  have hsplit : cauchyIcc μ R z - ∑ k : Fin (m + 1), lagrangeValue zs k z * cauchyIcc μ R (zs k)
      = ∫ q in Icc (-R) R, (1 / (z - (q : ℂ))
          - ∑ k : Fin (m + 1), lagrangeValue zs k z / (zs k - (q : ℂ))) ∂μ := by
    unfold cauchyIcc
    have hint_sum : ∀ k : Fin (m + 1), IntegrableOn
        (fun q : ℝ => lagrangeValue zs k z / (zs k - (q : ℂ))) (Icc (-R) R) μ := by
      intro k
      have h := (hcont_int (zs k) (hden k)).const_mul (lagrangeValue zs k z)
      exact IntegrableOn.congr_fun h (fun q _ => by ring) measurableSet_Icc
    rw [integral_sub (hcont_int z hdenz) (integrable_finsetSum _ fun k _ => hint_sum k),
      integral_finsetSum _ fun k _ => hint_sum k]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← integral_const_mul]
    congr 1
    funext q
    ring
  rw [hsplit]
  have hbound := norm_integral_le_of_norm_le_const (μ := μ.restrict (Icc (-R) R))
    (f := fun q : ℝ => 1 / (z - (q : ℂ))
          - ∑ k : Fin (m + 1), lagrangeValue zs k z / (zs k - (q : ℂ)))
    (C := 2 ^ (m + 2) * (H + H1) ^ (m + 1) / R ^ (m + 2))
    ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun q hq => hpt q hq))
  rw [measureReal_restrict_apply_univ] at hbound
  exact hbound

/-! ## Tail of the Cauchy transform: moment (Markov) estimate -/

/-- The tail `∫_{ℝ \ [-R,R]} dμ(q)/(z - q)` of the Cauchy transform. -/
def cauchyTail (μ : Measure ℝ) (R : ℝ) (z : ℂ) : ℂ :=
  ∫ q in (Icc (-R) R)ᶜ, 1 / (z - (q : ℂ)) ∂μ

/-- **Tail estimate.** If `μ` has a finite moment of order `2p` and its mass outside `[-R,R]` is
at distance at least `d` from `z`, then the tail is at most
`d^{-1} · R^{-2p} · ∫ q^{2p} dμ`. The bound is the Markov inequality `μ(|q| > R) ≤ R^{-2p} ∫ q^{2p}`
combined with `|1/(z-q)| ≤ 1/d` on the tail. -/
theorem cauchyTail_norm_le (μ : Measure ℝ) [IsFiniteMeasure μ] (R d : ℝ) (hR : 0 < R)
    (hd : 0 < d) (z : ℂ) (p : ℕ) (hint : Integrable (fun q : ℝ => q ^ (2 * p)) μ)
    (hfar : ∀ᵐ q ∂μ, q ∉ Icc (-R) R → d ≤ ‖z - (q : ℂ)‖) :
    ‖cauchyTail μ R z‖ ≤ (1 / d) * ((∫ q, q ^ (2 * p) ∂μ) / R ^ (2 * p)) := by
  have h1 : ‖cauchyTail μ R z‖ ≤ (1 / d) * μ.real (Icc (-R) R)ᶜ := by
    unfold cauchyTail
    have h := norm_integral_le_of_norm_le_const (μ := μ.restrict (Icc (-R) R)ᶜ)
      (f := fun q : ℝ => 1 / (z - (q : ℂ))) (C := 1 / d)
      ((ae_restrict_iff' measurableSet_Icc.compl).2 (by
        filter_upwards [hfar] with q hq hqc
        rw [norm_div, norm_one]
        exact one_div_le_one_div_of_le hd (hq hqc)))
    rwa [measureReal_restrict_apply_univ] at h
  have hεpos : (0 : ℝ) < R ^ (2 * p) := pow_pos hR _
  have hnn : 0 ≤ᵐ[μ] (fun q : ℝ => q ^ (2 * p)) :=
    Filter.Eventually.of_forall fun q => (even_two_mul p).pow_nonneg q
  have hmk := mul_meas_ge_le_integral_of_nonneg hnn hint (R ^ (2 * p))
  have hsub : μ.real (Icc (-R) R)ᶜ ≤ μ.real {x : ℝ | R ^ (2 * p) ≤ x ^ (2 * p)} := by
    refine measureReal_mono (fun q hq => ?_) (measure_ne_top μ _)
    have hRq : R < |q| := by
      by_contra h
      exact hq ⟨(abs_le.1 (not_lt.1 h)).1, (abs_le.1 (not_lt.1 h)).2⟩
    show R ^ (2 * p) ≤ q ^ (2 * p)
    rw [← (even_two_mul p).pow_abs q]
    exact pow_le_pow_left₀ hR.le hRq.le _
  have h2 : μ.real (Icc (-R) R)ᶜ ≤ (∫ q, q ^ (2 * p) ∂μ) / R ^ (2 * p) := by
    rw [le_div_iff₀ hεpos]
    calc μ.real (Icc (-R) R)ᶜ * R ^ (2 * p)
        ≤ μ.real {x : ℝ | R ^ (2 * p) ≤ x ^ (2 * p)} * R ^ (2 * p) :=
          mul_le_mul_of_nonneg_right hsub hεpos.le
      _ = R ^ (2 * p) * μ.real {x : ℝ | R ^ (2 * p) ≤ x ^ (2 * p)} := mul_comm _ _
      _ ≤ ∫ x : ℝ, x ^ (2 * p) ∂μ := hmk
  calc ‖cauchyTail μ R z‖ ≤ (1 / d) * μ.real (Icc (-R) R)ᶜ := h1
    _ ≤ (1 / d) * ((∫ q, q ^ (2 * p) ∂μ) / R ^ (2 * p)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

/-- If the quantum measure has no mass outside `[-R,R]`, its tail vanishes. -/
theorem cauchyTail_eq_zero_of_mass (ν : Measure ℝ) (R : ℝ) (z : ℂ)
    (hν : ν (Icc (-R) R)ᶜ = 0) : cauchyTail ν R z = 0 := by
  unfold cauchyTail
  rw [Measure.restrict_eq_zero.2 hν, integral_zero_measure]

/-! ## Combined deterministic extrapolation core (PROP-016 without probabilistic input) -/

/-- Full Cauchy-transform difference of two finite measures `μ`, `ν` at `w`:
`G_μ(w) - G_ν(w)` with `G = (restricted part on [-R,R]) + (tail)`. -/
def fullDiff (μ ν : Measure ℝ) (R : ℝ) (w : ℂ) : ℂ :=
  (cauchyIcc μ R w + cauchyTail μ R w) - (cauchyIcc ν R w + cauchyTail ν R w)

theorem norm_sum_mul_le {ι : Type*} (s : Finset ι) (ℓ X : ι → ℂ) (E : ℝ)
    (hX : ∀ i ∈ s, ‖X i‖ ≤ E) :
    ‖∑ i ∈ s, ℓ i * X i‖ ≤ (∑ i ∈ s, ‖ℓ i‖) * E := by
  calc ‖∑ i ∈ s, ℓ i * X i‖ ≤ ∑ i ∈ s, ‖ℓ i * X i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ‖ℓ i‖ * E := sum_le_sum fun i hi => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hX i hi) (norm_nonneg _)
    _ = (∑ i ∈ s, ‖ℓ i‖) * E := (sum_mul _ _ _).symm

/-- **Deterministic extrapolation core.** For finite measures `μ` (classical) and `ν` (quantum)
with `ν` carried by `[-R,R]` and both restricted masses at most `1`, and with the moment and
distance hypotheses for the classical tail, the full difference at any `z` in the rectangle
satisfies

  `‖G_μ(z) - G_ν(z)‖ ≤ (Λ + 1) T + Λ E + 2 C_{m,H,H₁} R^{-m-2}`,

where `Λ = lagrangeNormSum c H` (uniform in `a`), `T` is the classical tail bound
`d^{-1} R^{-2p} ∫ q^{2p} dμ`, and `E` is any bound on the node errors `‖G_μ(z_k) - G_ν(z_k)‖`.
Only the hypotheses stated here are used; no probabilistic event is assumed. -/
theorem extrapolation_core (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (a z : ℂ) (c : Fin (m + 1) → ℂ) (hc : Function.Injective c) (R H H1 d : ℝ) (p : ℕ)
    (hR : 0 < R) (hd : 0 < d) (hH : 2 * H ≤ R) (hH1 : 2 * H1 ≤ R)
    (hza : ‖z - a‖ ≤ H) (hcH1 : ∀ j, ‖c j‖ ≤ H1) (ha : 2 * R ≤ ‖a‖)
    (hμint : Integrable (fun q : ℝ => q ^ (2 * p)) μ)
    (hfarz : ∀ᵐ q ∂μ, q ∉ Icc (-R) R → d ≤ ‖z - (q : ℂ)‖)
    (hfark : ∀ k : Fin (m + 1), ∀ᵐ q ∂μ, q ∉ Icc (-R) R → d ≤ ‖a + c k - (q : ℂ)‖)
    (hνsupp : ν (Icc (-R) R)ᶜ = 0)
    (hμmass : μ.real (Icc (-R) R) ≤ 1) (hνmass : ν.real (Icc (-R) R) ≤ 1)
    (E : ℝ) (hE0 : 0 ≤ E) (hE : ∀ k : Fin (m + 1), ‖fullDiff μ ν R (a + c k)‖ ≤ E) :
    ‖fullDiff μ ν R z‖
      ≤ (lagrangeNormSum c H + 1) * ((1 / d) * ((∫ q, q ^ (2 * p) ∂μ) / R ^ (2 * p)))
        + lagrangeNormSum c H * E + 2 * (2 ^ (m + 2) * (H + H1) ^ (m + 1) / R ^ (m + 2)) := by
  set Λ := lagrangeNormSum c H with hΛdef
  set C := 2 ^ (m + 2) * (H + H1) ^ (m + 1) / R ^ (m + 2) with hCdef
  set T := (1 / d) * ((∫ q, q ^ (2 * p) ∂μ) / R ^ (2 * p)) with hTdef
  have hH0 : 0 ≤ H := le_trans (norm_nonneg _) hza
  have hH10 : 0 ≤ H1 := le_trans (norm_nonneg _) (hcH1 ⟨0, Nat.succ_pos m⟩)
  have hC0 : 0 ≤ C :=
    div_nonneg (mul_nonneg (by positivity) (pow_nonneg (by linarith) _)) (pow_nonneg hR.le _)
  have hTz : ‖cauchyTail μ R z‖ ≤ T :=
    cauchyTail_norm_le μ R d hR hd z p hμint hfarz
  have hTk : ∀ k : Fin (m + 1), ‖cauchyTail μ R (a + c k)‖ ≤ T :=
    fun k => cauchyTail_norm_le μ R d hR hd (a + c k) p hμint (hfark k)
  have hT0 : 0 ≤ T := le_trans (norm_nonneg _) hTz
  have hνt : ∀ w, cauchyTail ν R w = 0 := fun w => cauchyTail_eq_zero_of_mass ν R w hνsupp
  have hRμ := cauchyIcc_remainder μ a z c hc R H H1 hR hH hH1 hza hcH1 ha
  have hRν := cauchyIcc_remainder ν a z c hc R H H1 hR hH hH1 hza hcH1 ha
  have hΛb : ∑ k : Fin (m + 1), ‖lagrangeValue (fun j => a + c j) k z‖ ≤ Λ :=
    sum_norm_lagrange_nodes_le a c z H hza
  -- exact identity
  have hfin : fullDiff μ ν R z
      = ((cauchyIcc μ R z - ∑ k : Fin (m + 1), lagrangeValue (fun j => a + c j) k z *
            cauchyIcc μ R (a + c k))
          - (cauchyIcc ν R z - ∑ k : Fin (m + 1), lagrangeValue (fun j => a + c j) k z *
            cauchyIcc ν R (a + c k)))
        + ∑ k : Fin (m + 1), lagrangeValue (fun j => a + c j) k z * fullDiff μ ν R (a + c k)
        - ∑ k : Fin (m + 1), lagrangeValue (fun j => a + c j) k z * cauchyTail μ R (a + c k)
        + cauchyTail μ R z := by
    unfold fullDiff
    simp only [hνt, add_zero, mul_add, mul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    ring
  have hS1 : ‖∑ k : Fin (m + 1), lagrangeValue (fun j => a + c j) k z * fullDiff μ ν R (a + c k)‖
      ≤ Λ * E :=
    le_trans (norm_sum_mul_le _ _ _ E (fun k _ => hE k))
      (mul_le_mul_of_nonneg_right hΛb hE0)
  have hS2 : ‖∑ k : Fin (m + 1), lagrangeValue (fun j => a + c j) k z * cauchyTail μ R (a + c k)‖
      ≤ Λ * T :=
    le_trans (norm_sum_mul_le _ _ _ T (fun k _ => hTk k))
      (mul_le_mul_of_nonneg_right hΛb hT0)
  have hRm : ‖cauchyIcc μ R z - ∑ k : Fin (m + 1), lagrangeValue (fun j => a + c j) k z *
      cauchyIcc μ R (a + c k)‖ ≤ C :=
    le_trans hRμ (mul_le_of_le_one_right hC0 hμmass)
  have hRn : ‖cauchyIcc ν R z - ∑ k : Fin (m + 1), lagrangeValue (fun j => a + c j) k z *
      cauchyIcc ν R (a + c k)‖ ≤ C :=
    le_trans hRν (mul_le_of_le_one_right hC0 hνmass)
  rw [hfin]
  set X := (cauchyIcc μ R z - ∑ k : Fin (m + 1), lagrangeValue (fun j => a + c j) k z *
      cauchyIcc μ R (a + c k)) - (cauchyIcc ν R z - ∑ k : Fin (m + 1), lagrangeValue (fun j => a + c j) k z *
      cauchyIcc ν R (a + c k)) with hXdef
  have hX : ‖X‖ ≤ 2 * C := by
    have := norm_sub_le (cauchyIcc μ R z - ∑ k : Fin (m + 1), lagrangeValue (fun j => a + c j) k z *
      cauchyIcc μ R (a + c k)) (cauchyIcc ν R z - ∑ k : Fin (m + 1), lagrangeValue (fun j => a + c j) k z *
      cauchyIcc ν R (a + c k))
    linarith
  have a1 := norm_add_le X (∑ k : Fin (m + 1), lagrangeValue (fun j => a + c j) k z *
      fullDiff μ ν R (a + c k))
  have a2 := norm_sub_le (X + ∑ k : Fin (m + 1), lagrangeValue (fun j => a + c j) k z *
      fullDiff μ ν R (a + c k)) (∑ k : Fin (m + 1), lagrangeValue (fun j => a + c j) k z *
      cauchyTail μ R (a + c k))
  have a3 := norm_add_le (X + ∑ k : Fin (m + 1), lagrangeValue (fun j => a + c j) k z *
      fullDiff μ ν R (a + c k) - ∑ k : Fin (m + 1), lagrangeValue (fun j => a + c j) k z *
      cauchyTail μ R (a + c k)) (cauchyTail μ R z)
  have hexp : (Λ + 1) * T = Λ * T + T := by ring
  linarith [hX, hS1, hS2, hTz, a1, a2, a3, hexp]

/-! ## Empirical measure of the quantum roots and the full Cauchy transform -/

open scoped ENNReal

/-- The empirical measure `(1/N) ∑_j δ_{q_j}` of `N` quantum roots `q_j ∈ ℝ`. -/
def empMeasure (N : ℕ) (q : Fin N → ℝ) : Measure ℝ :=
  ((N : ℝ≥0∞))⁻¹ • ∑ j, Measure.dirac (q j)

theorem empMeasure_univ (N : ℕ) (hN : 0 < N) (q : Fin N → ℝ) :
    empMeasure N q univ = 1 := by
  have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hN.ne'
  have hNt : (N : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top N
  unfold empMeasure
  rw [Measure.smul_apply, Measure.finsetSum_apply]
  simp only [measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]
  exact ENNReal.inv_mul_cancel hN0 hNt

theorem empMeasure_real_univ (N : ℕ) (hN : 0 < N) (q : Fin N → ℝ) :
    (empMeasure N q).real univ = 1 := by
  rw [measureReal_def, empMeasure_univ N hN q, ENNReal.toReal_one]

/-- If every root lies in `[-R,R]`, the empirical measure has no mass outside. -/
theorem empMeasure_compl_eq_zero (N : ℕ) (q : Fin N → ℝ) (R : ℝ)
    (hq : ∀ j, q j ∈ Icc (-R) R) : empMeasure N q (Icc (-R) R)ᶜ = 0 := by
  have h0 : ∀ j, Measure.dirac (q j) (Icc (-R) R)ᶜ = 0 := by
    intro j
    rw [Measure.dirac_apply' _ measurableSet_Icc.compl]
    exact Set.indicator_of_notMem (by simpa using hq j) _
  unfold empMeasure
  rw [Measure.smul_apply, Measure.finsetSum_apply]
  simp [h0]

theorem empMeasure_real_Icc_le_one (N : ℕ) (hN : 0 < N) (q : Fin N → ℝ) (R : ℝ) :
    (empMeasure N q).real (Icc (-R) R) ≤ 1 := by
  have hfin : empMeasure N q univ ≠ ∞ := by
    rw [empMeasure_univ N hN q]
    exact ENNReal.one_ne_top
  rw [← empMeasure_real_univ N hN q]
  exact measureReal_mono (subset_univ _) hfin

/-- Full Cauchy transform `G_μ(w) = ∫ dμ(q)/(w - q)`. -/
def Gfull (μ : Measure ℝ) (w : ℂ) : ℂ := ∫ q, 1 / (w - (q : ℂ)) ∂μ

/-- Splitting of the full transform along `[-R,R]` and its complement, given integrability of the
complement part. -/
theorem Gfull_eq_split (μ : Measure ℝ) [IsFiniteMeasure μ] (R : ℝ) (w : ℂ)
    (hw : ∀ q ∈ Icc (-R) R, w - (q : ℂ) ≠ 0)
    (hcompl : IntegrableOn (fun q : ℝ => 1 / (w - (q : ℂ))) (Icc (-R) R)ᶜ μ) :
    Gfull μ w = cauchyIcc μ R w + cauchyTail μ R w := by
  have hcont : ContinuousOn (fun q : ℝ => 1 / (w - (q : ℂ))) (Icc (-R) R) := by
    refine ContinuousOn.div continuousOn_const (continuousOn_const.sub ?_) (fun q hq => hw q hq)
    exact Complex.continuous_ofReal.continuousOn
  have hIcc : IntegrableOn (fun q : ℝ => 1 / (w - (q : ℂ))) (Icc (-R) R) μ :=
    ContinuousOn.integrableOn_compact isCompact_Icc hcont
  have hint : Integrable (fun q : ℝ => 1 / (w - (q : ℂ))) μ := by
    rw [← integrableOn_univ, ← Set.union_compl_self (Icc (-R) R)]
    exact hIcc.union hcompl
  unfold Gfull cauchyIcc cauchyTail
  rw [← integral_add_compl measurableSet_Icc hint]

/-- Integrability of the complement part from a finite-moment-free ae distance bound. -/
theorem integrableOn_tail_of_far (μ : Measure ℝ) [IsFiniteMeasure μ] (R d : ℝ) (hd : 0 < d)
    (w : ℂ) (hfar : ∀ᵐ q ∂μ, q ∉ Icc (-R) R → d ≤ ‖w - (q : ℂ)‖) :
    IntegrableOn (fun q : ℝ => 1 / (w - (q : ℂ))) (Icc (-R) R)ᶜ μ := by
  refine Measure.integrableOn_of_bounded (M := 1 / d) (measure_ne_top μ _) ?_ ?_
  · exact (Measurable.aestronglyMeasurable
      (measurable_const.div (measurable_const.sub Complex.measurable_ofReal)))
  · refine (ae_restrict_iff' measurableSet_Icc.compl).2 ?_
    filter_upwards [hfar] with q hq hqc
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hd (hq hqc)

/-- Integrability of the complement part when the measure has no mass there. -/
theorem integrableOn_compl_of_null (ν : Measure ℝ) (R : ℝ) (w : ℂ)
    (hν : ν (Icc (-R) R)ᶜ = 0) :
    IntegrableOn (fun q : ℝ => 1 / (w - (q : ℂ))) (Icc (-R) R)ᶜ ν := by
  unfold IntegrableOn
  rw [Measure.restrict_eq_zero.2 hν]
  exact integrable_zero_measure

/-- For a measure with no mass outside `[-R,R]`, the full transform is the restricted one. -/
theorem Gfull_eq_Icc_of_null (ν : Measure ℝ) [IsFiniteMeasure ν] (R : ℝ) (w : ℂ)
    (hw : ∀ q ∈ Icc (-R) R, w - (q : ℂ) ≠ 0) (hν : ν (Icc (-R) R)ᶜ = 0) :
    Gfull ν w = cauchyIcc ν R w := by
  rw [Gfull_eq_split ν R w hw (integrableOn_compl_of_null ν R w hν), cauchyTail_eq_zero_of_mass ν R w hν,
    add_zero]

/-- The deterministic difference equals the difference of full transforms, once the quantum
measure has no mass outside `[-R,R]` and the classical tail is controlled. -/
theorem fullDiff_eq_Gfull_sub (μ ν : Measure ℝ) (R : ℝ) (w : ℂ)
    (hμ : Gfull μ w = cauchyIcc μ R w + cauchyTail μ R w)
    (hν : Gfull ν w = cauchyIcc ν R w) (hνt : cauchyTail ν R w = 0) :
    fullDiff μ ν R w = Gfull μ w - Gfull ν w := by
  unfold fullDiff
  rw [hμ, hν, hνt, add_zero]

/-! ## Probabilistic error-tail assembly for PROP-016 -/

/-- Nonvanishing of `a + c_k - q` on `[-R,R]` from the cut geometry (nodes within `H₁`, `‖a‖ ≥ 2R`). -/
theorem node_sub_ne_of_mem_Icc (a : ℂ) (c : Fin (m + 1) → ℂ) (R H H1 : ℝ) (hR : 0 < R)
    (hH0 : 0 ≤ H) (hH : 2 * H ≤ R) (hH1 : 2 * H1 ≤ R) (hcH1 : ∀ j, ‖c j‖ ≤ H1) (ha : 2 * R ≤ ‖a‖)
    (q : ℝ) (hq : q ∈ Icc (-R) R) (k : Fin (m + 1)) : a + c k - (q : ℂ) ≠ 0 := by
  have hqn : ‖(q : ℂ)‖ ≤ R := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact ⟨hq.1, hq.2⟩
  have hzsa : ∀ j, ‖(fun j => a + c j) j - a‖ ≤ H1 := fun j => by simpa using hcH1 j
  have h := (distance_lower_bounds (fun j => a + c j) (q : ℂ) a a R H H1 hR hH hH1
    (by simp [hH0]) hzsa hqn ha).1 k
  intro h0
  simp only [h0] at h
  simp only [norm_zero] at h
  linarith

/-- Nonvanishing of `z - q` on `[-R,R]` for `‖z - a‖ ≤ H`. -/
theorem z_sub_ne_of_mem_Icc (a z : ℂ) (c : Fin (m + 1) → ℂ) (R H H1 : ℝ) (hR : 0 < R)
    (hH : 2 * H ≤ R) (hH1 : 2 * H1 ≤ R) (hza : ‖z - a‖ ≤ H) (hcH1 : ∀ j, ‖c j‖ ≤ H1)
    (ha : 2 * R ≤ ‖a‖) (q : ℝ) (hq : q ∈ Icc (-R) R) : z - (q : ℂ) ≠ 0 := by
  have hqn : ‖(q : ℂ)‖ ≤ R := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact ⟨hq.1, hq.2⟩
  have hzsa : ∀ j, ‖(fun j => a + c j) j - a‖ ≤ H1 := fun j => by simpa using hcH1 j
  have h := (distance_lower_bounds (fun j => a + c j) (q : ℂ) z a R H H1 hR hH hH1 hza hzsa
    hqn ha).2
  intro h0
  rw [h0, norm_zero] at h
  linarith

/-- **PROP-016 (probabilistic form, deterministic-core-based).** Let `q_1,…,q_N` be the random
quantum roots on a probability space `(Ω,P)`, with empirical measure `ν_ω = empMeasure N (q ω)`,
and let `μ` be the classical probability law with a finite moment of order `2p`. Assume:

* the moment and cut-distance hypotheses on `μ` (`hμint`, `hfarS`, `hfark`);
* the second-moment bound of the node errors, `E|G_N(z_k) - G(z_k)|² ≤ C_var/(N y_k²)` with
  `y_k = Im c_k > 0` (`hvar`, source `Q7A:eq:ms`), with `hsq` integrability.

Then, with `Λ = lagrangeNormSum c H`, `T = d^{-1} R^{-2p} ∫x^{2p}dμ`, `C = 2^{m+2}(H+H₁)^{m+1}R^{-m-2}`
and `B(ε) = (Λ+1)T + Λε + 2C`, the probability of the event that all roots lie in `[-R,R]` and
SOME `z` with `‖z-a‖ ≤ H` has `‖G_μ(z) - G_N(z)‖ > B(ε)` is at most `∑_k C_var/y_k² / (N ε²)`.
No probabilistic conclusion is assumed; the only probabilistic inputs are `hsq` and `hvar`. -/
theorem prop016_error_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (hN : 0 < N) (q : Ω → Fin N → ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : ℂ) (c : Fin (m + 1) → ℂ) (hc : Function.Injective c) (hyk : ∀ k, 0 < (c k).im)
    (R H H1 d : ℝ) (p : ℕ) (hR : 0 < R) (hd : 0 < d) (hH0 : 0 ≤ H)
    (hH : 2 * H ≤ R) (hH1 : 2 * H1 ≤ R) (hcH1 : ∀ j, ‖c j‖ ≤ H1) (ha : 2 * R ≤ ‖a‖)
    (hμint : Integrable (fun x : ℝ => x ^ (2 * p)) μ)
    (hfarS : ∀ z : ℂ, ‖z - a‖ ≤ H → ∀ᵐ x ∂μ, x ∉ Icc (-R) R → d ≤ ‖z - (x : ℂ)‖)
    (hfark : ∀ k : Fin (m + 1), ∀ᵐ x ∂μ, x ∉ Icc (-R) R → d ≤ ‖a + c k - (x : ℂ)‖)
    (hsq : ∀ k : Fin (m + 1), Integrable
      (fun ω => ‖Gfull μ (a + c k) - Gfull (empMeasure N (q ω)) (a + c k)‖ ^ 2) P)
    (Cvar : ℝ)
    (hvar : ∀ k : Fin (m + 1), ∫ ω, ‖Gfull μ (a + c k) - Gfull (empMeasure N (q ω)) (a + c k)‖ ^ 2 ∂P
      ≤ Cvar / ((N : ℝ) * (c k).im ^ 2))
    (ε : ℝ) (hε : 0 < ε) :
    P.real {ω | (∀ j, |q ω j| ≤ R) ∧ ∃ z : ℂ, ‖z - a‖ ≤ H ∧
        (lagrangeNormSum c H + 1) * ((1 / d) * ((∫ x, x ^ (2 * p) ∂μ) / R ^ (2 * p)))
          + lagrangeNormSum c H * ε + 2 * (2 ^ (m + 2) * (H + H1) ^ (m + 1) / R ^ (m + 2))
          < ‖Gfull μ z - Gfull (empMeasure N (q ω)) z‖}
      ≤ (∑ k : Fin (m + 1), Cvar / (c k).im ^ 2) / ((N : ℝ) * ε ^ 2) := by
  set Λ := lagrangeNormSum c H with hΛdef
  set T := (1 / d) * ((∫ x, x ^ (2 * p) ∂μ) / R ^ (2 * p)) with hTdef
  set C := 2 ^ (m + 2) * (H + H1) ^ (m + 1) / R ^ (m + 2) with hCdef
  set err : Ω → Fin (m + 1) → ℝ := fun ω k =>
    ‖Gfull μ (a + c k) - Gfull (empMeasure N (q ω)) (a + c k)‖ with herrdef
  have hμmass : μ.real (Icc (-R) R) ≤ 1 := by
    have h := measureReal_mono (μ := μ) (subset_univ (Icc (-R) R))
    rwa [probReal_univ] at h
  -- event inclusion: on the root event, small node errors force the bound at every `z`
  have hincl : {ω | (∀ j, |q ω j| ≤ R) ∧ ∃ z : ℂ, ‖z - a‖ ≤ H ∧
        (Λ + 1) * T + Λ * ε + 2 * C < ‖Gfull μ z - Gfull (empMeasure N (q ω)) z‖}
      ⊆ ⋃ k ∈ (univ : Finset (Fin (m + 1))), {ω | ε < err ω k} := by
    intro ω hω
    obtain ⟨hA, z, hz, hbad⟩ := hω
    by_contra hcon
    have hall : ∀ k : Fin (m + 1), err ω k ≤ ε := by
      intro k
      by_contra hk
      exact hcon (Set.mem_iUnion₂.2 ⟨k, Finset.mem_univ k, not_le.1 hk⟩)
    have : IsFiniteMeasure (empMeasure N (q ω)) := ⟨by
      rw [empMeasure_univ N hN]
      exact ENNReal.one_lt_top⟩
    have hqI : ∀ j, q ω j ∈ Icc (-R) R := fun j => abs_le.1 (hA j)
    have hνc := empMeasure_compl_eq_zero N (q ω) R hqI
    have hνm := empMeasure_real_Icc_le_one N hN (q ω) R
    have hmass : μ.real (Icc (-R) R) ≤ 1 := hμmass
    -- node identities
    have hnode : ∀ k : Fin (m + 1), ‖fullDiff μ (empMeasure N (q ω)) R (a + c k)‖ ≤ ε := by
      intro k
      have hw : ∀ x ∈ Icc (-R) R, a + c k - (x : ℂ) ≠ 0 :=
        fun x hx => node_sub_ne_of_mem_Icc a c R H H1 hR hH0 hH hH1 hcH1 ha x hx k
      have hμk := Gfull_eq_split μ R (a + c k) hw (integrableOn_tail_of_far μ R d hd _ (hfark k))
      have hνk := Gfull_eq_Icc_of_null (empMeasure N (q ω)) R (a + c k) hw hνc
      have hνt := cauchyTail_eq_zero_of_mass (empMeasure N (q ω)) R (a + c k) hνc
      rw [fullDiff_eq_Gfull_sub μ (empMeasure N (q ω)) R (a + c k) hμk hνk hνt]
      exact hall k
    -- the deterministic core at `z`
    have hcore := extrapolation_core μ (empMeasure N (q ω)) a z c hc R H H1 d p hR hd hH hH1
      (hza := hz) hcH1 ha hμint (hfarS z hz) hfark hνc hmass hνm ε hε.le
      (fun k => hnode k)
    have hzdiff : fullDiff μ (empMeasure N (q ω)) R z
        = Gfull μ z - Gfull (empMeasure N (q ω)) z := by
      have hw : ∀ x ∈ Icc (-R) R, z - (x : ℂ) ≠ 0 :=
        fun x hx => z_sub_ne_of_mem_Icc a z c R H H1 hR hH hH1 hz hcH1 ha x hx
      have hμz := Gfull_eq_split μ R z hw (integrableOn_tail_of_far μ R d hd z (hfarS z hz))
      have hνz := Gfull_eq_Icc_of_null (empMeasure N (q ω)) R z hw hνc
      have hνt := cauchyTail_eq_zero_of_mass (empMeasure N (q ω)) R z hνc
      exact fullDiff_eq_Gfull_sub μ (empMeasure N (q ω)) R z hμz hνz hνt
    rw [hzdiff] at hcore
    linarith
  -- union bound and Chebyshev on each node
  have hunion := measureReal_biUnion_finset_le (μ := P) (univ : Finset (Fin (m + 1)))
    (fun k => {ω | ε < err ω k})
  have hcheb : ∀ k : Fin (m + 1), P.real {ω | ε < err ω k} ≤
      (Cvar / ((N : ℝ) * (c k).im ^ 2)) / ε ^ 2 := by
    intro k
    have hnn : 0 ≤ᵐ[P] (fun ω => err ω k ^ 2) :=
      Filter.Eventually.of_forall fun ω => sq_nonneg _
    have hmk := mul_meas_ge_le_integral_of_nonneg hnn (hsq k) (ε ^ 2)
    have hsub : P.real {ω | ε < err ω k} ≤ P.real {x | ε ^ 2 ≤ err x k ^ 2} := by
      refine measureReal_mono (fun ω hω => ?_) (measure_ne_top P _)
      have hεω : ε < err ω k := hω
      show ε ^ 2 ≤ err ω k ^ 2
      nlinarith [norm_nonneg (Gfull μ (a + c k) - Gfull (empMeasure N (q ω)) (a + c k))]
    have hpos : 0 < ε ^ 2 := by positivity
    have h2 : P.real {ω | ε < err ω k} ≤ (∫ ω, err ω k ^ 2 ∂P) / ε ^ 2 := by
      rw [le_div_iff₀ hpos]
      calc P.real {ω | ε < err ω k} * ε ^ 2 ≤ P.real {x | ε ^ 2 ≤ err x k ^ 2} * ε ^ 2 :=
            mul_le_mul_of_nonneg_right hsub hpos.le
        _ = ε ^ 2 * P.real {x | ε ^ 2 ≤ err x k ^ 2} := mul_comm _ _
        _ ≤ ∫ ω, err ω k ^ 2 ∂P := hmk
    exact h2.trans (div_le_div_of_nonneg_right (hvar k) hpos.le)
  have hsum_eq : (∑ k : Fin (m + 1), Cvar / (c k).im ^ 2) / ((N : ℝ) * ε ^ 2)
      = ∑ k : Fin (m + 1), (Cvar / ((N : ℝ) * (c k).im ^ 2)) / ε ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hk : (c k).im ≠ 0 := (hyk k).ne'
    have hε2 : ε ^ 2 ≠ 0 := by positivity
    field_simp
  calc P.real {ω | (∀ j, |q ω j| ≤ R) ∧ ∃ z : ℂ, ‖z - a‖ ≤ H ∧
        (Λ + 1) * T + Λ * ε + 2 * C < ‖Gfull μ z - Gfull (empMeasure N (q ω)) z‖}
      ≤ P.real (⋃ k ∈ (univ : Finset (Fin (m + 1))), {ω | ε < err ω k}) :=
        measureReal_mono hincl (measure_ne_top P _)
    _ ≤ ∑ k ∈ (univ : Finset (Fin (m + 1))), P.real {ω | ε < err ω k} := hunion
    _ ≤ ∑ k ∈ (univ : Finset (Fin (m + 1))), (Cvar / ((N : ℝ) * (c k).im ^ 2)) / ε ^ 2 :=
        Finset.sum_le_sum fun k _ => hcheb k
    _ = (∑ k : Fin (m + 1), Cvar / (c k).im ^ 2) / ((N : ℝ) * ε ^ 2) := hsum_eq.symm

/-! ## Literal quantities of PROP-016: `G_N(z) = (1/N) ∑_j 1/(z - q_j)` and `G(z) = ∫ dμ/(z - q)` -/

/-- Integral of a function against the empirical measure is the normalized finite sum. -/
theorem integral_empMeasure (N : ℕ) (q : Fin N → ℝ) (f : ℝ → ℂ) :
    ∫ x, f x ∂(empMeasure N q) = (1 / (N : ℂ)) * ∑ j, f (q j) := by
  unfold empMeasure
  rw [integral_smul_measure, integral_finsetSum_measure]
  · have hc : ((N : ℝ≥0∞))⁻¹.toReal = 1 / (N : ℝ) := by
      rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]
    rw [hc, Complex.real_smul]
    congr 1
    · push_cast
      ring_nf
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_dirac]
  · intro j _
    exact integrable_dirac (by simp)

/-- The literal `G_N(z) = (1/N) ∑_j 1/(z - q_j)` is the full Cauchy transform of the empirical
measure. -/
theorem Gfull_empMeasure (N : ℕ) (q : Fin N → ℝ) (z : ℂ) :
    Gfull (empMeasure N q) z = (1 / (N : ℂ)) * ∑ j, 1 / (z - (q j : ℂ)) := by
  unfold Gfull
  exact integral_empMeasure N q (fun x => 1 / (z - (x : ℂ)))


theorem prop016_error_tail_set {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (hN : 0 < N) (q : Ω → Fin N → ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : ℂ) (c : Fin (m + 1) → ℂ) (hc : Function.Injective c) (hyk : ∀ k, 0 < (c k).im)
    (R H H1 d : ℝ) (p : ℕ) (hR : 0 < R) (hd : 0 < d) (hH0 : 0 ≤ H)
    (hH : 2 * H ≤ R) (hH1 : 2 * H1 ≤ R) (hcH1 : ∀ j, ‖c j‖ ≤ H1) (ha : 2 * R ≤ ‖a‖)
    (hμint : Integrable (fun x : ℝ => x ^ (2 * p)) μ)
    (S : Set ℂ) (hS : ∀ z ∈ S, ‖z - a‖ ≤ H)
    (hfarS : ∀ z ∈ S, ∀ᵐ x ∂μ, x ∉ Icc (-R) R → d ≤ ‖z - (x : ℂ)‖)
    (hfark : ∀ k : Fin (m + 1), ∀ᵐ x ∂μ, x ∉ Icc (-R) R → d ≤ ‖a + c k - (x : ℂ)‖)
    (hsq : ∀ k : Fin (m + 1), Integrable
      (fun ω => ‖Gfull μ (a + c k) - Gfull (empMeasure N (q ω)) (a + c k)‖ ^ 2) P)
    (Cvar : ℝ)
    (hvar : ∀ k : Fin (m + 1), ∫ ω, ‖Gfull μ (a + c k) - Gfull (empMeasure N (q ω)) (a + c k)‖ ^ 2 ∂P
      ≤ Cvar / ((N : ℝ) * (c k).im ^ 2))
    (ε : ℝ) (hε : 0 < ε) :
    P.real {ω | (∀ j, |q ω j| ≤ R) ∧ ∃ z ∈ S,
        (lagrangeNormSum c H + 1) * ((1 / d) * ((∫ x, x ^ (2 * p) ∂μ) / R ^ (2 * p)))
          + lagrangeNormSum c H * ε + 2 * (2 ^ (m + 2) * (H + H1) ^ (m + 1) / R ^ (m + 2))
          < ‖Gfull μ z - Gfull (empMeasure N (q ω)) z‖}
      ≤ (∑ k : Fin (m + 1), Cvar / (c k).im ^ 2) / ((N : ℝ) * ε ^ 2) := by
  set Λ := lagrangeNormSum c H with hΛdef
  set T := (1 / d) * ((∫ x, x ^ (2 * p) ∂μ) / R ^ (2 * p)) with hTdef
  set C := 2 ^ (m + 2) * (H + H1) ^ (m + 1) / R ^ (m + 2) with hCdef
  set err : Ω → Fin (m + 1) → ℝ := fun ω k =>
    ‖Gfull μ (a + c k) - Gfull (empMeasure N (q ω)) (a + c k)‖ with herrdef
  have hμmass : μ.real (Icc (-R) R) ≤ 1 := by
    have h := measureReal_mono (μ := μ) (subset_univ (Icc (-R) R))
    rwa [probReal_univ] at h
  -- event inclusion: on the root event, small node errors force the bound at every `z`
  have hincl : {ω | (∀ j, |q ω j| ≤ R) ∧ ∃ z ∈ S,
        (Λ + 1) * T + Λ * ε + 2 * C < ‖Gfull μ z - Gfull (empMeasure N (q ω)) z‖}
      ⊆ ⋃ k ∈ (univ : Finset (Fin (m + 1))), {ω | ε < err ω k} := by
    intro ω hω
    obtain ⟨hA, z, hz, hbad⟩ := hω
    by_contra hcon
    have hall : ∀ k : Fin (m + 1), err ω k ≤ ε := by
      intro k
      by_contra hk
      exact hcon (Set.mem_iUnion₂.2 ⟨k, Finset.mem_univ k, not_le.1 hk⟩)
    have : IsFiniteMeasure (empMeasure N (q ω)) := ⟨by
      rw [empMeasure_univ N hN]
      exact ENNReal.one_lt_top⟩
    have hqI : ∀ j, q ω j ∈ Icc (-R) R := fun j => abs_le.1 (hA j)
    have hνc := empMeasure_compl_eq_zero N (q ω) R hqI
    have hνm := empMeasure_real_Icc_le_one N hN (q ω) R
    have hmass : μ.real (Icc (-R) R) ≤ 1 := hμmass
    -- node identities
    have hnode : ∀ k : Fin (m + 1), ‖fullDiff μ (empMeasure N (q ω)) R (a + c k)‖ ≤ ε := by
      intro k
      have hw : ∀ x ∈ Icc (-R) R, a + c k - (x : ℂ) ≠ 0 :=
        fun x hx => node_sub_ne_of_mem_Icc a c R H H1 hR hH0 hH hH1 hcH1 ha x hx k
      have hμk := Gfull_eq_split μ R (a + c k) hw (integrableOn_tail_of_far μ R d hd _ (hfark k))
      have hνk := Gfull_eq_Icc_of_null (empMeasure N (q ω)) R (a + c k) hw hνc
      have hνt := cauchyTail_eq_zero_of_mass (empMeasure N (q ω)) R (a + c k) hνc
      rw [fullDiff_eq_Gfull_sub μ (empMeasure N (q ω)) R (a + c k) hμk hνk hνt]
      exact hall k
    -- the deterministic core at `z`
    have hcore := extrapolation_core μ (empMeasure N (q ω)) a z c hc R H H1 d p hR hd hH hH1
      (hza := hS z hz) hcH1 ha hμint (hfarS z hz) hfark hνc hmass hνm ε hε.le
      (fun k => hnode k)
    have hzdiff : fullDiff μ (empMeasure N (q ω)) R z
        = Gfull μ z - Gfull (empMeasure N (q ω)) z := by
      have hw : ∀ x ∈ Icc (-R) R, z - (x : ℂ) ≠ 0 :=
        fun x hx => z_sub_ne_of_mem_Icc a z c R H H1 hR hH hH1 (hS z hz) hcH1 ha x hx
      have hμz := Gfull_eq_split μ R z hw (integrableOn_tail_of_far μ R d hd z (hfarS z hz))
      have hνz := Gfull_eq_Icc_of_null (empMeasure N (q ω)) R z hw hνc
      have hνt := cauchyTail_eq_zero_of_mass (empMeasure N (q ω)) R z hνc
      exact fullDiff_eq_Gfull_sub μ (empMeasure N (q ω)) R z hμz hνz hνt
    rw [hzdiff] at hcore
    linarith
  -- union bound and Chebyshev on each node
  have hunion := measureReal_biUnion_finset_le (μ := P) (univ : Finset (Fin (m + 1)))
    (fun k => {ω | ε < err ω k})
  have hcheb : ∀ k : Fin (m + 1), P.real {ω | ε < err ω k} ≤
      (Cvar / ((N : ℝ) * (c k).im ^ 2)) / ε ^ 2 := by
    intro k
    have hnn : 0 ≤ᵐ[P] (fun ω => err ω k ^ 2) :=
      Filter.Eventually.of_forall fun ω => sq_nonneg _
    have hmk := mul_meas_ge_le_integral_of_nonneg hnn (hsq k) (ε ^ 2)
    have hsub : P.real {ω | ε < err ω k} ≤ P.real {x | ε ^ 2 ≤ err x k ^ 2} := by
      refine measureReal_mono (fun ω hω => ?_) (measure_ne_top P _)
      have hεω : ε < err ω k := hω
      show ε ^ 2 ≤ err ω k ^ 2
      nlinarith [norm_nonneg (Gfull μ (a + c k) - Gfull (empMeasure N (q ω)) (a + c k))]
    have hpos : 0 < ε ^ 2 := by positivity
    have h2 : P.real {ω | ε < err ω k} ≤ (∫ ω, err ω k ^ 2 ∂P) / ε ^ 2 := by
      rw [le_div_iff₀ hpos]
      calc P.real {ω | ε < err ω k} * ε ^ 2 ≤ P.real {x | ε ^ 2 ≤ err x k ^ 2} * ε ^ 2 :=
            mul_le_mul_of_nonneg_right hsub hpos.le
        _ = ε ^ 2 * P.real {x | ε ^ 2 ≤ err x k ^ 2} := mul_comm _ _
        _ ≤ ∫ ω, err ω k ^ 2 ∂P := hmk
    exact h2.trans (div_le_div_of_nonneg_right (hvar k) hpos.le)
  have hsum_eq : (∑ k : Fin (m + 1), Cvar / (c k).im ^ 2) / ((N : ℝ) * ε ^ 2)
      = ∑ k : Fin (m + 1), (Cvar / ((N : ℝ) * (c k).im ^ 2)) / ε ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hk : (c k).im ≠ 0 := (hyk k).ne'
    have hε2 : ε ^ 2 ≠ 0 := by positivity
    field_simp
  calc P.real {ω | (∀ j, |q ω j| ≤ R) ∧ ∃ z ∈ S,
        (Λ + 1) * T + Λ * ε + 2 * C < ‖Gfull μ z - Gfull (empMeasure N (q ω)) z‖}
      ≤ P.real (⋃ k ∈ (univ : Finset (Fin (m + 1))), {ω | ε < err ω k}) :=
        measureReal_mono hincl (measure_ne_top P _)
    _ ≤ ∑ k ∈ (univ : Finset (Fin (m + 1))), P.real {ω | ε < err ω k} := hunion
    _ ≤ ∑ k ∈ (univ : Finset (Fin (m + 1))), (Cvar / ((N : ℝ) * (c k).im ^ 2)) / ε ^ 2 :=
        Finset.sum_le_sum fun k _ => hcheb k
    _ = (∑ k : Fin (m + 1), Cvar / (c k).im ^ 2) / ((N : ℝ) * ε ^ 2) := hsum_eq.symm


/-! ## Literal source instance of PROP-016: nodes `±a + i(η₀+1+j)`, rectangle, constants -/

/-- Source nodes `y_j = η₀+1+j`, `c_j = i y_j`, so `z_j^± = ±a + c_j` (`window_reconstruction.tex`). -/
def srcNodes (η0 : ℝ) (m : ℕ) : Fin (m + 1) → ℂ :=
  fun j => (((η0 + 1 + ((j : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I

/-- The source rectangle `{z : |Re z - a| ≤ 2ρ, |Im z| ≤ h+2ρ}` (the `+` cut with centre `a`; the
`−` cut is the same set with centre `−a`). -/
def srcRect (a ρ h : ℝ) : Set ℂ := {z | |z.re - a| ≤ 2 * ρ ∧ |z.im| ≤ h + 2 * ρ}

theorem srcNodes_im (η0 : ℝ) (m : ℕ) (j : Fin (m + 1)) :
    (srcNodes η0 m j).im = η0 + 1 + ((j : ℕ) : ℝ) := by
  simp [srcNodes]

theorem srcNodes_re (η0 : ℝ) (m : ℕ) (j : Fin (m + 1)) : (srcNodes η0 m j).re = 0 := by
  simp [srcNodes]

theorem srcNodes_injective (η0 : ℝ) (m : ℕ) : Function.Injective (srcNodes η0 m) := by
  intro i j hij
  have h := congrArg Complex.im hij
  rw [srcNodes_im, srcNodes_im] at h
  exact Fin.ext (by exact_mod_cast (by linarith : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ)))

theorem srcNodes_norm_le (η0 : ℝ) (hη0 : 0 ≤ η0) (m : ℕ) (j : Fin (m + 1)) :
    ‖srcNodes η0 m j‖ ≤ η0 + 1 + m := by
  have hj : ((j : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.lt_succ_iff.1 j.isLt
  unfold srcNodes
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith [(Nat.cast_nonneg (j : ℕ) : (0 : ℝ) ≤ ((j : ℕ) : ℝ))])]
  linarith

theorem srcNodes_im_pos (η0 : ℝ) (hη0 : 0 ≤ η0) (m : ℕ) (j : Fin (m + 1)) :
    0 < (srcNodes η0 m j).im := by
  rw [srcNodes_im]
  linarith [(Nat.cast_nonneg (j : ℕ) : (0 : ℝ) ≤ ((j : ℕ) : ℝ))]

/-- Rectangle points are within `h+4ρ` of the centre (since `‖w‖ ≤ |Re w| + |Im w|`). -/
theorem srcRect_norm_le (a ρ h : ℝ) (z : ℂ) (hz : z ∈ srcRect a ρ h) :
    ‖z - (a : ℂ)‖ ≤ h + 4 * ρ := by
  obtain ⟨h1, h2⟩ := hz
  have hn := Complex.norm_le_abs_re_add_abs_im (z - (a : ℂ))
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero] at hn
  linarith

/-- Distance from a rectangle point to a real point of distance `≥ δ` from the centre. -/
theorem srcRect_support_dist (a ρ h δ : ℝ) (z : ℂ) (hz : z ∈ srcRect a ρ h) (x : ℝ)
    (hx : δ ≤ |x - a|) : δ - 2 * ρ ≤ ‖z - (x : ℂ)‖ := by
  obtain ⟨h1, _⟩ := hz
  have hre : |z.re - x| ≤ ‖z - (x : ℂ)‖ := by
    have := Complex.abs_re_le_norm (z - (x : ℂ))
    simpa using this
  have htri : |x - a| ≤ |z.re - x| + |z.re - a| := by
    have := abs_sub_le x z.re a
    rw [abs_sub_comm x z.re] at this
    linarith [abs_sub_comm (z.re) a, this]
  linarith

/-- Node distance from a real point at distance `≥ δ` from the centre. -/
theorem node_support_dist (a : ℝ) (η0 : ℝ) (m : ℕ) (δ : ℝ) (x : ℝ) (hx : δ ≤ |x - a|)
    (j : Fin (m + 1)) : δ ≤ ‖(a : ℂ) + srcNodes η0 m j - (x : ℂ)‖ := by
  have hre : |((a : ℂ) + srcNodes η0 m j - (x : ℂ)).re| ≤ ‖(a : ℂ) + srcNodes η0 m j - (x : ℂ)‖ :=
    Complex.abs_re_le_norm _
  have h0 : ((a : ℂ) + srcNodes η0 m j - (x : ℂ)).re = a - x := by
    simp [srcNodes_re]
  rw [h0] at hre
  have : |a - x| = |x - a| := abs_sub_comm a x
  linarith

/-- Literal constants of PROP-016. `Λ` is the uniform Lagrange bound, `K` the variance sum,
`C_m = max(Λ, 2^{m+3}(H+H₁)^{m+1}, K)` and `C_{m,p} = (Λ+1)·∫x^{2p}dμ/(δ-2ρ)`. They depend only on
`m, η₀, H, ρ, δ, Cvar, μ, p`, not on `N, a, R, ε`. -/
def srcLam (η0 H : ℝ) (m : ℕ) : ℝ := lagrangeNormSum (srcNodes η0 m) H

def srcK (η0 Cvar : ℝ) (m : ℕ) : ℝ := ∑ k : Fin (m + 1), Cvar / (η0 + 1 + ((k : ℕ) : ℝ)) ^ 2

def srcCm (η0 H Cvar : ℝ) (m : ℕ) : ℝ :=
  max (max (srcLam η0 H m) (2 ^ (m + 3) * (H + (η0 + 1 + m)) ^ (m + 1))) (srcK η0 Cvar m)

def srcCmp (η0 H δ ρ : ℝ) (m : ℕ) (μ : Measure ℝ) (p : ℕ) : ℝ :=
  (srcLam η0 H m + 1) * ((∫ x, x ^ (2 * p) ∂μ) / (δ - 2 * ρ))

/-- Literal Cauchy transform of the roots, `G_N(z) = (1/N) ∑_j 1/(z - q_j)`. -/
def GN {N : ℕ} (q : Fin N → ℝ) (z : ℂ) : ℂ := (1 / (N : ℂ)) * ∑ j, 1 / (z - (q j : ℂ))

/-- The core bound with the literal constants: `(Λ+1)T + ΛE + 2C ≤ C_m E + C_m R^{-m-2} + C_{m,p}R^{-2p}`. -/
theorem literal_bound_le (m : ℕ) (η0 H δ ρ R E : ℝ) (μ : Measure ℝ) (p : ℕ) (Cvar : ℝ)
    (hR : 0 < R) (hE : 0 ≤ E) :
    (srcLam η0 H m + 1) * ((1 / (δ - 2 * ρ)) * ((∫ x, x ^ (2 * p) ∂μ) / R ^ (2 * p)))
      + srcLam η0 H m * E
      + 2 * (2 ^ (m + 2) * (H + (η0 + 1 + m)) ^ (m + 1) / R ^ (m + 2))
      ≤ srcCm η0 H Cvar m * E + srcCm η0 H Cvar m * (1 / R ^ (m + 2))
        + srcCmp η0 H δ ρ m μ p * (1 / R ^ (2 * p)) := by
  have hΛC : srcLam η0 H m ≤ srcCm η0 H Cvar m :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hC2 : 2 * (2 ^ (m + 2) * (H + (η0 + 1 + m)) ^ (m + 1) / R ^ (m + 2))
      ≤ srcCm η0 H Cvar m * (1 / R ^ (m + 2)) := by
    have h1 : 2 ^ (m + 3) * (H + (η0 + 1 + m)) ^ (m + 1) ≤ srcCm η0 H Cvar m :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    have hR' : 0 ≤ 1 / R ^ (m + 2) := by positivity
    calc 2 * (2 ^ (m + 2) * (H + (η0 + 1 + m)) ^ (m + 1) / R ^ (m + 2))
        = (2 ^ (m + 3) * (H + (η0 + 1 + m)) ^ (m + 1)) * (1 / R ^ (m + 2)) := by
          ring
      _ ≤ srcCm η0 H Cvar m * (1 / R ^ (m + 2)) :=
          mul_le_mul_of_nonneg_right h1 hR'
  have hT : (srcLam η0 H m + 1) * ((1 / (δ - 2 * ρ)) * ((∫ x, x ^ (2 * p) ∂μ) / R ^ (2 * p)))
      = srcCmp η0 H δ ρ m μ p * (1 / R ^ (2 * p)) := by
    unfold srcCmp
    ring
  have hLE : srcLam η0 H m * E ≤ srcCm η0 H Cvar m * E :=
    mul_le_mul_of_nonneg_right hΛC hE
  rw [hT]
  linarith

/-- **PROP-016, literal source packaging** (`window_reconstruction.tex`, `Q7A:lem:extrap`).

Setting: nodes `z_j^± = ±a + i(η₀+1+j)`, `0 ≤ j ≤ m`, realized by the real centre `a` with
`|a| ≥ 2R` (the sign `±` is the choice of `a`); rectangle `{|Re z − a| ≤ 2ρ, |Im z| ≤ h+2ρ}`
(`srcRect a ρ h`); `0 < ρ < δ/4`, `η₀ < h`, `H > h+4ρ`. The classical law `μ` is a probability
measure with a finite moment of order `2p` and `|x − a| ≥ δ` almost surely (distance from the cut).
The quantum roots are random `q : Ω → Fin N → ℝ` on a probability space.

Hypotheses are the section's model hypotheses only: the node second-moment bound
(`hvar`, `Q7A:eq:ms` at the nodes) with its integrability (`hsq`); no probabilistic conclusion
is assumed.

Conclusions:
* **(D) deterministic clause (`eq:extrap`).** On the root event `max_j |q_j| ≤ R`, if every node
  error is at most `E`, then for every `z` of the rectangle
  `|G_N(z) − G(z)| ≤ C_m E + C_m R^{-m-2} + C_{m,p} R^{-2p}`, with `C_m, C_{m,p}` the literal
  constants `srcCm`, `srcCmp` (independent of `N, a, R, E`). Here `G_N(z) = GN q z` and `G(z)` is
  the full integral `Gfull μ z`.
* **(P) probability clause.** For every `ε > 0`, the probability that all roots lie in `[-R,R]` and
  the right side of (D) with `E = ε` is exceeded at some `z` of the rectangle is at most
  `C_m/(Nε²)`. (For a continuous bounded function on the compact rectangle, `sup > c` is equivalent
  to `∃ z, > c`; the statement uses the existential form.) -/
theorem prop016_literal {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (hN : 0 < N) (q : Ω → Fin N → ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m : ℕ) (η0 δ ρ h H R a : ℝ) (p : ℕ)
    (hη0 : 0 < η0) (hρ : 0 < ρ) (hρδ : ρ < δ / 4) (hηh : η0 < h)
    (hH : h + 4 * ρ < H) (hR : 0 < R) (hRH : 2 * H ≤ R) (hRH1 : 2 * (η0 + 1 + m) ≤ R)
    (hcut : 2 * R ≤ |a|)
    (hμint : Integrable (fun x : ℝ => x ^ (2 * p)) μ)
    (hsupp : ∀ᵐ x ∂μ, δ ≤ |x - a|)
    (Cvar : ℝ)
    (hsq : ∀ k : Fin (m + 1), Integrable (fun ω =>
      ‖Gfull μ ((a : ℂ) + srcNodes η0 m k) - GN (q ω) ((a : ℂ) + srcNodes η0 m k)‖ ^ 2) P)
    (hvar : ∀ k : Fin (m + 1), ∫ ω,
      ‖Gfull μ ((a : ℂ) + srcNodes η0 m k) - GN (q ω) ((a : ℂ) + srcNodes η0 m k)‖ ^ 2 ∂P
        ≤ Cvar / ((N : ℝ) * (η0 + 1 + ((k : ℕ) : ℝ)) ^ 2)) :
    (∀ ω : Ω, (∀ j, |q ω j| ≤ R) → ∀ E : ℝ, 0 ≤ E →
        (∀ k : Fin (m + 1), ‖Gfull μ ((a : ℂ) + srcNodes η0 m k)
            - GN (q ω) ((a : ℂ) + srcNodes η0 m k)‖ ≤ E) →
        ∀ z ∈ srcRect a ρ h, ‖Gfull μ z - GN (q ω) z‖
          ≤ srcCm η0 H Cvar m * E + srcCm η0 H Cvar m * (1 / R ^ (m + 2))
            + srcCmp η0 H δ ρ m μ p * (1 / R ^ (2 * p))) ∧
    (∀ ε : ℝ, 0 < ε → P.real {ω | (∀ j, |q ω j| ≤ R) ∧ ∃ z ∈ srcRect a ρ h,
        srcCm η0 H Cvar m * ε + srcCm η0 H Cvar m * (1 / R ^ (m + 2))
          + srcCmp η0 H δ ρ m μ p * (1 / R ^ (2 * p)) < ‖Gfull μ z - GN (q ω) z‖}
      ≤ srcCm η0 H Cvar m / ((N : ℝ) * ε ^ 2)) := by
  have hH0 : 0 ≤ H := by linarith
  have hd : 0 < δ - 2 * ρ := by linarith
  have hcH1 : ∀ j : Fin (m + 1), ‖srcNodes η0 m j‖ ≤ η0 + 1 + m :=
    fun j => srcNodes_norm_le η0 hη0.le m j
  have hyk : ∀ k : Fin (m + 1), 0 < (srcNodes η0 m k).im :=
    fun k => srcNodes_im_pos η0 hη0.le m k
  have hc : Function.Injective (srcNodes η0 m) := srcNodes_injective η0 m
  have hGeq : ∀ (ω : Ω) (w : ℂ), Gfull (empMeasure N (q ω)) w = GN (q ω) w :=
    fun ω w => Gfull_empMeasure N (q ω) w
  have ha : 2 * R ≤ ‖(a : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hcut
  have hfarZ : ∀ z ∈ srcRect a ρ h, ∀ᵐ x ∂μ, x ∉ Icc (-R) R →
      δ - 2 * ρ ≤ ‖z - (x : ℂ)‖ :=
    fun z hz => Filter.Eventually.mono hsupp (fun x hx _ => srcRect_support_dist a ρ h δ z hz x hx)
  have hfarK : ∀ k : Fin (m + 1), ∀ᵐ x ∂μ, x ∉ Icc (-R) R →
      δ - 2 * ρ ≤ ‖(a : ℂ) + srcNodes η0 m k - (x : ℂ)‖ :=
    fun k => Filter.Eventually.mono hsupp (fun x hx _ =>
      le_trans (by linarith) (node_support_dist a η0 m δ x hx k))
  have hμ1 : μ.real (Icc (-R) R) ≤ 1 := by
    have h := measureReal_mono (μ := μ) (subset_univ (Icc (-R) R))
    rwa [probReal_univ] at h
  -- (D) deterministic clause
  have hD : ∀ ω : Ω, (∀ j, |q ω j| ≤ R) → ∀ E : ℝ, 0 ≤ E →
      (∀ k : Fin (m + 1), ‖Gfull μ ((a : ℂ) + srcNodes η0 m k)
          - GN (q ω) ((a : ℂ) + srcNodes η0 m k)‖ ≤ E) →
      ∀ z ∈ srcRect a ρ h, ‖Gfull μ z - GN (q ω) z‖
        ≤ srcCm η0 H Cvar m * E + srcCm η0 H Cvar m * (1 / R ^ (m + 2))
          + srcCmp η0 H δ ρ m μ p * (1 / R ^ (2 * p)) := by
    intro ω hA E hE hEk z hz
    have : IsFiniteMeasure (empMeasure N (q ω)) := ⟨by
      rw [empMeasure_univ N hN]
      exact ENNReal.one_lt_top⟩
    have hqI : ∀ j, q ω j ∈ Icc (-R) R := fun j => abs_le.1 (hA j)
    have hνc := empMeasure_compl_eq_zero N (q ω) R hqI
    have hνm := empMeasure_real_Icc_le_one N hN (q ω) R
    have hz' : ‖z - (a : ℂ)‖ ≤ H :=
      le_trans (srcRect_norm_le a ρ h z hz) (by linarith)
    have hRH1' : 2 * (η0 + 1 + m) ≤ R := hRH1
    -- node identities and the deterministic core
    have hEnode : ∀ k : Fin (m + 1), ‖fullDiff μ (empMeasure N (q ω)) R ((a : ℂ) + srcNodes η0 m k)‖ ≤ E := by
      intro k
      have hw : ∀ x ∈ Icc (-R) R, (a : ℂ) + srcNodes η0 m k - (x : ℂ) ≠ 0 :=
        fun x hx => node_sub_ne_of_mem_Icc (a : ℂ) (srcNodes η0 m) R H (η0 + 1 + m) hR hH0 hRH
          hRH1' hcH1 ha x hx k
      have hμk := Gfull_eq_split μ R ((a : ℂ) + srcNodes η0 m k) hw
        (integrableOn_tail_of_far μ R (δ - 2 * ρ) hd _ (hfarK k))
      have hνk := Gfull_eq_Icc_of_null (empMeasure N (q ω)) R ((a : ℂ) + srcNodes η0 m k) hw hνc
      have hνt := cauchyTail_eq_zero_of_mass (empMeasure N (q ω)) R ((a : ℂ) + srcNodes η0 m k) hνc
      rw [fullDiff_eq_Gfull_sub μ (empMeasure N (q ω)) R _ hμk hνk hνt, hGeq]
      exact hEk k
    have hcore := extrapolation_core μ (empMeasure N (q ω)) (a : ℂ) z (srcNodes η0 m) hc R H
      (η0 + 1 + m) (δ - 2 * ρ) p hR hd hRH hRH1' hz' hcH1 ha hμint (hfarZ z hz) hfarK hνc
      (by simp only [hμ1]) hνm E hE hEnode
    have hwz : ∀ x ∈ Icc (-R) R, z - (x : ℂ) ≠ 0 :=
      fun x hx => z_sub_ne_of_mem_Icc (a : ℂ) z (srcNodes η0 m) R H (η0 + 1 + m) hR hRH hRH1' hz'
        hcH1 ha x hx
    have hμz := Gfull_eq_split μ R z hwz (integrableOn_tail_of_far μ R (δ - 2 * ρ) hd z (hfarZ z hz))
    have hνz := Gfull_eq_Icc_of_null (empMeasure N (q ω)) R z hwz hνc
    have hνtz := cauchyTail_eq_zero_of_mass (empMeasure N (q ω)) R z hνc
    have hzdiff := fullDiff_eq_Gfull_sub μ (empMeasure N (q ω)) R z hμz hνz hνtz
    have hbound := literal_bound_le m η0 H δ ρ R E μ p Cvar hR hE
    rw [← hGeq ω z, ← hzdiff]
    exact le_trans hcore hbound
  refine ⟨hD, ?_⟩
  -- (P) probability clause
  intro ε hε
  have hsq' : ∀ k : Fin (m + 1), Integrable (fun ω =>
      ‖Gfull μ ((a : ℂ) + srcNodes η0 m k) - Gfull (empMeasure N (q ω)) ((a : ℂ) + srcNodes η0 m k)‖ ^ 2) P :=
    fun k => by simp only [hGeq]; exact hsq k
  have hvar' : ∀ k : Fin (m + 1), ∫ ω,
      ‖Gfull μ ((a : ℂ) + srcNodes η0 m k) - Gfull (empMeasure N (q ω)) ((a : ℂ) + srcNodes η0 m k)‖ ^ 2 ∂P
        ≤ Cvar / ((N : ℝ) * (srcNodes η0 m k).im ^ 2) := by
    intro k
    rw [srcNodes_im]
    simp only [hGeq]
    exact hvar k
  have hPr := prop016_error_tail_set P hN q μ (a : ℂ) (srcNodes η0 m) hc hyk R H (η0 + 1 + m)
    (δ - 2 * ρ) p hR hd hH0 hRH hRH1 hcH1 ha hμint (srcRect a ρ h)
    (fun z hz => le_trans (srcRect_norm_le a ρ h z hz) (by linarith)) hfarZ hfarK hsq' Cvar hvar'
    ε hε
  have hsub : {ω | (∀ j, |q ω j| ≤ R) ∧ ∃ z ∈ srcRect a ρ h,
        srcCm η0 H Cvar m * ε + srcCm η0 H Cvar m * (1 / R ^ (m + 2))
          + srcCmp η0 H δ ρ m μ p * (1 / R ^ (2 * p)) < ‖Gfull μ z - GN (q ω) z‖}
      ⊆ {ω | (∀ j, |q ω j| ≤ R) ∧ ∃ z ∈ srcRect a ρ h,
        (lagrangeNormSum (srcNodes η0 m) H + 1) * ((1 / (δ - 2 * ρ)) * ((∫ x, x ^ (2 * p) ∂μ) / R ^ (2 * p)))
          + lagrangeNormSum (srcNodes η0 m) H * ε + 2 * (2 ^ (m + 2) * (H + (η0 + 1 + m)) ^ (m + 1) / R ^ (m + 2))
          < ‖Gfull μ z - Gfull (empMeasure N (q ω)) z‖} := by
    intro ω hω
    obtain ⟨hA, z, hz, hlt⟩ := hω
    refine ⟨hA, z, hz, ?_⟩
    rw [hGeq]
    exact lt_of_le_of_lt (literal_bound_le m η0 H δ ρ R ε μ p Cvar hR hε.le) hlt
  have hK : (∑ k : Fin (m + 1), Cvar / (srcNodes η0 m k).im ^ 2) = srcK η0 Cvar m := by
    unfold srcK
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [srcNodes_im]
  have hNε : (0 : ℝ) < (N : ℝ) * ε ^ 2 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  calc P.real {ω | (∀ j, |q ω j| ≤ R) ∧ ∃ z ∈ srcRect a ρ h,
        srcCm η0 H Cvar m * ε + srcCm η0 H Cvar m * (1 / R ^ (m + 2))
          + srcCmp η0 H δ ρ m μ p * (1 / R ^ (2 * p)) < ‖Gfull μ z - GN (q ω) z‖}
      ≤ P.real {ω | (∀ j, |q ω j| ≤ R) ∧ ∃ z ∈ srcRect a ρ h,
        (lagrangeNormSum (srcNodes η0 m) H + 1) * ((1 / (δ - 2 * ρ)) * ((∫ x, x ^ (2 * p) ∂μ) / R ^ (2 * p)))
          + lagrangeNormSum (srcNodes η0 m) H * ε + 2 * (2 ^ (m + 2) * (H + (η0 + 1 + m)) ^ (m + 1) / R ^ (m + 2))
          < ‖Gfull μ z - Gfull (empMeasure N (q ω)) z‖} :=
        measureReal_mono hsub (measure_ne_top P _)
    _ ≤ (∑ k : Fin (m + 1), Cvar / (srcNodes η0 m k).im ^ 2) / ((N : ℝ) * ε ^ 2) := hPr
    _ = srcK η0 Cvar m / ((N : ℝ) * ε ^ 2) := by rw [hK]
    _ ≤ srcCm η0 H Cvar m / ((N : ℝ) * ε ^ 2) :=
        div_le_div_of_nonneg_right (le_max_right _ _) hNε.le

/-- Literal maximum form of the deterministic clause: the bound with `E` the maximum over the nodes
of `|G_N(z_j^±) − G(z_j^±)|`. -/
theorem prop016_literal_max {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (hN : 0 < N) (q : Ω → Fin N → ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m : ℕ) (η0 δ ρ h H R a : ℝ) (p : ℕ)
    (hη0 : 0 < η0) (hρ : 0 < ρ) (hρδ : ρ < δ / 4) (hηh : η0 < h)
    (hH : h + 4 * ρ < H) (hR : 0 < R) (hRH : 2 * H ≤ R) (hRH1 : 2 * (η0 + 1 + m) ≤ R)
    (hcut : 2 * R ≤ |a|)
    (hμint : Integrable (fun x : ℝ => x ^ (2 * p)) μ)
    (hsupp : ∀ᵐ x ∂μ, δ ≤ |x - a|)
    (Cvar : ℝ)
    (hsq : ∀ k : Fin (m + 1), Integrable (fun ω =>
      ‖Gfull μ ((a : ℂ) + srcNodes η0 m k) - GN (q ω) ((a : ℂ) + srcNodes η0 m k)‖ ^ 2) P)
    (hvar : ∀ k : Fin (m + 1), ∫ ω,
      ‖Gfull μ ((a : ℂ) + srcNodes η0 m k) - GN (q ω) ((a : ℂ) + srcNodes η0 m k)‖ ^ 2 ∂P
        ≤ Cvar / ((N : ℝ) * (η0 + 1 + ((k : ℕ) : ℝ)) ^ 2)) :
    ∀ ω : Ω, (∀ j, |q ω j| ≤ R) → ∀ z ∈ srcRect a ρ h,
      ‖Gfull μ z - GN (q ω) z‖
        ≤ srcCm η0 H Cvar m * (Finset.univ.sup' Finset.univ_nonempty fun k : Fin (m + 1) =>
              ‖Gfull μ ((a : ℂ) + srcNodes η0 m k) - GN (q ω) ((a : ℂ) + srcNodes η0 m k)‖)
          + srcCm η0 H Cvar m * (1 / R ^ (m + 2))
          + srcCmp η0 H δ ρ m μ p * (1 / R ^ (2 * p)) := by
  intro ω hA z hz
  have hD := (prop016_literal P hN q μ m η0 δ ρ h H R a p hη0 hρ hρδ hηh hH hR hRH hRH1 hcut hμint
    hsupp Cvar hsq hvar).1
  have hE0 : 0 ≤ Finset.univ.sup' Finset.univ_nonempty fun k : Fin (m + 1) =>
      ‖Gfull μ ((a : ℂ) + srcNodes η0 m k) - GN (q ω) ((a : ℂ) + srcNodes η0 m k)‖ :=
    le_trans (norm_nonneg _) (Finset.le_sup' (fun k : Fin (m + 1) =>
      ‖Gfull μ ((a : ℂ) + srcNodes η0 m k) - GN (q ω) ((a : ℂ) + srcNodes η0 m k)‖)
        (Finset.mem_univ (0 : Fin (m + 1))))
  exact hD ω hA _ hE0 (fun k => Finset.le_sup' (fun k : Fin (m + 1) =>
      ‖Gfull μ ((a : ℂ) + srcNodes η0 m k) - GN (q ω) ((a : ℂ) + srcNodes η0 m k)‖)
    (Finset.mem_univ k)) z hz

/-- Literal supremum form of the deterministic clause, `sup_{z ∈ rectangle} |G_N(z) − G(z)|`. -/
theorem prop016_literal_sup {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (hN : 0 < N) (q : Ω → Fin N → ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m : ℕ) (η0 δ ρ h H R a : ℝ) (p : ℕ)
    (hη0 : 0 < η0) (hρ : 0 < ρ) (hρδ : ρ < δ / 4) (hηh : η0 < h)
    (hH : h + 4 * ρ < H) (hR : 0 < R) (hRH : 2 * H ≤ R) (hRH1 : 2 * (η0 + 1 + m) ≤ R)
    (hcut : 2 * R ≤ |a|)
    (hμint : Integrable (fun x : ℝ => x ^ (2 * p)) μ)
    (hsupp : ∀ᵐ x ∂μ, δ ≤ |x - a|)
    (Cvar : ℝ)
    (hsq : ∀ k : Fin (m + 1), Integrable (fun ω =>
      ‖Gfull μ ((a : ℂ) + srcNodes η0 m k) - GN (q ω) ((a : ℂ) + srcNodes η0 m k)‖ ^ 2) P)
    (hvar : ∀ k : Fin (m + 1), ∫ ω,
      ‖Gfull μ ((a : ℂ) + srcNodes η0 m k) - GN (q ω) ((a : ℂ) + srcNodes η0 m k)‖ ^ 2 ∂P
        ≤ Cvar / ((N : ℝ) * (η0 + 1 + ((k : ℕ) : ℝ)) ^ 2)) :
    ∀ ω : Ω, (∀ j, |q ω j| ≤ R) →
      sSup ((fun z => ‖Gfull μ z - GN (q ω) z‖) '' srcRect a ρ h)
        ≤ srcCm η0 H Cvar m * (Finset.univ.sup' Finset.univ_nonempty fun k : Fin (m + 1) =>
              ‖Gfull μ ((a : ℂ) + srcNodes η0 m k) - GN (q ω) ((a : ℂ) + srcNodes η0 m k)‖)
          + srcCm η0 H Cvar m * (1 / R ^ (m + 2))
          + srcCmp η0 H δ ρ m μ p * (1 / R ^ (2 * p)) := by
  intro ω hA
  have hmax := prop016_literal_max P hN q μ m η0 δ ρ h H R a p hη0 hρ hρδ hηh hH hR hRH hRH1 hcut
    hμint hsupp Cvar hsq hvar ω hA
  have hne : ((fun z => ‖Gfull μ z - GN (q ω) z‖) '' srcRect a ρ h).Nonempty := by
    refine ⟨‖Gfull μ (a : ℂ) - GN (q ω) (a : ℂ)‖, ⟨(a : ℂ), ?_, rfl⟩⟩
    show |(a : ℂ).re - a| ≤ 2 * ρ ∧ |(a : ℂ).im| ≤ h + 2 * ρ
    simp only [Complex.ofReal_re, Complex.ofReal_im, sub_self, abs_zero]
    exact ⟨by linarith, by linarith⟩
  apply csSup_le hne
  rintro _ ⟨z, hz, rfl⟩
  exact hmax z hz

/-! ## Repair of clause (P): supremum versus existential, and discharge of the node-error integrability -/

theorem srcRect_isCompact (a ρ h : ℝ) : IsCompact (srcRect a ρ h) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact IsClosed.inter
      (isClosed_le (Complex.continuous_re.sub continuous_const).abs continuous_const)
      (isClosed_le Complex.continuous_im.abs continuous_const)
  · apply (Metric.isBounded_closedBall (x := (a : ℂ)) (r := h + 4 * ρ)).subset
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact srcRect_norm_le a ρ h z hz

theorem srcRect_nonempty (a ρ h : ℝ) (hρ : 0 ≤ ρ) (hh : 0 ≤ h) : (srcRect a ρ h).Nonempty := by
  refine ⟨(a : ℂ), ?_⟩
  show |(a : ℂ).re - a| ≤ 2 * ρ ∧ |(a : ℂ).im| ≤ h + 2 * ρ
  simp only [Complex.ofReal_re, Complex.ofReal_im, sub_self, abs_zero]
  exact ⟨by linarith, by linarith⟩

/-- Points of the rectangle are at distance `≥ R - 2ρ` from every real root with `|q| ≤ R`
(when `2R ≤ |a|`). -/
theorem rect_sub_root_dist (a ρ h R : ℝ) (z : ℂ) (hz : z ∈ srcRect a ρ h) (q : ℝ)
    (hcut : 2 * R ≤ |a|) (hq : |q| ≤ R) : R - 2 * ρ ≤ ‖z - (q : ℂ)‖ := by
  obtain ⟨h1, _⟩ := hz
  have hre : |z.re - q| ≤ ‖z - (q : ℂ)‖ := by
    simpa using Complex.abs_re_le_norm (z - (q : ℂ))
  have htri1 : |a - q| ≤ |z.re - q| + |z.re - a| := by
    have := abs_add_le (a - z.re) (z.re - q)
    rw [show a - z.re + (z.re - q) = a - q by ring, abs_sub_comm a z.re] at this
    linarith
  have htri2 : |a| - |q| ≤ |a - q| := abs_sub_abs_le_abs_sub a q
  linarith

/-- Continuity of the full Cauchy transform on the rectangle (dominated convergence; the
integrand is bounded by `(δ-2ρ)^{-1}` almost surely, since `|z-x| ≥ δ-2ρ`). -/
theorem Gfull_continuousOn_rect (μ : Measure ℝ) [IsFiniteMeasure μ] (a ρ h δ : ℝ)
    (hd : 0 < δ - 2 * ρ) (hsupp : ∀ᵐ x ∂μ, δ ≤ |x - a|) :
    ContinuousOn (fun z : ℂ => Gfull μ z) (srcRect a ρ h) := by
  unfold Gfull
  refine continuousOn_of_dominated (bound := fun _ => 1 / (δ - 2 * ρ)) ?_ ?_
    (integrable_const _) ?_
  · intro z _
    exact (Measurable.aestronglyMeasurable
      (measurable_const.div (measurable_const.sub Complex.measurable_ofReal)))
  · intro z hz
    filter_upwards [hsupp] with x hx
    show ‖1 / (z - (x : ℂ))‖ ≤ 1 / (δ - 2 * ρ)
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hd (srcRect_support_dist a ρ h δ z hz x hx)
  · filter_upwards [hsupp] with x hx
    refine ContinuousOn.div continuousOn_const
      (continuous_id.sub continuous_const).continuousOn (fun z hz => ?_)
    show z - (x : ℂ) ≠ 0
    have := srcRect_support_dist a ρ h δ z hz x hx
    intro h0
    rw [h0, norm_zero] at this
    linarith

/-- Continuity of the literal empirical transform on the rectangle, when the roots lie in
`[-R,R]` and `2ρ < R`. -/
theorem GN_continuousOn_rect {N : ℕ} (q : Fin N → ℝ) (a ρ h R : ℝ) (hcut : 2 * R ≤ |a|)
    (hR2 : 2 * ρ < R) (hA : ∀ j, |q j| ≤ R) :
    ContinuousOn (fun z : ℂ => GN q z) (srcRect a ρ h) := by
  unfold GN
  refine ContinuousOn.mul continuousOn_const (continuousOn_finsetSum Finset.univ fun j _ => ?_)
  refine ContinuousOn.div continuousOn_const
    (continuous_id.sub continuous_const).continuousOn (fun z hz => ?_)
  show z - (q j : ℂ) ≠ 0
  have := rect_sub_root_dist a ρ h R z hz (q j) hcut (hA j)
  intro h0
  rw [h0, norm_zero] at this
  linarith

/-- For a continuous function on a compact nonempty set, "some point exceeds `c`" is equivalent
to "the supremum exceeds `c`" (the supremum is attained). -/
theorem exists_lt_iff_lt_sSup {s : Set ℂ} (hs : IsCompact s) (hne : s.Nonempty) {f : ℂ → ℝ}
    (hf : ContinuousOn f s) (c : ℝ) :
    (∃ z ∈ s, c < f z) ↔ c < sSup (f '' s) := by
  have himg : IsCompact (f '' s) := hs.image_of_continuousOn hf
  have hne' : (f '' s).Nonempty := hne.image f
  constructor
  · rintro ⟨z, hz, hcz⟩
    exact lt_of_lt_of_le hcz (le_csSup himg.bddAbove ⟨z, hz, rfl⟩)
  · intro hc
    obtain ⟨z, hz, hfz⟩ := himg.sSup_mem hne'
    exact ⟨z, hz, by rw [hfz]; exact hc⟩

/-- Measurability and deterministic bound for the node errors, which discharges `hsq`:
for `Im w > 0` the Cauchy transform and the empirical transform are bounded by `1/Im w`, so the
squared node error is bounded and (for measurable roots) integrable. -/
theorem node_err_sq_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (hN : 0 < N) (q : Ω → Fin N → ℝ) (hq : Measurable q)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (w : ℂ) (hw : 0 < w.im) :
    Integrable (fun ω => ‖Gfull μ w - GN (q ω) w‖ ^ 2) P := by
  have hG : ‖Gfull μ w‖ ≤ 1 / w.im := by
    unfold Gfull
    have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x : ℝ => 1 / (w - (x : ℂ)))
      (C := 1 / w.im) (Filter.Eventually.of_forall fun x => by
        show ‖1 / (w - (x : ℂ))‖ ≤ 1 / w.im
        rw [norm_div, norm_one]
        apply one_div_le_one_div_of_le hw
        have h3 := Complex.abs_im_le_norm (w - (x : ℂ))
        simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h3
        exact le_trans (le_abs_self _) h3)
    rwa [probReal_univ, mul_one] at h
  have hGN : ∀ ω, ‖GN (q ω) w‖ ≤ 1 / w.im := by
    intro ω
    unfold GN
    rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    calc (1 / (N : ℝ)) * ‖∑ j, 1 / (w - (q ω j : ℂ))‖
        ≤ (1 / (N : ℝ)) * ∑ j, ‖1 / (w - (q ω j : ℂ))‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ (1 / (N : ℝ)) * ∑ _j : Fin N, (1 / w.im) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => by
            rw [norm_div, norm_one]
            apply one_div_le_one_div_of_le hw
            have h3 := Complex.abs_im_le_norm (w - (q ω j : ℂ))
            simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h3
            exact le_trans (le_abs_self _) h3) (by positivity)
      _ = 1 / w.im := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  have hbd : ∀ ω, ‖Gfull μ w - GN (q ω) w‖ ^ 2 ≤ (2 / w.im) ^ 2 := by
    intro ω
    have h1 : ‖Gfull μ w - GN (q ω) w‖ ≤ 2 / w.im := by
      have := norm_sub_le (Gfull μ w) (GN (q ω) w)
      have h2 : (2 : ℝ) / w.im = 1 / w.im + 1 / w.im := by ring
      linarith [hG, hGN ω]
    have h0 : 0 ≤ ‖Gfull μ w - GN (q ω) w‖ := norm_nonneg _
    exact pow_le_pow_left₀ h0 h1 2
  have hmeas : Measurable (fun ω => GN (q ω) w) := by
    unfold GN
    refine Measurable.const_mul (Finset.measurable_sum _ fun j _ => ?_) _
    exact measurable_const.div (measurable_const.sub
      (Complex.measurable_ofReal.comp ((measurable_pi_apply j).comp hq)))
  have hmeas2 : Measurable (fun ω => ‖Gfull μ w - GN (q ω) w‖ ^ 2) :=
    ((measurable_const.sub hmeas).norm).pow_const 2
  refine Integrable.of_bound hmeas2.aestronglyMeasurable ((2 / w.im) ^ 2)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact hbd ω

/-- **PROP-016, repaired packaging.** Same hypotheses as `prop016_literal`, except:
* `hsq` is discharged: the roots are random variables (`hq : Measurable q`, the coordinate law of
  the Bethe roots, implicit in `E_{N,u}`), and the node errors are deterministically bounded;
* clause (P) is stated in the source's **supremum** form, `sup_{z ∈ rectangle} |G − G_N|`,
  which is equivalent to the existential form for each root configuration in `[-R,R]^N`, by
  continuity of `G − G_N` on the compact rectangle (`Gfull_continuousOn_rect`,
  `GN_continuousOn_rect`, `exists_lt_iff_lt_sSup`).

Clause (D) is the deterministic `eq:extrap` (as in `prop016_literal`). Clause (P):
`P{roots in [-R,R] and c(ε) < sup_{z ∈ rectangle} |G(z) − G_N(z)|} ≤ C_m/(N ε²)`, with
`c(ε) = C_m ε + C_m R^{-m-2} + C_{m,p} R^{-2p}`. -/
theorem prop016_final {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (hN : 0 < N) (q : Ω → Fin N → ℝ) (hq : Measurable q)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m : ℕ) (η0 δ ρ h H R a : ℝ) (p : ℕ)
    (hη0 : 0 < η0) (hρ : 0 < ρ) (hρδ : ρ < δ / 4) (hηh : η0 < h)
    (hH : h + 4 * ρ < H) (hR : 0 < R) (hRH : 2 * H ≤ R) (hRH1 : 2 * (η0 + 1 + m) ≤ R)
    (hcut : 2 * R ≤ |a|)
    (hμint : Integrable (fun x : ℝ => x ^ (2 * p)) μ)
    (hsupp : ∀ᵐ x ∂μ, δ ≤ |x - a|)
    (Cvar : ℝ)
    (hvar : ∀ k : Fin (m + 1), ∫ ω,
      ‖Gfull μ ((a : ℂ) + srcNodes η0 m k) - GN (q ω) ((a : ℂ) + srcNodes η0 m k)‖ ^ 2 ∂P
        ≤ Cvar / ((N : ℝ) * (η0 + 1 + ((k : ℕ) : ℝ)) ^ 2)) :
    (∀ ω : Ω, (∀ j, |q ω j| ≤ R) → ∀ E : ℝ, 0 ≤ E →
        (∀ k : Fin (m + 1), ‖Gfull μ ((a : ℂ) + srcNodes η0 m k)
            - GN (q ω) ((a : ℂ) + srcNodes η0 m k)‖ ≤ E) →
        ∀ z ∈ srcRect a ρ h, ‖Gfull μ z - GN (q ω) z‖
          ≤ srcCm η0 H Cvar m * E + srcCm η0 H Cvar m * (1 / R ^ (m + 2))
            + srcCmp η0 H δ ρ m μ p * (1 / R ^ (2 * p))) ∧
    (∀ ε : ℝ, 0 < ε → P.real {ω | (∀ j, |q ω j| ≤ R) ∧
        srcCm η0 H Cvar m * ε + srcCm η0 H Cvar m * (1 / R ^ (m + 2))
          + srcCmp η0 H δ ρ m μ p * (1 / R ^ (2 * p))
          < sSup ((fun z => ‖Gfull μ z - GN (q ω) z‖) '' srcRect a ρ h)}
      ≤ srcCm η0 H Cvar m / ((N : ℝ) * ε ^ 2)) := by
  have hh0 : 0 ≤ h := by linarith
  have hd : 0 < δ - 2 * ρ := by linarith
  have hR2 : 2 * ρ < R := by linarith
  have hsq : ∀ k : Fin (m + 1), Integrable (fun ω =>
      ‖Gfull μ ((a : ℂ) + srcNodes η0 m k) - GN (q ω) ((a : ℂ) + srcNodes η0 m k)‖ ^ 2) P := by
    intro k
    refine node_err_sq_integrable P hN q hq μ _ ?_
    rw [Complex.add_im, Complex.ofReal_im, zero_add, srcNodes_im]
    linarith [(Nat.cast_nonneg (k : ℕ) : (0 : ℝ) ≤ ((k : ℕ) : ℝ))]
  obtain ⟨hD, hP⟩ := prop016_literal P hN q μ m η0 δ ρ h H R a p hη0 hρ hρδ hηh hH hR hRH hRH1
    hcut hμint hsupp Cvar hsq hvar
  refine ⟨hD, fun ε hε => ?_⟩
  have hset : {ω | (∀ j, |q ω j| ≤ R) ∧
        srcCm η0 H Cvar m * ε + srcCm η0 H Cvar m * (1 / R ^ (m + 2))
          + srcCmp η0 H δ ρ m μ p * (1 / R ^ (2 * p))
          < sSup ((fun z => ‖Gfull μ z - GN (q ω) z‖) '' srcRect a ρ h)}
      = {ω | (∀ j, |q ω j| ≤ R) ∧ ∃ z ∈ srcRect a ρ h,
        srcCm η0 H Cvar m * ε + srcCm η0 H Cvar m * (1 / R ^ (m + 2))
          + srcCmp η0 H δ ρ m μ p * (1 / R ^ (2 * p)) < ‖Gfull μ z - GN (q ω) z‖} := by
    ext ω
    constructor
    · rintro ⟨hA, hlt⟩
      have hcont : ContinuousOn (fun z => ‖Gfull μ z - GN (q ω) z‖) (srcRect a ρ h) :=
        ((Gfull_continuousOn_rect μ a ρ h δ hd hsupp).sub
          (GN_continuousOn_rect (q ω) a ρ h R hcut hR2 hA)).norm
      exact ⟨hA, (exists_lt_iff_lt_sSup (srcRect_isCompact a ρ h)
        (srcRect_nonempty a ρ h hρ.le hh0) hcont _).2 hlt⟩
    · rintro ⟨hA, hex⟩
      have hcont : ContinuousOn (fun z => ‖Gfull μ z - GN (q ω) z‖) (srcRect a ρ h) :=
        ((Gfull_continuousOn_rect μ a ρ h δ hd hsupp).sub
          (GN_continuousOn_rect (q ω) a ρ h R hcut hR2 hA)).norm
      exact ⟨hA, (exists_lt_iff_lt_sSup (srcRect_isCompact a ρ h)
        (srcRect_nonempty a ρ h hρ.le hh0) hcont _).1 hex⟩
  rw [hset]
  exact hP ε hε

/-! ## PROP-016 probability clause in the source's RIGHT-SIDE form (repair) -/

theorem srcLam_nonneg (η0 H : ℝ) (m : ℕ) (hH0 : 0 ≤ H) : 0 ≤ srcLam η0 H m := by
  unfold srcLam lagrangeNormSum
  refine Finset.sum_nonneg fun k _ => Finset.prod_nonneg fun j _ => ?_
  exact div_nonneg (by positivity) (norm_nonneg _)

/-- **Node union bound.** For node errors `err_k` with second moments bounded as in the source
(`Q7A:eq:ms`), `P(max_k err_k > ε)` is at most `∑_k Cvar/y_k² / (N ε²)` (Markov on each squared
error, then the union bound). -/
theorem node_union_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m N : ℕ) (hN : 0 < N) (err : Ω → Fin (m + 1) → ℝ) (y : Fin (m + 1) → ℝ) (hy : ∀ k, 0 < y k)
    (Cvar ε : ℝ) (hε : 0 < ε) (hsq : ∀ k, Integrable (fun ω => err ω k ^ 2) P)
    (hvar : ∀ k, ∫ ω, err ω k ^ 2 ∂P ≤ Cvar / ((N : ℝ) * y k ^ 2)) :
    P.real (⋃ k ∈ (univ : Finset (Fin (m + 1))), {ω | ε < err ω k})
      ≤ (∑ k, Cvar / y k ^ 2) / ((N : ℝ) * ε ^ 2) := by
  have hpos : 0 < ε ^ 2 := by positivity
  have hcheb : ∀ k : Fin (m + 1), P.real {ω | ε < err ω k} ≤ (Cvar / ((N : ℝ) * y k ^ 2)) / ε ^ 2 := by
    intro k
    have hnn : 0 ≤ᵐ[P] (fun ω => err ω k ^ 2) := Filter.Eventually.of_forall fun ω => sq_nonneg _
    have hmk := mul_meas_ge_le_integral_of_nonneg hnn (hsq k) (ε ^ 2)
    have hsub : P.real {ω | ε < err ω k} ≤ P.real {x | ε ^ 2 ≤ err x k ^ 2} := by
      refine measureReal_mono (fun ω hω => ?_) (measure_ne_top P _)
      have hεω : ε < err ω k := hω
      show ε ^ 2 ≤ err ω k ^ 2
      nlinarith
    have h2 : P.real {ω | ε < err ω k} ≤ (∫ ω, err ω k ^ 2 ∂P) / ε ^ 2 := by
      rw [le_div_iff₀ hpos]
      calc P.real {ω | ε < err ω k} * ε ^ 2 ≤ P.real {x | ε ^ 2 ≤ err x k ^ 2} * ε ^ 2 :=
            mul_le_mul_of_nonneg_right hsub hpos.le
        _ = ε ^ 2 * P.real {x | ε ^ 2 ≤ err x k ^ 2} := mul_comm _ _
        _ ≤ ∫ ω, err ω k ^ 2 ∂P := hmk
    exact h2.trans (div_le_div_of_nonneg_right (hvar k) hpos.le)
  have hunion := measureReal_biUnion_finset_le (μ := P) (univ : Finset (Fin (m + 1)))
    (fun k => {ω | ε < err ω k})
  have hsum_eq : (∑ k, Cvar / y k ^ 2) / ((N : ℝ) * ε ^ 2)
      = ∑ k, (Cvar / ((N : ℝ) * y k ^ 2)) / ε ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hk : y k ≠ 0 := (hy k).ne'
    have hε2 : ε ^ 2 ≠ 0 := hpos.ne'
    field_simp
  calc P.real (⋃ k ∈ (univ : Finset (Fin (m + 1))), {ω | ε < err ω k})
      ≤ ∑ k ∈ (univ : Finset (Fin (m + 1))), P.real {ω | ε < err ω k} := hunion
    _ ≤ ∑ k ∈ (univ : Finset (Fin (m + 1))), (Cvar / ((N : ℝ) * y k ^ 2)) / ε ^ 2 :=
        Finset.sum_le_sum fun k _ => hcheb k
    _ = (∑ k, Cvar / y k ^ 2) / ((N : ℝ) * ε ^ 2) := hsum_eq.symm

/-- The source node maximum `max_k |G(z_k^±) − G_N(z_k^±)|` (the RHS of `eq:extrap`). -/
def srcMaxErr (μ : Measure ℝ) {N : ℕ} (q : Fin N → ℝ) (a η0 : ℝ) (m : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun k : Fin (m + 1) =>
    ‖Gfull μ ((a : ℂ) + srcNodes η0 m k) - GN q ((a : ℂ) + srcNodes η0 m k)‖

theorem srcMaxErr_exists {N : ℕ} (μ : Measure ℝ) (q : Fin N → ℝ) (a η0 : ℝ) (m : ℕ) :
    ∃ k : Fin (m + 1), srcMaxErr μ q a η0 m
      = ‖Gfull μ ((a : ℂ) + srcNodes η0 m k) - GN q ((a : ℂ) + srcNodes η0 m k)‖ :=
  let ⟨k, _, hk⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun k : Fin (m + 1) => ‖Gfull μ ((a : ℂ) + srcNodes η0 m k) - GN q ((a : ℂ) + srcNodes η0 m k)‖)
  ⟨k, hk⟩

/-- **PROP-016, source RIGHT-SIDE probability clause.** For `ε > 0`,
`P{roots in [-R,R] and RHS(eq:extrap) > C_m ε + C_m R^{-m-2} + C_{m,p} R^{-2p}} ≤ C_m/(N ε²)`,
where `RHS(eq:extrap) = C_m · max_k |G − G_N|(z_k^±) + C_m R^{-m-2} + C_{m,p} R^{-2p}`.
Proof: the event forces `max_k` node error `> ε` (the common terms cancel and `C_m ≥ 0`), which is
covered by node Markov bounds and the union bound. No supremum, no continuity. -/
theorem prop016_rhs_event {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (hN : 0 < N) (q : Ω → Fin N → ℝ) (hq : Measurable q)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m : ℕ) (η0 δ ρ h H R a : ℝ) (p : ℕ)
    (hη0 : 0 < η0) (hρ : 0 < ρ) (hηh : η0 < h) (hH : h + 4 * ρ < H)
    (Cvar : ℝ)
    (hvar : ∀ k : Fin (m + 1), ∫ ω,
      ‖Gfull μ ((a : ℂ) + srcNodes η0 m k) - GN (q ω) ((a : ℂ) + srcNodes η0 m k)‖ ^ 2 ∂P
        ≤ Cvar / ((N : ℝ) * (η0 + 1 + ((k : ℕ) : ℝ)) ^ 2)) :
    ∀ ε : ℝ, 0 < ε → P.real {ω | (∀ j, |q ω j| ≤ R) ∧
        srcCm η0 H Cvar m * ε + srcCm η0 H Cvar m * (1 / R ^ (m + 2))
          + srcCmp η0 H δ ρ m μ p * (1 / R ^ (2 * p))
          < srcCm η0 H Cvar m * srcMaxErr μ (q ω) a η0 m
            + srcCm η0 H Cvar m * (1 / R ^ (m + 2))
            + srcCmp η0 H δ ρ m μ p * (1 / R ^ (2 * p))}
      ≤ srcCm η0 H Cvar m / ((N : ℝ) * ε ^ 2) := by
  intro ε hε
  have hH0 : 0 ≤ H := by linarith
  have hCnn : 0 ≤ srcCm η0 H Cvar m :=
    le_trans (srcLam_nonneg η0 H m hH0) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hsq : ∀ k : Fin (m + 1), Integrable (fun ω =>
      ‖Gfull μ ((a : ℂ) + srcNodes η0 m k) - GN (q ω) ((a : ℂ) + srcNodes η0 m k)‖ ^ 2) P := by
    intro k
    refine node_err_sq_integrable P hN q hq μ _ ?_
    rw [Complex.add_im, Complex.ofReal_im, zero_add, srcNodes_im]
    linarith [(Nat.cast_nonneg (k : ℕ) : (0 : ℝ) ≤ ((k : ℕ) : ℝ))]
  set err : Ω → Fin (m + 1) → ℝ := fun ω k =>
    ‖Gfull μ ((a : ℂ) + srcNodes η0 m k) - GN (q ω) ((a : ℂ) + srcNodes η0 m k)‖ with herr
  have hy : ∀ k : Fin (m + 1), 0 < (srcNodes η0 m k).im := fun k => srcNodes_im_pos η0 hη0.le m k
  have hunion := node_union_bound P m N hN err (fun k => (srcNodes η0 m k).im) hy Cvar ε hε hsq
    (fun k => by
      have := hvar k
      rw [srcNodes_im] at *
      exact this)
  -- the event lies inside the node-maximum event
  have hsub : {ω | (∀ j, |q ω j| ≤ R) ∧
        srcCm η0 H Cvar m * ε + srcCm η0 H Cvar m * (1 / R ^ (m + 2))
          + srcCmp η0 H δ ρ m μ p * (1 / R ^ (2 * p))
          < srcCm η0 H Cvar m * srcMaxErr μ (q ω) a η0 m
            + srcCm η0 H Cvar m * (1 / R ^ (m + 2))
            + srcCmp η0 H δ ρ m μ p * (1 / R ^ (2 * p))}
      ⊆ ⋃ k ∈ (univ : Finset (Fin (m + 1))), {ω | ε < err ω k} := by
    intro ω hω
    obtain ⟨_, hlt⟩ := hω
    have h1 : srcCm η0 H Cvar m * ε < srcCm η0 H Cvar m * srcMaxErr μ (q ω) a η0 m := by
      linarith
    have h2 : ε < srcMaxErr μ (q ω) a η0 m := lt_of_mul_lt_mul_left h1 hCnn
    obtain ⟨k, hk⟩ := srcMaxErr_exists μ (q ω) a η0 m
    refine Set.mem_iUnion₂.2 ⟨k, Finset.mem_univ k, ?_⟩
    show ε < err ω k
    rw [herr]
    simp only
    rw [← hk]
    exact h2
  calc P.real {ω | (∀ j, |q ω j| ≤ R) ∧
        srcCm η0 H Cvar m * ε + srcCm η0 H Cvar m * (1 / R ^ (m + 2))
          + srcCmp η0 H δ ρ m μ p * (1 / R ^ (2 * p))
          < srcCm η0 H Cvar m * srcMaxErr μ (q ω) a η0 m
            + srcCm η0 H Cvar m * (1 / R ^ (m + 2))
            + srcCmp η0 H δ ρ m μ p * (1 / R ^ (2 * p))}
      ≤ P.real (⋃ k ∈ (univ : Finset (Fin (m + 1))), {ω | ε < err ω k}) :=
        measureReal_mono hsub (measure_ne_top P _)
    _ ≤ (∑ k : Fin (m + 1), Cvar / (srcNodes η0 m k).im ^ 2) / ((N : ℝ) * ε ^ 2) := hunion
    _ = srcK η0 Cvar m / ((N : ℝ) * ε ^ 2) := by
        unfold srcK
        refine congrArg (· / ((N : ℝ) * ε ^ 2)) (Finset.sum_congr rfl fun k _ => ?_)
        rw [srcNodes_im]
    _ ≤ srcCm η0 H Cvar m / ((N : ℝ) * ε ^ 2) :=
        div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)

/-- **PROP-016, repaired packaging (round 9).** Clause (D) is the deterministic `eq:extrap` (the
per-`E`, max and sup forms of round 8, unchanged). Clause (P) is now the RIGHT-SIDE event of the
source (`prop016_rhs_event`). The round-8 clause (P) (left-side supremum) is retained only in
`prop016_final`, documented as superseded. -/
theorem prop016_final_rhs {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (hN : 0 < N) (q : Ω → Fin N → ℝ) (hq : Measurable q)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m : ℕ) (η0 δ ρ h H R a : ℝ) (p : ℕ)
    (hη0 : 0 < η0) (hρ : 0 < ρ) (hρδ : ρ < δ / 4) (hηh : η0 < h)
    (hH : h + 4 * ρ < H) (hR : 0 < R) (hRH : 2 * H ≤ R) (hRH1 : 2 * (η0 + 1 + m) ≤ R)
    (hcut : 2 * R ≤ |a|)
    (hμint : Integrable (fun x : ℝ => x ^ (2 * p)) μ)
    (hsupp : ∀ᵐ x ∂μ, δ ≤ |x - a|)
    (Cvar : ℝ)
    (hvar : ∀ k : Fin (m + 1), ∫ ω,
      ‖Gfull μ ((a : ℂ) + srcNodes η0 m k) - GN (q ω) ((a : ℂ) + srcNodes η0 m k)‖ ^ 2 ∂P
        ≤ Cvar / ((N : ℝ) * (η0 + 1 + ((k : ℕ) : ℝ)) ^ 2)) :
    (∀ ω : Ω, (∀ j, |q ω j| ≤ R) → ∀ E : ℝ, 0 ≤ E →
        (∀ k : Fin (m + 1), ‖Gfull μ ((a : ℂ) + srcNodes η0 m k)
            - GN (q ω) ((a : ℂ) + srcNodes η0 m k)‖ ≤ E) →
        ∀ z ∈ srcRect a ρ h, ‖Gfull μ z - GN (q ω) z‖
          ≤ srcCm η0 H Cvar m * E + srcCm η0 H Cvar m * (1 / R ^ (m + 2))
            + srcCmp η0 H δ ρ m μ p * (1 / R ^ (2 * p))) ∧
    (∀ ε : ℝ, 0 < ε → P.real {ω | (∀ j, |q ω j| ≤ R) ∧
        srcCm η0 H Cvar m * ε + srcCm η0 H Cvar m * (1 / R ^ (m + 2))
          + srcCmp η0 H δ ρ m μ p * (1 / R ^ (2 * p))
          < srcCm η0 H Cvar m * srcMaxErr μ (q ω) a η0 m
            + srcCm η0 H Cvar m * (1 / R ^ (m + 2))
            + srcCmp η0 H δ ρ m μ p * (1 / R ^ (2 * p))}
      ≤ srcCm η0 H Cvar m / ((N : ℝ) * ε ^ 2)) :=
  ⟨(prop016_final P hN q hq μ m η0 δ ρ h H R a p hη0 hρ hρδ hηh hH hR hRH hRH1 hcut hμint hsupp
      Cvar hvar).1,
    prop016_rhs_event P hN q hq μ m η0 δ ρ h H R a p hη0 hρ hηh hH Cvar hvar⟩

end

end QuantumNLS.Extrapolation

/-! Axiom check for the headline declarations (compile-log evidence). -/
#print axioms QuantumNLS.Extrapolation.extrapolation_core
#print axioms QuantumNLS.Extrapolation.Gfull_eq_split
#print axioms QuantumNLS.Extrapolation.node_union_bound
#print axioms QuantumNLS.Extrapolation.node_err_sq_integrable
#print axioms QuantumNLS.Extrapolation.prop016_literal
#print axioms QuantumNLS.Extrapolation.prop016_literal_max
#print axioms QuantumNLS.Extrapolation.prop016_literal_sup
#print axioms QuantumNLS.Extrapolation.prop016_rhs_event
#print axioms QuantumNLS.Extrapolation.prop016_final_rhs
#print axioms QuantumNLS.Extrapolation.exists_lt_iff_lt_sSup
