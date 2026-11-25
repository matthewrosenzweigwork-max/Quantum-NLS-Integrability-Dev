import Mathlib
import QuantumNLS.Extrapolation

/-!
# PROP-017 root-event constituent (source `Q7A:prop:packet`, `Q7A:eq:tail`, `Q7A:eq:bad`)

Source read (`source/chapters/propagation/window_reconstruction.tex`):

* The distribution of the Bethe spectral resolution of `u^{⊗N}` is `P_{N,u}` (line 7), so the random
  roots `q = (q_1,…,q_N)` are the coordinate law under `P_{N,u}`, and `E_{N,u}` is its expectation.
* Model hypothesis 1 (`Q7A:eq:tail`): for every fixed positive integer `p`, uniformly in `N` and
  `R ≥ R₀`,
  `E_{N,u}[(1/N) ∑_j 1_{|q_j|>R}] ≤ C_p R^{-2p} + D_p/(N R)`.
* PROP-017 (`Q7A:eq:bad`): `P_{N,u}(E_N^c) ≤ C_p N R^{-2p} + D_p R^{-1} + C_b (1+a)/(N ε³)`, and on
  `E_N` all roots satisfy `max_j |q_j| ≤ R` (`Q7A:eq:allroots`). The proof (line 113) takes the
  failure of the root event to have probability at most `C_p N R^{-2p} + D_p R^{-1}` by
  `Q7A:eq:tail`.

This file proves exactly that root-event part, from the tail hypothesis, as a deterministic
consequence of the union bound and integration. The Chebyshev term `C_b(1+a)/(Nε³)` and the node-error
part of `E_N` belong to PROP-016 and are not part of this constituent.

The tail hypothesis is an INPUT (a source model hypothesis), not a proved fact about the physical
model. Nothing here is assumed beyond it.
-/

namespace QuantumNLS.RootEvent

open MeasureTheory Set Finset

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The event that some root leaves `[-R, R]`, `⋃_j {|q_j| > R}`. -/
def outside {N : ℕ} (q : Ω → Fin N → ℝ) (R : ℝ) : Set Ω :=
  {ω | ∃ j : Fin N, R < |q ω j|}

/-- The empirical tail fraction `(1/N) ∑_j 1_{|q_j| > R}` of source `Q7A:eq:tail`. -/
def tailFraction {N : ℕ} (q : Ω → Fin N → ℝ) (R : ℝ) (ω : Ω) : ℝ :=
  (1 / (N : ℝ)) * ∑ j : Fin N, ({ω : Ω | R < |q ω j|}).indicator (fun _ => (1 : ℝ)) ω

theorem measurableSet_tail_j {N : ℕ} (q : Ω → Fin N → ℝ) (hq : Measurable q) (R : ℝ) (j : Fin N) :
    MeasurableSet {ω : Ω | R < |q ω j|} :=
  measurableSet_lt measurable_const
    (continuous_abs.measurable.comp ((measurable_pi_apply j).comp hq))

theorem measurableSet_outside {N : ℕ} (q : Ω → Fin N → ℝ) (hq : Measurable q) (R : ℝ) :
    MeasurableSet (outside q R) := by
  have h : outside q R = ⋃ j : Fin N, {ω : Ω | R < |q ω j|} := by
    ext ω
    simp [outside]
  rw [h]
  exact MeasurableSet.iUnion fun j => measurableSet_tail_j q hq R j

omit [MeasurableSpace Ω] in
/-- Pointwise domination of the root-failure indicator by the sum of the single-root indicators. -/
theorem indicator_outside_le_sum {N : ℕ} (q : Ω → Fin N → ℝ) (R : ℝ) (ω : Ω) :
    (outside q R).indicator (fun _ => (1 : ℝ)) ω
      ≤ ∑ j : Fin N, ({ω : Ω | R < |q ω j|}).indicator (fun _ => (1 : ℝ)) ω := by
  by_cases h : ω ∈ outside q R
  · obtain ⟨j, hj⟩ := h
    rw [indicator_of_mem (show ω ∈ outside q R from ⟨j, hj⟩)]
    have hj1 : ({ω : Ω | R < |q ω j|}).indicator (fun _ => (1 : ℝ)) ω = 1 :=
      indicator_of_mem (show ω ∈ {ω : Ω | R < |q ω j|} from hj) _
    have hnn : ∀ i ∈ (univ : Finset (Fin N)),
        0 ≤ ({ω : Ω | R < |q ω i|}).indicator (fun _ => (1 : ℝ)) ω := fun i _ =>
      indicator_nonneg (fun _ _ => zero_le_one) ω
    have := Finset.single_le_sum hnn (Finset.mem_univ j)
    rw [hj1] at this
    exact this
  · rw [indicator_of_notMem h]
    exact Finset.sum_nonneg fun i _ => indicator_nonneg (fun _ _ => zero_le_one) ω

/-- The root-event bound (PROP-017 root part): from the tail hypothesis `Q7A:eq:tail`, for `R ≥ R₀`,
`P(some root leaves [-R,R]) ≤ N C_p R^{-2p} + D_p / R`. -/
theorem root_event_bound {N : ℕ} (hN : 0 < N) (P : Measure Ω) [IsProbabilityMeasure P]
    (q : Ω → Fin N → ℝ) (hq : Measurable q) (p : ℕ) (C D R0 R : ℝ)
    (hR0 : R0 ≤ R) (hRpos : 0 < R)
    (hTail : ∀ R' : ℝ, R0 ≤ R' → 0 < R' →
      ∫ ω, tailFraction q R' ω ∂P ≤ C * (1 / R' ^ (2 * p)) + D / ((N : ℝ) * R')) :
    P.real (outside q R) ≤ (N : ℝ) * (C * (1 / R ^ (2 * p))) + D / R := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  -- indicator of each single root event is integrable (bounded, measurable)
  have hint_j : ∀ j : Fin N, Integrable
      (({ω : Ω | R < |q ω j|}).indicator (fun _ => (1 : ℝ))) P := fun j =>
    (integrable_const (1 : ℝ)).indicator (measurableSet_tail_j q hq R j)
  have hint_out : Integrable ((outside q R).indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_outside q hq R)
  have hsum_int : Integrable (fun ω => ∑ j : Fin N,
      ({ω : Ω | R < |q ω j|}).indicator (fun _ => (1 : ℝ)) ω) P :=
    integrable_finsetSum _ fun j _ => hint_j j
  -- step 1: P(outside) ≤ E[∑_j 1_{|q_j|>R}]
  have step1 : P.real (outside q R)
      ≤ ∫ ω, ∑ j : Fin N, ({ω : Ω | R < |q ω j|}).indicator (fun _ => (1 : ℝ)) ω ∂P := by
    rw [← integral_indicator_one (measurableSet_outside q hq R)]
    exact integral_mono hint_out hsum_int fun ω => indicator_outside_le_sum q R ω
  -- step 2: the sum equals N times the tail fraction
  have hsum_eq : (fun ω => ∑ j : Fin N,
      ({ω : Ω | R < |q ω j|}).indicator (fun _ => (1 : ℝ)) ω)
        = fun ω => (N : ℝ) * tailFraction q R ω := by
    funext ω
    unfold tailFraction
    rw [← mul_assoc, mul_one_div_cancel hNr, one_mul]
  -- step 3: apply the tail hypothesis at `R`
  have hT := hTail R hR0 hRpos
  rw [hsum_eq, integral_const_mul] at step1
  have hfin : (N : ℝ) * ∫ ω, tailFraction q R ω ∂P
      ≤ (N : ℝ) * (C * (1 / R ^ (2 * p)) + D / ((N : ℝ) * R)) :=
    mul_le_mul_of_nonneg_left hT (by positivity)
  have hsimp : (N : ℝ) * (C * (1 / R ^ (2 * p)) + D / ((N : ℝ) * R))
      = (N : ℝ) * (C * (1 / R ^ (2 * p))) + D / R := by
    field_simp
  linarith



/-! ## PROP-017 combination (`Q7A:eq:bad`): deterministic Lipschitz and covering steps -/

open QuantumNLS.Extrapolation

/-- Pointwise Lipschitz bound of `1/(z-q)` on the half-plane `|Im z| ≥ y`. -/
theorem inv_sub_lipschitz (z z' : ℂ) (q : ℝ) (y : ℝ) (hy : 0 < y) (hz : y ≤ |z.im|)
    (hz' : y ≤ |z'.im|) :
    ‖1 / (z - (q : ℂ)) - 1 / (z' - (q : ℂ))‖ ≤ ‖z - z'‖ / (y * y) := by
  have hzq : y ≤ ‖z - (q : ℂ)‖ := by
    have h := Complex.abs_im_le_norm (z - (q : ℂ))
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
    linarith [le_abs_self z.im]
  have hzq' : y ≤ ‖z' - (q : ℂ)‖ := by
    have h := Complex.abs_im_le_norm (z' - (q : ℂ))
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
    linarith [le_abs_self z'.im]
  have hne : z - (q : ℂ) ≠ 0 := fun h0 => by
    rw [h0, norm_zero] at hzq
    linarith
  have hne' : z' - (q : ℂ) ≠ 0 := fun h0 => by
    rw [h0, norm_zero] at hzq'
    linarith
  rw [div_sub_div _ _ hne hne', norm_div, norm_mul]
  have hnum : ‖1 * (z' - (q : ℂ)) - (z - (q : ℂ)) * 1‖ = ‖z - z'‖ := by
    rw [show 1 * (z' - (q : ℂ)) - (z - (q : ℂ)) * 1 = z' - z by ring, norm_sub_rev]
  rw [hnum]
  have hden : y * y ≤ ‖z - (q : ℂ)‖ * ‖z' - (q : ℂ)‖ := mul_le_mul hzq hzq' hy.le (norm_nonneg _)
  have hpos : 0 < y * y := mul_pos hy hy
  exact div_le_div_of_nonneg_left (norm_nonneg _) hpos hden

/-- Lipschitz bound of the classical Cauchy transform on the half-plane `|Im z| ≥ y`. -/
theorem Gfull_lipschitz (μ : Measure ℝ) [IsProbabilityMeasure μ] (z z' : ℂ) (y : ℝ) (hy : 0 < y)
    (hz : y ≤ |z.im|) (hz' : y ≤ |z'.im|) :
    ‖Gfull μ z - Gfull μ z'‖ ≤ ‖z - z'‖ / (y * y) := by
  have hint : ∀ w : ℂ, y ≤ |w.im| → Integrable (fun q : ℝ => 1 / (w - (q : ℂ))) μ := by
    intro w hw
    refine Integrable.of_bound ?_ (1 / y) (Filter.Eventually.of_forall fun q => ?_)
    · exact (Measurable.aestronglyMeasurable
        (measurable_const.div (measurable_const.sub Complex.measurable_ofReal)))
    · show ‖1 / (w - (q : ℂ))‖ ≤ 1 / y
      rw [norm_div, norm_one]
      apply one_div_le_one_div_of_le hy
      have h := Complex.abs_im_le_norm (w - (q : ℂ))
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
      linarith [le_abs_self w.im]
  unfold Gfull
  rw [← integral_sub (hint z hz) (hint z' hz')]
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun q : ℝ => 1 / (z - (q : ℂ)) - 1 / (z' - (q : ℂ))) (C := ‖z - z'‖ / (y * y))
    (Filter.Eventually.of_forall fun q => inv_sub_lipschitz z z' q y hy hz hz')
  rwa [probReal_univ, mul_one] at h

/-- Lipschitz bound of the empirical transform on the half-plane. -/
theorem GN_lipschitz {N : ℕ} (hN : 0 < N) (q : Fin N → ℝ) (z z' : ℂ) (y : ℝ) (hy : 0 < y)
    (hz : y ≤ |z.im|) (hz' : y ≤ |z'.im|) :
    ‖GN q z - GN q z'‖ ≤ ‖z - z'‖ / (y * y) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hdiff : GN q z - GN q z' = (1 / (N : ℂ)) * ∑ j, (1 / (z - (q j : ℂ)) - 1 / (z' - (q j : ℂ))) := by
    unfold GN
    rw [Finset.sum_sub_distrib, mul_sub]
  rw [hdiff, norm_mul, norm_div, norm_one, Complex.norm_natCast]
  have hsum : ‖∑ j, (1 / (z - (q j : ℂ)) - 1 / (z' - (q j : ℂ)))‖ ≤ N * (‖z - z'‖ / (y * y)) := by
    calc ‖∑ j, (1 / (z - (q j : ℂ)) - 1 / (z' - (q j : ℂ)))‖
        ≤ ∑ j, ‖1 / (z - (q j : ℂ)) - 1 / (z' - (q j : ℂ))‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin N, ‖z - z'‖ / (y * y) :=
          Finset.sum_le_sum fun j _ => inv_sub_lipschitz z z' (q j) y hy hz hz'
      _ = N * (‖z - z'‖ / (y * y)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc 1 / (N : ℝ) * ‖∑ j, (1 / (z - (q j : ℂ)) - 1 / (z' - (q j : ℂ)))‖
      ≤ 1 / (N : ℝ) * (N * (‖z - z'‖ / (y * y))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ‖z - z'‖ / (y * y) := by field_simp

/-- Lipschitz bound of the difference `G − G_N` on the half-plane `|Im z| ≥ y` with constant `2/y²`. -/
theorem diff_lipschitz (μ : Measure ℝ) [IsProbabilityMeasure μ] {N : ℕ} (hN : 0 < N) (q : Fin N → ℝ)
    (z z' : ℂ) (y : ℝ) (hy : 0 < y) (hz : y ≤ |z.im|) (hz' : y ≤ |z'.im|) :
    ‖(Gfull μ z - GN q z) - (Gfull μ z' - GN q z')‖ ≤ 2 * ‖z - z'‖ / (y * y) := by
  have h1 := Gfull_lipschitz μ z z' y hy hz hz'
  have h2 := GN_lipschitz hN q z z' y hy hz hz'
  have e : (Gfull μ z - GN q z) - (Gfull μ z' - GN q z')
      = (Gfull μ z - Gfull μ z') - (GN q z - GN q z') := by ring
  rw [e]
  calc ‖(Gfull μ z - Gfull μ z') - (GN q z - GN q z')‖
      ≤ ‖Gfull μ z - Gfull μ z'‖ + ‖GN q z - GN q z'‖ := norm_sub_le _ _
    _ ≤ ‖z - z'‖ / (y * y) + ‖z - z'‖ / (y * y) := add_le_add h1 h2
    _ = 2 * ‖z - z'‖ / (y * y) := by ring

/-- Covering of an interval by a finite mesh: every `x ∈ [x0, x0+L]` lies within one mesh step of
a grid point `x0 + i·mesh` with `i ≤ ⌈L/mesh⌉₊`. -/
theorem mesh_cover (x0 L mesh x : ℝ) (hmesh : 0 < mesh) (hx0 : x0 ≤ x)
    (hx : x ≤ x0 + L) :
    ∃ i : ℕ, i ≤ ⌈L / mesh⌉₊ ∧ |x - (x0 + (i : ℝ) * mesh)| ≤ mesh := by
  set t := (x - x0) / mesh with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hmesh.le
  have htL : t ≤ L / mesh := div_le_div_of_nonneg_right (by linarith) hmesh.le
  have hi1 : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0
  have hi2 : t < ((⌊t⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one t
  refine ⟨⌊t⌋₊, ?_, ?_⟩
  · have hle : ((⌊t⌋₊ : ℕ) : ℝ) ≤ ((⌈L / mesh⌉₊ : ℕ) : ℝ) :=
      le_trans hi1 (le_trans htL (Nat.le_ceil _))
    exact_mod_cast hle
  · have hxmesh : x - x0 = t * mesh := by
      rw [ht]; field_simp
    have key : x - (x0 + ((⌊t⌋₊ : ℕ) : ℝ) * mesh) = (t - ((⌊t⌋₊ : ℕ) : ℝ)) * mesh := by
      have : x - (x0 + ((⌊t⌋₊ : ℕ) : ℝ) * mesh) = (x - x0) - ((⌊t⌋₊ : ℕ) : ℝ) * mesh := by ring
      rw [this, hxmesh]; ring
    rw [key, abs_of_nonneg (mul_nonneg (by linarith) hmesh.le)]
    exact mul_le_of_le_one_left hmesh.le (by linarith)

/-! ## Conjugation symmetry, integrability and generic Chebyshev union bound -/

theorem Gfull_conj (μ : Measure ℝ) (w : ℂ) : Gfull μ (starRingEnd ℂ w) = starRingEnd ℂ (Gfull μ w) := by
  unfold Gfull
  rw [← integral_conj]
  congr 1
  funext q
  simp only [map_div₀, map_one, map_sub, Complex.conj_ofReal]

theorem GN_conj {N : ℕ} (q : Fin N → ℝ) (w : ℂ) :
    GN q (starRingEnd ℂ w) = starRingEnd ℂ (GN q w) := by
  unfold GN
  simp only [map_mul, map_sum, map_div₀, map_one, map_sub, Complex.conj_ofReal, map_natCast]

/-- The error at the conjugate point has the same modulus. -/
theorem err_conj {N : ℕ} (μ : Measure ℝ) (q : Fin N → ℝ) (w : ℂ) :
    ‖Gfull μ (starRingEnd ℂ w) - GN q (starRingEnd ℂ w)‖ = ‖Gfull μ w - GN q w‖ := by
  rw [Gfull_conj, GN_conj, ← map_sub, Complex.norm_conj]

/-- Integrability of the squared error at any point of nonzero imaginary part (roots measurable). -/
theorem sq_integrable_of_im_ne {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (hN : 0 < N) (q : Ω → Fin N → ℝ) (hq : Measurable q)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (w : ℂ) (hw : w.im ≠ 0) :
    Integrable (fun ω => ‖Gfull μ w - GN (q ω) w‖ ^ 2) P := by
  rcases lt_or_gt_of_ne hw with hneg | hpos
  · have h := node_err_sq_integrable P hN q hq μ (starRingEnd ℂ w)
      (by rw [Complex.conj_im]; linarith)
    refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
    show ‖Gfull μ (starRingEnd ℂ w) - GN (q ω) (starRingEnd ℂ w)‖ ^ 2
      = ‖Gfull μ w - GN (q ω) w‖ ^ 2
    rw [err_conj]
  · exact node_err_sq_integrable P hN q hq μ w hpos

/-- Generic Chebyshev union bound over a finite index set. -/
theorem union_chebyshev {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (err : Ω → ι → ℝ) (ε : ℝ) (hε : 0 < ε)
    (V : ι → ℝ) (hsq : ∀ i, Integrable (fun ω => err ω i ^ 2) P)
    (hvar : ∀ i, ∫ ω, err ω i ^ 2 ∂P ≤ V i) :
    P.real (⋃ i ∈ (Finset.univ : Finset ι), {ω | ε < err ω i}) ≤ (∑ i, V i) / ε ^ 2 := by
  have hpos : 0 < ε ^ 2 := by positivity
  have hcheb : ∀ i : ι, P.real {ω | ε < err ω i} ≤ V i / ε ^ 2 := by
    intro i
    have hnn : 0 ≤ᵐ[P] (fun ω => err ω i ^ 2) := Filter.Eventually.of_forall fun ω => sq_nonneg _
    have hmk := mul_meas_ge_le_integral_of_nonneg hnn (hsq i) (ε ^ 2)
    have hsub : P.real {ω | ε < err ω i} ≤ P.real {x | ε ^ 2 ≤ err x i ^ 2} := by
      refine measureReal_mono (fun ω hω => ?_) (measure_ne_top P _)
      have hεω : ε < err ω i := hω
      show ε ^ 2 ≤ err ω i ^ 2
      nlinarith
    have h2 : P.real {ω | ε < err ω i} ≤ (∫ ω, err ω i ^ 2 ∂P) / ε ^ 2 := by
      rw [le_div_iff₀ hpos]
      calc P.real {ω | ε < err ω i} * ε ^ 2 ≤ P.real {x | ε ^ 2 ≤ err x i ^ 2} * ε ^ 2 :=
            mul_le_mul_of_nonneg_right hsub hpos.le
        _ = ε ^ 2 * P.real {x | ε ^ 2 ≤ err x i ^ 2} := mul_comm _ _
        _ ≤ ∫ ω, err ω i ^ 2 ∂P := hmk
    exact h2.trans (div_le_div_of_nonneg_right (hvar i) hpos.le)
  have hunion := measureReal_biUnion_finset_le (μ := P) (Finset.univ : Finset ι)
    (fun i => {ω | ε < err ω i})
  calc P.real (⋃ i ∈ (Finset.univ : Finset ι), {ω | ε < err ω i})
      ≤ ∑ i ∈ (Finset.univ : Finset ι), P.real {ω | ε < err ω i} := hunion
    _ ≤ ∑ i ∈ (Finset.univ : Finset ι), V i / ε ^ 2 := Finset.sum_le_sum fun i _ => hcheb i
    _ = (∑ i, V i) / ε ^ 2 := (Finset.sum_div _ _ _).symm


/-! ## The PROP-017 event `E_N` and its complement -/

/-- Heights of the four horizontal segments, `±(h-2ρ)` and `±(h+2ρ)`. -/
def gridHeight (h ρ : ℝ) : Fin 4 → ℝ := ![h - 2 * ρ, -(h - 2 * ρ), h + 2 * ρ, -(h + 2 * ρ)]

/-- The horizontal segments `[-a-2ρ, a+2ρ] × {±(h-2ρ), ±(h+2ρ)}`. -/
def segSet (a ρ h : ℝ) : Set ℂ :=
  {z | z.re ∈ Icc (-a - 2 * ρ) (a + 2 * ρ) ∧ ∃ j : Fin 4, z.im = gridHeight h ρ j}

/-- Mesh of the grid on the segments, `ε (h-2ρ)² / 4`. -/
def gridMesh (ε h ρ : ℝ) : ℝ := ε * (h - 2 * ρ) ^ 2 / 4

/-- Number of mesh steps needed to cover the segment length `2a + 4ρ`. -/
def gridN (ε h ρ a : ℝ) : ℕ := ⌈(2 * a + 4 * ρ) / gridMesh ε h ρ⌉₊

/-- Grid index: height index and column index. -/
abbrev GridIdx (ε h ρ a : ℝ) := Fin 4 × Fin (gridN ε h ρ a + 1)

/-- Grid point `(-a-2ρ + i·mesh) + i·height_j`. -/
def gridPt (ε h ρ a : ℝ) (p : GridIdx ε h ρ a) : ℂ :=
  ⟨-a - 2 * ρ + ((p.2 : ℕ) : ℝ) * gridMesh ε h ρ, gridHeight h ρ p.1⟩

/-- The error `|G − G_N|(z)` at a point. -/
def fErr (μ : Measure ℝ) {Ω : Type*} {N : ℕ} (q : Ω → Fin N → ℝ) (ω : Ω) (z : ℂ) : ℝ :=
  ‖Gfull μ z - GN (q ω) z‖

/-- The node error `|G − G_N|(x + i(η₀+1+k))` for the real centre `x` (`x = ±a`). -/
def nodeErr (μ : Measure ℝ) {Ω : Type*} {N : ℕ} (q : Ω → Fin N → ℝ) (x η0 : ℝ) (m : ℕ) (ω : Ω)
    (k : Fin (m + 1)) : ℝ :=
  ‖Gfull μ ((x : ℂ) + srcNodes η0 m k) - GN (q ω) ((x : ℂ) + srcNodes η0 m k)‖

/-- The PROP-017 event `E_N`: all roots in `[-R,R]`, both cuts' node errors at most `ε`, and
`|G − G_N| ≤ ε` on the horizontal segments (source `Q7A:prop:packet`). -/
def EN (μ : Measure ℝ) {Ω : Type*} {N : ℕ} (q : Ω → Fin N → ℝ) (R a ρ h η0 ε : ℝ) (m : ℕ) :
    Set Ω :=
  {ω | (∀ j, |q ω j| ≤ R) ∧ (∀ k : Fin (m + 1), nodeErr μ q a η0 m ω k ≤ ε) ∧
    (∀ k : Fin (m + 1), nodeErr μ q (-a) η0 m ω k ≤ ε) ∧ ∀ z ∈ segSet a ρ h, fErr μ q ω z ≤ ε}

theorem gridHeight_abs_ge (h ρ : ℝ) (hρ : 0 ≤ ρ) (j : Fin 4) :
    h - 2 * ρ ≤ |gridHeight h ρ j| := by
  fin_cases j
  · show h - 2 * ρ ≤ |h - 2 * ρ|
    exact le_abs_self _
  · show h - 2 * ρ ≤ |-(h - 2 * ρ)|
    rw [abs_neg]
    exact le_abs_self _
  · show h - 2 * ρ ≤ |h + 2 * ρ|
    exact le_trans (by linarith) (le_abs_self _)
  · show h - 2 * ρ ≤ |-(h + 2 * ρ)|
    rw [abs_neg]
    exact le_trans (by linarith) (le_abs_self _)

/-- On the grid, `|G − G_N| ≤ ε/2` everywhere implies `|G − G_N| ≤ ε` on the segments. -/
theorem grid_implies_seg (μ : Measure ℝ) [IsProbabilityMeasure μ] {Ω : Type*} {N : ℕ} (hN : 0 < N)
    (q : Ω → Fin N → ℝ) (ω : Ω) (a ρ h ε : ℝ) (hρ : 0 ≤ ρ) (hy : 0 < h - 2 * ρ) (hε : 0 < ε)
    (hgrid : ∀ p : GridIdx ε h ρ a, fErr μ q ω (gridPt ε h ρ a p) ≤ ε / 2) :
    ∀ z ∈ segSet a ρ h, fErr μ q ω z ≤ ε := by
  rintro z ⟨hre, j, him⟩
  have hmesh : 0 < gridMesh ε h ρ := by unfold gridMesh; positivity
  have hL : 0 ≤ 2 * a + 4 * ρ := by linarith [hre.1, hre.2]
  obtain ⟨i, hi, hdist⟩ := mesh_cover (-a - 2 * ρ) (2 * a + 4 * ρ) (gridMesh ε h ρ) z.re hmesh
    hre.1 (by linarith [hre.2])
  have hi' : i < gridN ε h ρ a + 1 := Nat.lt_succ_of_le hi
  let g : ℂ := gridPt ε h ρ a (j, ⟨i, hi'⟩)
  have hgim : g.im = z.im := by
    simp only [g, gridPt, him]
  have hgre : g.re = -a - 2 * ρ + (i : ℝ) * gridMesh ε h ρ := rfl
  have hzg : ‖z - g‖ ≤ gridMesh ε h ρ := by
    have h1 := Complex.norm_le_abs_re_add_abs_im (z - g)
    simp only [Complex.sub_re, Complex.sub_im, hgim, sub_self, abs_zero, add_zero] at h1
    rw [hgre] at h1
    have : |z.re - (-a - 2 * ρ + (i : ℝ) * gridMesh ε h ρ)| ≤ gridMesh ε h ρ := hdist
    linarith
  have hgim_abs : h - 2 * ρ ≤ |g.im| := by
    rw [hgim, him]; exact gridHeight_abs_ge h ρ hρ j
  have hzim_abs : h - 2 * ρ ≤ |z.im| := by
    rw [him]; exact gridHeight_abs_ge h ρ hρ j
  have hlip := diff_lipschitz μ hN (q ω) z g (h - 2 * ρ) hy hzim_abs hgim_abs
  have hbound : 2 * ‖z - g‖ / ((h - 2 * ρ) * (h - 2 * ρ)) ≤ ε / 2 := by
    have hyy : 0 < (h - 2 * ρ) * (h - 2 * ρ) := mul_pos hy hy
    have hmesh_eq : 2 * gridMesh ε h ρ / ((h - 2 * ρ) * (h - 2 * ρ)) = ε / 2 := by
      unfold gridMesh
      field_simp
      ring
    calc 2 * ‖z - g‖ / ((h - 2 * ρ) * (h - 2 * ρ))
        ≤ 2 * gridMesh ε h ρ / ((h - 2 * ρ) * (h - 2 * ρ)) :=
          div_le_div_of_nonneg_right (by linarith) hyy.le
      _ = ε / 2 := hmesh_eq
  have hg := hgrid (j, ⟨i, hi'⟩)
  have hgrid_eq : g = gridPt ε h ρ a (j, ⟨i, hi'⟩) := rfl
  unfold fErr at hg ⊢
  rw [← hgrid_eq] at hg
  have htri := norm_sub_norm_le (Gfull μ z - GN (q ω) z) (Gfull μ g - GN (q ω) g)
  linarith [hlip, hbound, hg]

/-! ## Probability bounds for PROP-017 -/

/-- Variance hypothesis at any height `|t| ≥ η₀`, both signs (conjugation reflection). -/
theorem hms_all {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (q : Ω → Fin N → ℝ) (μ : Measure ℝ) (η0 Cms : ℝ)
    (hms : ∀ x y : ℝ, η0 ≤ y → ∫ ω, ‖Gfull μ ((x : ℂ) + (y : ℂ) * Complex.I)
        - GN (q ω) ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 ∂P ≤ Cms / ((N : ℝ) * y ^ 2))
    (x t : ℝ) (ht : η0 ≤ |t|) :
    ∫ ω, ‖Gfull μ ((x : ℂ) + (t : ℂ) * Complex.I) - GN (q ω) ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 ∂P
      ≤ Cms / ((N : ℝ) * t ^ 2) := by
  rcases le_or_gt 0 t with ht0 | htneg
  · rw [abs_of_nonneg ht0] at ht
    exact hms x t ht
  · have hconj : ((x : ℂ) + (t : ℂ) * Complex.I)
        = starRingEnd ℂ ((x : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) := by
      apply Complex.ext <;> simp
    have hcongr : (fun ω => ‖Gfull μ ((x : ℂ) + (t : ℂ) * Complex.I)
          - GN (q ω) ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
        = fun ω => ‖Gfull μ ((x : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)
          - GN (q ω) ((x : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖ ^ 2 := by
      funext ω
      rw [hconj, err_conj]
    have hneg : η0 ≤ -t := by
      rw [abs_of_neg htneg] at ht
      exact ht
    have h := hms x (-t) hneg
    have hsq : (-t) ^ 2 = t ^ 2 := by ring
    rw [hcongr]
    rw [hsq] at h
    exact h

/-- Node-maximum union bound for one cut centre `x` (source RHS node errors). -/
theorem nodes_union_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (hN : 0 < N) (q : Ω → Fin N → ℝ) (hq : Measurable q) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (x η0 Cms ε : ℝ) (m : ℕ) (hη0 : 0 < η0) (hε : 0 < ε)
    (hms : ∀ x y : ℝ, η0 ≤ y → ∫ ω, ‖Gfull μ ((x : ℂ) + (y : ℂ) * Complex.I)
        - GN (q ω) ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 ∂P ≤ Cms / ((N : ℝ) * y ^ 2)) :
    P.real (⋃ k ∈ (Finset.univ : Finset (Fin (m + 1))), {ω | ε < nodeErr μ q x η0 m ω k})
      ≤ (∑ k : Fin (m + 1), Cms / ((N : ℝ) * (η0 + 1 + ((k : ℕ) : ℝ)) ^ 2)) / ε ^ 2 := by
  have hpos : ∀ k : Fin (m + 1), (0 : ℝ) < η0 + 1 + ((k : ℕ) : ℝ) := fun k => by
    have := (Nat.cast_nonneg (k : ℕ) : (0 : ℝ) ≤ ((k : ℕ) : ℝ))
    linarith
  refine union_chebyshev P (fun ω k => nodeErr μ q x η0 m ω k) ε hε
    (fun k => Cms / ((N : ℝ) * (η0 + 1 + ((k : ℕ) : ℝ)) ^ 2)) ?_ ?_
  · intro k
    have hw : ((x : ℂ) + srcNodes η0 m k).im ≠ 0 := by
      rw [Complex.add_im, Complex.ofReal_im, zero_add, srcNodes_im]
      exact (hpos k).ne'
    exact sq_integrable_of_im_ne P hN q hq μ _ hw
  · intro k
    have ht : η0 ≤ |η0 + 1 + ((k : ℕ) : ℝ)| := by
      rw [abs_of_pos (hpos k)]
      linarith [(Nat.cast_nonneg (k : ℕ) : (0 : ℝ) ≤ ((k : ℕ) : ℝ))]
    exact hms_all P q μ η0 Cms hms x _ ht

/-- Grid union bound: the horizontal-segment grid errors exceed `ε/2` with small probability. -/
theorem grid_union_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (hN : 0 < N) (q : Ω → Fin N → ℝ) (hq : Measurable q) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a ρ h ε η0 Cms : ℝ) (hρ : 0 ≤ ρ) (hη0 : 0 < η0) (hyη : η0 ≤ h - 2 * ρ) (hCms : 0 ≤ Cms)
    (hε : 0 < ε)
    (hms : ∀ x y : ℝ, η0 ≤ y → ∫ ω, ‖Gfull μ ((x : ℂ) + (y : ℂ) * Complex.I)
        - GN (q ω) ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 ∂P ≤ Cms / ((N : ℝ) * y ^ 2)) :
    P.real (⋃ p ∈ (Finset.univ : Finset (GridIdx ε h ρ a)), {ω | ε / 2 < fErr μ q ω (gridPt ε h ρ a p)})
      ≤ (∑ _p : GridIdx ε h ρ a, Cms / ((N : ℝ) * (h - 2 * ρ) ^ 2)) / (ε / 2) ^ 2 := by
  have hy : 0 < h - 2 * ρ := lt_of_lt_of_le hη0 hyη
  have hheight : ∀ j : Fin 4, h - 2 * ρ ≤ |gridHeight h ρ j| := gridHeight_abs_ge h ρ hρ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  refine union_chebyshev P (fun ω p => fErr μ q ω (gridPt ε h ρ a p)) (ε / 2) (by positivity)
    (fun _ => Cms / ((N : ℝ) * (h - 2 * ρ) ^ 2)) ?_ ?_
  · intro p
    have hw : (gridPt ε h ρ a p).im ≠ 0 := by
      show gridHeight h ρ p.1 ≠ 0
      intro h0
      have := hheight p.1
      rw [h0, abs_zero] at this
      linarith
    exact sq_integrable_of_im_ne P hN q hq μ _ hw
  · intro p
    set xi : ℝ := -a - 2 * ρ + ((p.2 : ℕ) : ℝ) * gridMesh ε h ρ with hxi
    set t : ℝ := gridHeight h ρ p.1 with ht
    have hg : gridPt ε h ρ a p = (xi : ℂ) + (t : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [gridPt, hxi, ht]
    have hht : η0 ≤ |t| := le_trans hyη (hheight p.1)
    have h1 := hms_all P q μ η0 Cms hms xi t hht
    have hpos : (0 : ℝ) < (N : ℝ) * (h - 2 * ρ) ^ 2 := by positivity
    have hsqle : (N : ℝ) * (h - 2 * ρ) ^ 2 ≤ (N : ℝ) * t ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hNpos.le
      have h2 := hheight p.1
      rw [← ht] at h2
      have h3 : (h - 2 * ρ) ^ 2 ≤ |t| ^ 2 := pow_le_pow_left₀ hy.le h2 2
      rwa [sq_abs] at h3
    calc ∫ ω, fErr μ q ω (gridPt ε h ρ a p) ^ 2 ∂P
        = ∫ ω, ‖Gfull μ ((xi : ℂ) + (t : ℂ) * Complex.I)
            - GN (q ω) ((xi : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 ∂P := by
          congr 1
          funext ω
          unfold fErr
          rw [hg]
      _ ≤ Cms / ((N : ℝ) * t ^ 2) := h1
      _ ≤ Cms / ((N : ℝ) * (h - 2 * ρ) ^ 2) := div_le_div_of_nonneg_left hCms hpos hsqle

/-- Event inclusion: the complement of `E_N` lies in the union of the four bad events. -/
theorem EN_compl_subset {Ω : Type*} {N : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] (hN : 0 < N)
    (q : Ω → Fin N → ℝ) (R a ρ h η0 ε : ℝ) (m : ℕ) (hρ : 0 ≤ ρ) (hy : 0 < h - 2 * ρ) (hε : 0 < ε) :
    (EN μ q R a ρ h η0 ε m)ᶜ ⊆
      outside q R ∪ (⋃ k ∈ (Finset.univ : Finset (Fin (m + 1))), {ω | ε < nodeErr μ q a η0 m ω k})
        ∪ (⋃ k ∈ (Finset.univ : Finset (Fin (m + 1))), {ω | ε < nodeErr μ q (-a) η0 m ω k})
        ∪ (⋃ p ∈ (Finset.univ : Finset (GridIdx ε h ρ a)), {ω | ε / 2 < fErr μ q ω (gridPt ε h ρ a p)}) := by
  intro ω hω
  by_contra hcon
  apply hω
  have hA : ∀ j, |q ω j| ≤ R := by
    intro j
    by_contra hj
    exact hcon (Or.inl (Or.inl (Or.inl ⟨j, not_le.1 hj⟩)))
  have hB : ∀ k : Fin (m + 1), nodeErr μ q a η0 m ω k ≤ ε := by
    intro k
    by_contra hk
    exact hcon (Or.inl (Or.inl (Or.inr (Set.mem_iUnion₂.2 ⟨k, Finset.mem_univ k, not_le.1 hk⟩))))
  have hC : ∀ k : Fin (m + 1), nodeErr μ q (-a) η0 m ω k ≤ ε := by
    intro k
    by_contra hk
    exact hcon (Or.inl (Or.inr (Set.mem_iUnion₂.2 ⟨k, Finset.mem_univ k, not_le.1 hk⟩)))
  have hD : ∀ p : GridIdx ε h ρ a, fErr μ q ω (gridPt ε h ρ a p) ≤ ε / 2 := by
    intro p
    by_contra hp
    exact hcon (Or.inr (Set.mem_iUnion₂.2 ⟨p, Finset.mem_univ p, not_le.1 hp⟩))
  exact ⟨hA, hB, hC, grid_implies_seg μ hN q ω a ρ h ε hρ hy hε hD⟩

/-- The grid count: `n + 1 ≤ A₁(1+a)/ε` with `A₁ = (8+16ρ)/(h-2ρ)² + 2`. -/
theorem gridN_bound (ε h ρ a : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 ≤ ρ) (ha : 0 ≤ a)
    (hy : 0 < h - 2 * ρ) :
    ((gridN ε h ρ a : ℕ) : ℝ) + 1 ≤ ((8 + 16 * ρ) / (h - 2 * ρ) ^ 2 + 2) * (1 + a) / ε := by
  have hmesh : 0 < gridMesh ε h ρ := by unfold gridMesh; positivity
  have ht0 : 0 ≤ (2 * a + 4 * ρ) / gridMesh ε h ρ := div_nonneg (by linarith) hmesh.le
  have hceil : ((gridN ε h ρ a : ℕ) : ℝ) < (2 * a + 4 * ρ) / gridMesh ε h ρ + 1 :=
    Nat.ceil_lt_add_one ht0
  have hT : (2 * a + 4 * ρ) / gridMesh ε h ρ = (8 * a + 16 * ρ) / (ε * (h - 2 * ρ) ^ 2) := by
    unfold gridMesh
    field_simp
    ring
  have hT2 : (8 * a + 16 * ρ) / (ε * (h - 2 * ρ) ^ 2) ≤ (8 + 16 * ρ) * (1 + a) / (ε * (h - 2 * ρ) ^ 2) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have hone : (2 : ℝ) ≤ 2 * (1 + a) / ε := by
    rw [le_div_iff₀ hε]
    nlinarith
  have hsplit : ((8 + 16 * ρ) * (1 + a) / (ε * (h - 2 * ρ) ^ 2)) + 2 * (1 + a) / ε
      = ((8 + 16 * ρ) / (h - 2 * ρ) ^ 2 + 2) * (1 + a) / ε := by
    field_simp
  have hfin : ((gridN ε h ρ a : ℕ) : ℝ) + 1 ≤ ((8 + 16 * ρ) * (1 + a) / (ε * (h - 2 * ρ) ^ 2))
      + 2 * (1 + a) / ε := by
    have hone' : (1 : ℝ) ≤ (1 + a) / ε := by
      rw [le_div_iff₀ hε]; nlinarith
    linarith [hceil, hT, hT2, hone, hone']
  rw [← hsplit]
  linarith [hfin]

/-! ## The PROP-017 bound `P(E_N^c) ≤ C_p N R^{-2p} + D_p R^{-1} + C_b (1+a)/(N ε³)` -/

/-- `Kn = ∑_k C_ms/(η₀+1+k)²` (node variance sum, without `N`). -/
def prop017Kn (η0 Cms : ℝ) (m : ℕ) : ℝ :=
  ∑ k : Fin (m + 1), Cms / (η0 + 1 + ((k : ℕ) : ℝ)) ^ 2

/-- The explicit constant `C_b = 2 Kn + 16 A₁ C_ms/(h-2ρ)²`, `A₁ = (8+16ρ)/(h-2ρ)² + 2`. -/
def prop017Cb (η0 h ρ Cms : ℝ) (m : ℕ) : ℝ :=
  2 * prop017Kn η0 Cms m + 16 * ((8 + 16 * ρ) / (h - 2 * ρ) ^ 2 + 2) * Cms / (h - 2 * ρ) ^ 2

theorem prop017_arith (N ε η0 h ρ a Cms : ℝ) (m : ℕ) (n : ℝ) (hN : 0 < N) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (ha : 0 ≤ a) (hy : 0 < h - 2 * ρ) (hCms : 0 ≤ Cms)
    (hKn : 0 ≤ prop017Kn η0 Cms m) (hn0 : 0 ≤ n)
    (hn : n ≤ ((8 + 16 * ρ) / (h - 2 * ρ) ^ 2 + 2) * (1 + a) / ε - 1) :
    2 * ((prop017Kn η0 Cms m / N) / ε ^ 2)
        + 4 * (n + 1) * (Cms / (N * (h - 2 * ρ) ^ 2)) / (ε / 2) ^ 2
      ≤ prop017Cb η0 h ρ Cms m * (1 + a) / (N * ε ^ 3) := by
  set K := prop017Kn η0 Cms m with hK
  set A1 := (8 + 16 * ρ) / (h - 2 * ρ) ^ 2 + 2 with hA1
  have hy2 : 0 < (h - 2 * ρ) ^ 2 := by positivity
  have hN0 : N ≠ 0 := hN.ne'
  have hε0 : ε ≠ 0 := hε.ne'
  have hd : 0 ≤ (1 + a) - ε := by linarith
  -- term 1: 2K/(Nε²) ≤ 2K(1+a)/(Nε³)
  have e1 : 2 * ((K / N) / ε ^ 2) ≤ 2 * K * (1 + a) / (N * ε ^ 3) := by
    rw [div_div, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have h0 : 0 ≤ K * N * ε ^ 2 * ((1 + a) - ε) :=
      mul_nonneg (mul_nonneg (mul_nonneg hKn hN.le) (sq_nonneg ε)) hd
    nlinarith [h0]
  -- term 2: grid
  have e2 : 4 * (n + 1) * (Cms / (N * (h - 2 * ρ) ^ 2)) / (ε / 2) ^ 2
      = (16 * Cms / (N * (h - 2 * ρ) ^ 2 * ε ^ 2)) * (n + 1) := by
    field_simp
    ring
  have hpos2 : 0 ≤ 16 * Cms / (N * (h - 2 * ρ) ^ 2 * ε ^ 2) := by positivity
  have e3 : (16 * Cms / (N * (h - 2 * ρ) ^ 2 * ε ^ 2)) * (n + 1)
      ≤ (16 * Cms / (N * (h - 2 * ρ) ^ 2 * ε ^ 2)) * (A1 * (1 + a) / ε) := by
    apply mul_le_mul_of_nonneg_left _ hpos2
    linarith
  have e4 : (16 * Cms / (N * (h - 2 * ρ) ^ 2 * ε ^ 2)) * (A1 * (1 + a) / ε)
      = 16 * A1 * Cms / (h - 2 * ρ) ^ 2 * (1 + a) / (N * ε ^ 3) := by
    field_simp
  have hfinal : prop017Cb η0 h ρ Cms m * (1 + a) / (N * ε ^ 3)
      = 2 * K * (1 + a) / (N * ε ^ 3) + 16 * A1 * Cms / (h - 2 * ρ) ^ 2 * (1 + a) / (N * ε ^ 3) := by
    unfold prop017Cb
    rw [← hK, ← hA1]
    ring
  have hsplit : 4 * (n + 1) * (Cms / (N * (h - 2 * ρ) ^ 2)) / (ε / 2) ^ 2
      ≤ 16 * A1 * Cms / (h - 2 * ρ) ^ 2 * (1 + a) / (N * ε ^ 3) := by
    rw [e2]
    linarith [e3, e4]
  have hleft : 2 * ((K / N) / ε ^ 2) + 4 * (n + 1) * (Cms / (N * (h - 2 * ρ) ^ 2)) / (ε / 2) ^ 2
      ≤ 2 * K * (1 + a) / (N * ε ^ 3) + 16 * A1 * Cms / (h - 2 * ρ) ^ 2 * (1 + a) / (N * ε ^ 3) := by
    linarith [e1, hsplit]
  rw [hfinal]
  exact hleft

/-- **PROP-017 probability bound, source `Q7A:eq:bad`.** With `E_N` the source event (all roots in
`[-R,R]`, both cuts' node errors `≤ ε`, and `|G−G_N| ≤ ε` on the horizontal segments),
`P(E_N^c) ≤ C_p N R^{-2p} + D_p R^{-1} + C_b (1+a)/(N ε³)`, where `C_p, D_p` are the source tail
constants (`Q7A:eq:tail`, hypothesis `hTail`), the variance constant `C_ms` is the source
`Q7A:eq:ms` constant (hypothesis `hms`), and `C_b = prop017Cb` (explicit). -/
theorem prop017_bad {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (hN : 0 < N) (q : Ω → Fin N → ℝ) (hq : Measurable q)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m : ℕ) (η0 h ρ a R ε C D R0 Cms : ℝ) (p : ℕ)
    (hCms : 0 ≤ Cms) (hη0 : 0 < η0) (hρ : 0 ≤ ρ) (hyη : η0 ≤ h - 2 * ρ) (ha : 0 ≤ a)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hRpos : 0 < R) (hR0 : R0 ≤ R)
    (hTail : ∀ R' : ℝ, R0 ≤ R' → 0 < R' →
      ∫ ω, tailFraction q R' ω ∂P ≤ C * (1 / R' ^ (2 * p)) + D / ((N : ℝ) * R'))
    (hms : ∀ x y : ℝ, η0 ≤ y → ∫ ω, ‖Gfull μ ((x : ℂ) + (y : ℂ) * Complex.I)
        - GN (q ω) ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 ∂P ≤ Cms / ((N : ℝ) * y ^ 2)) :
    P.real (EN μ q R a ρ h η0 ε m)ᶜ
      ≤ (N : ℝ) * (C * (1 / R ^ (2 * p))) + D / R
        + prop017Cb η0 h ρ Cms m * (1 + a) / ((N : ℝ) * ε ^ 3) := by
  have hy : 0 < h - 2 * ρ := lt_of_lt_of_le hη0 hyη
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  -- inclusion of the complement
  have hsub := EN_compl_subset μ hN q R a ρ h η0 ε m hρ hy hε
  have h1 := measureReal_mono (μ := P) hsub (measure_ne_top P _)
  have h2 := measureReal_union_le (μ := P)
    (outside q R ∪ (⋃ k ∈ (Finset.univ : Finset (Fin (m + 1))), {ω | ε < nodeErr μ q a η0 m ω k})
      ∪ (⋃ k ∈ (Finset.univ : Finset (Fin (m + 1))), {ω | ε < nodeErr μ q (-a) η0 m ω k}))
    (⋃ p ∈ (Finset.univ : Finset (GridIdx ε h ρ a)), {ω | ε / 2 < fErr μ q ω (gridPt ε h ρ a p)})
  have h3 := measureReal_union_le (μ := P)
    (outside q R ∪ (⋃ k ∈ (Finset.univ : Finset (Fin (m + 1))), {ω | ε < nodeErr μ q a η0 m ω k}))
    (⋃ k ∈ (Finset.univ : Finset (Fin (m + 1))), {ω | ε < nodeErr μ q (-a) η0 m ω k})
  have h4 := measureReal_union_le (μ := P)
    (outside q R)
    (⋃ k ∈ (Finset.univ : Finset (Fin (m + 1))), {ω | ε < nodeErr μ q a η0 m ω k})
  -- root part
  have hroot := root_event_bound hN P q hq p C D R0 R hR0 hRpos hTail
  -- node parts (both cuts)
  have hnodeP := nodes_union_bound P hN q hq μ a η0 Cms ε m hη0 hε hms
  have hnodeM := nodes_union_bound P hN q hq μ (-a) η0 Cms ε m hη0 hε hms
  -- grid part
  have hgrid := grid_union_bound P hN q hq μ a ρ h ε η0 Cms hρ hη0 hyη hCms hε hms
  -- simplify node sums: ∑ Cms/(N t²) = Kn / N
  have hnodesum : ∑ k : Fin (m + 1), Cms / ((N : ℝ) * (η0 + 1 + ((k : ℕ) : ℝ)) ^ 2)
      = prop017Kn η0 Cms m / (N : ℝ) := by
    unfold prop017Kn
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [div_div, mul_comm]
  -- simplify grid sum: card(GridIdx) = 4 (n+1)
  have hgridsum : (∑ _p : GridIdx ε h ρ a, Cms / ((N : ℝ) * (h - 2 * ρ) ^ 2))
      = 4 * ((gridN ε h ρ a : ℝ) + 1) * (Cms / ((N : ℝ) * (h - 2 * ρ) ^ 2)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    ring
  rw [hnodesum] at hnodeP hnodeM
  rw [hgridsum] at hgrid
  -- the arithmetic bound
  have hKn : 0 ≤ prop017Kn η0 Cms m := by
    unfold prop017Kn
    exact Finset.sum_nonneg fun k _ => div_nonneg hCms (by positivity)
  have hn := gridN_bound ε h ρ a hε hε1 hρ ha hy
  have harith := prop017_arith (N : ℝ) ε η0 h ρ a Cms m ((gridN ε h ρ a : ℕ) : ℝ) hNpos hε hε1 ha
    hy hCms hKn (Nat.cast_nonneg _) (by linarith [hn])
  have hfin : (N : ℝ) * (C * (1 / R ^ (2 * p))) + D / R
      + (2 * ((prop017Kn η0 Cms m / (N : ℝ)) / ε ^ 2)
          + 4 * ((gridN ε h ρ a : ℝ) + 1) * (Cms / ((N : ℝ) * (h - 2 * ρ) ^ 2)) / (ε / 2) ^ 2)
      ≤ (N : ℝ) * (C * (1 / R ^ (2 * p))) + D / R
        + prop017Cb η0 h ρ Cms m * (1 + a) / ((N : ℝ) * ε ^ 3) := by
    linarith [harith]
  calc P.real (EN μ q R a ρ h η0 ε m)ᶜ
      ≤ P.real (outside q R ∪ (⋃ k ∈ (Finset.univ : Finset (Fin (m + 1))), {ω | ε < nodeErr μ q a η0 m ω k})
          ∪ (⋃ k ∈ (Finset.univ : Finset (Fin (m + 1))), {ω | ε < nodeErr μ q (-a) η0 m ω k})
          ∪ (⋃ p ∈ (Finset.univ : Finset (GridIdx ε h ρ a)), {ω | ε / 2 < fErr μ q ω (gridPt ε h ρ a p)})) := h1
    _ ≤ P.real (outside q R ∪ (⋃ k ∈ (Finset.univ : Finset (Fin (m + 1))), {ω | ε < nodeErr μ q a η0 m ω k})
          ∪ (⋃ k ∈ (Finset.univ : Finset (Fin (m + 1))), {ω | ε < nodeErr μ q (-a) η0 m ω k}))
          + P.real (⋃ p ∈ (Finset.univ : Finset (GridIdx ε h ρ a)), {ω | ε / 2 < fErr μ q ω (gridPt ε h ρ a p)}) := h2
    _ ≤ P.real (outside q R ∪ (⋃ k ∈ (Finset.univ : Finset (Fin (m + 1))), {ω | ε < nodeErr μ q a η0 m ω k}))
          + P.real (⋃ k ∈ (Finset.univ : Finset (Fin (m + 1))), {ω | ε < nodeErr μ q (-a) η0 m ω k})
          + P.real (⋃ p ∈ (Finset.univ : Finset (GridIdx ε h ρ a)), {ω | ε / 2 < fErr μ q ω (gridPt ε h ρ a p)}) := by
        linarith [h3]
    _ ≤ P.real (outside q R) + P.real (⋃ k ∈ (Finset.univ : Finset (Fin (m + 1))), {ω | ε < nodeErr μ q a η0 m ω k})
          + P.real (⋃ k ∈ (Finset.univ : Finset (Fin (m + 1))), {ω | ε < nodeErr μ q (-a) η0 m ω k})
          + P.real (⋃ p ∈ (Finset.univ : Finset (GridIdx ε h ρ a)), {ω | ε / 2 < fErr μ q ω (gridPt ε h ρ a p)}) := by
        linarith [h4]
    _ ≤ (N : ℝ) * (C * (1 / R ^ (2 * p))) + D / R
          + (2 * ((prop017Kn η0 Cms m / (N : ℝ)) / ε ^ 2)
            + 4 * ((gridN ε h ρ a : ℝ) + 1) * (Cms / ((N : ℝ) * (h - 2 * ρ) ^ 2)) / (ε / 2) ^ 2) := by
        linarith [hroot, hnodeP, hnodeM, hgrid]
    _ ≤ (N : ℝ) * (C * (1 / R ^ (2 * p))) + D / R
        + prop017Cb η0 h ρ Cms m * (1 + a) / ((N : ℝ) * ε ^ 3) := hfin

end

end QuantumNLS.RootEvent






/-! Axiom check for the headline declarations (compile-log evidence). -/
#print axioms QuantumNLS.RootEvent.root_event_bound
#print axioms QuantumNLS.RootEvent.nodes_union_bound
#print axioms QuantumNLS.RootEvent.grid_union_bound
#print axioms QuantumNLS.RootEvent.EN_compl_subset
#print axioms QuantumNLS.RootEvent.grid_implies_seg
#print axioms QuantumNLS.RootEvent.prop017_arith
#print axioms QuantumNLS.RootEvent.prop017_bad
