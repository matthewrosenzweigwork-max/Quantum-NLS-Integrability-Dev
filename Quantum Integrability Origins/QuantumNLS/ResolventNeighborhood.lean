import Mathlib
import QuantumNLS.RootEvent
import QuantumNLS.Extrapolation

/-!
# Resolvent neighborhood: partial constituents for PROP-017 (Q7A:eq:Gneighbor, Q7A:eq:derivative)

Owner: haiku_inventory (round 10). Imports the frozen `RootEvent` and `Extrapolation` (read-only).

Scope of this file (independent constituents; NOT the full Gneighbor or derivative clauses):

1. Deterministic Taylor-log sum bound: for `‖w_j‖ ≤ 1/2`,
   `‖∑ (log(1+w_j) − w_j)‖ ≤ ∑ ‖w_j‖²`; and, for `w_j = (c/N)/(z − q_j)` with
   `‖c‖/N ≤ |Im z|/2` and `Im z ≠ 0`, the identity `∑ w_j = c · G_N(z)` yields
   `‖∑ log(1+w_j) − c·G_N(z)‖ ≤ ‖c‖²/(N·(Im z)²)`, which is the O(N⁻¹) error of the
   source Taylor-log estimate (with coefficient normalization `c/N`; see review record).
2. Holomorphy of the full Cauchy transform `G = Gfull μ` (μ a probability measure on ℝ) and of
   `G_N = GN q` on `{z | Im z ≠ 0}`, proved from `hasDerivAt_integral_of_dominated_loc_of_deriv_le`.
3. Maximum modulus on an open rectangle `(a1,a2) × (b1,b2)` lying in the upper half plane
   (`0 < b1`), with the bound given on the frontier. Applied to `G_N − G`, this is the interior
   step of the source strip argument; the boundary bounds (grid event on horizontal sides,
   extrapolation on vertical sides) are NOT proved here and enter as hypotheses.
4. Cauchy derivative bound: a sup bound on a sphere of a function holomorphic on a closed ball in
   the upper half plane controls the derivative at the center (source Cauchy-differentiation step,
   first order only).

Nothing here assumes the target conclusion. No `sorry`, no axioms.
-/

namespace QuantumNLS.ResolventNeighborhood

open MeasureTheory Set Finset Metric
open scoped Topology
open QuantumNLS.Extrapolation
open QuantumNLS.RootEvent

/-! ## 1. Deterministic Taylor-log bounds -/

/-- Pointwise: `‖log(1+w) − w‖ ≤ ‖w‖²` when `‖w‖ ≤ 1/2`. -/
lemma log_sub_self_le_sq {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖Complex.log (1 + w) - w‖ ≤ ‖w‖ ^ 2 := by
  have h1 : ‖w‖ < 1 := by linarith
  refine (Complex.norm_log_one_add_sub_self_le h1).trans ?_
  have hpos : 0 < 1 - ‖w‖ := by linarith
  have hinv : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    linarith
  have hn : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
  have hmul : ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ ≤ ‖w‖ ^ 2 * 2 := mul_le_mul_of_nonneg_left hinv hn
  linarith

/-- Finite sum: `‖∑ (log(1+w_j) − w_j)‖ ≤ ∑ ‖w_j‖²` when every `‖w_j‖ ≤ 1/2`. -/
lemma logTaylor_sum_le {N : ℕ} (w : Fin N → ℂ) (hw : ∀ j, ‖w j‖ ≤ 1 / 2) :
    ‖∑ j, (Complex.log (1 + w j) - w j)‖ ≤ ∑ j, ‖w j‖ ^ 2 :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => log_sub_self_le_sq (hw j))

/-- `|z − q|` dominates `|Im z|` for real `q`. -/
lemma abs_im_le_norm_sub_ofReal (z : ℂ) (q : ℝ) : |z.im| ≤ ‖z - (q : ℂ)‖ := by
  have h := Complex.abs_im_le_norm (z - (q : ℂ))
  simpa using h

/-- Off the real axis, `z − q ≠ 0` for every real `q`. -/
lemma sub_ofReal_ne_zero {z : ℂ} (hz : z.im ≠ 0) (q : ℝ) : z - (q : ℂ) ≠ 0 := by
  intro h
  apply hz
  have := congrArg Complex.im h
  simpa using this

/-- **Taylor-log estimate for the resolvent sum.** With coefficient `c/N` and
`‖c‖/N ≤ |Im z|/2`, `Im z ≠ 0`:
`‖∑_j log(1 + (c/N)/(z − q_j)) − c·G_N(z)‖ ≤ ‖c‖²/(N·(Im z)²)`. -/
lemma logSum_GN_approx {N : ℕ} (hN : N ≠ 0) (q : Fin N → ℝ) (c z : ℂ) (hz : z.im ≠ 0)
    (hc : ‖c‖ / (N : ℝ) ≤ |z.im| / 2) :
    ‖(∑ j, Complex.log (1 + (c / (N : ℂ)) / (z - (q j : ℂ)))) - c * GN q z‖
      ≤ ‖c‖ ^ 2 / ((N : ℝ) * z.im ^ 2) := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hdpos : 0 < |z.im| := abs_pos.mpr hz
  -- the coefficient norm is ‖c‖/N
  have hcN : ‖c / (N : ℂ)‖ = ‖c‖ / (N : ℝ) := by
    rw [norm_div, Complex.norm_natCast]
  -- each summand is at most (‖c‖/N)/|Im z| ≤ 1/2
  have hnorm : ∀ j, ‖(c / (N : ℂ)) / (z - (q j : ℂ))‖ ≤ (‖c‖ / (N : ℝ)) / |z.im| := by
    intro j
    rw [norm_div, hcN]
    exact div_le_div_of_nonneg_left (by positivity) hdpos (abs_im_le_norm_sub_ofReal z (q j))
  have hw : ∀ j, ‖(c / (N : ℂ)) / (z - (q j : ℂ))‖ ≤ 1 / 2 := by
    intro j
    refine (hnorm j).trans ?_
    rw [div_le_iff₀ hdpos]
    linarith
  -- the sum of the coefficients is c·G_N(z)
  have hsum : ∑ j, (c / (N : ℂ)) / (z - (q j : ℂ)) = c * GN q z := by
    unfold GN
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have key : ∑ j, (Complex.log (1 + (c / (N : ℂ)) / (z - (q j : ℂ)))
      - (c / (N : ℂ)) / (z - (q j : ℂ)))
      = (∑ j, Complex.log (1 + (c / (N : ℂ)) / (z - (q j : ℂ)))) - c * GN q z := by
    rw [Finset.sum_sub_distrib, hsum]
  have hbound := logTaylor_sum_le (fun j => (c / (N : ℂ)) / (z - (q j : ℂ))) hw
  have hsq : ∑ j, ‖(c / (N : ℂ)) / (z - (q j : ℂ))‖ ^ 2
      ≤ ‖c‖ ^ 2 / ((N : ℝ) * z.im ^ 2) := by
    calc ∑ j, ‖(c / (N : ℂ)) / (z - (q j : ℂ))‖ ^ 2
        ≤ ∑ _j : Fin N, ((‖c‖ / (N : ℝ)) / |z.im|) ^ 2 :=
          Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hnorm j) 2
      _ = (N : ℝ) * ((‖c‖ / (N : ℝ)) / |z.im|) ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ‖c‖ ^ 2 / ((N : ℝ) * z.im ^ 2) := by
          rw [div_pow, sq_abs]
          field_simp
  rw [← key]
  exact hbound.trans hsq

/-! ## 2. Holomorphy of `G = Gfull μ` and `G_N = GN q` off the real axis -/

/-- Derivative of `w ↦ 1/(w − q)` for real `q`, off `q`. -/
lemma hasDerivAt_one_div_sub_ofReal {z : ℂ} {q : ℝ} (hz : z - (q : ℂ) ≠ 0) :
    HasDerivAt (fun w : ℂ => 1 / (w - (q : ℂ))) (-(1 / (z - (q : ℂ)) ^ 2)) z := by
  have h : HasDerivAt (fun w : ℂ => (w - (q : ℂ))⁻¹) (-1 / (z - (q : ℂ)) ^ 2) z :=
    ((hasDerivAt_id z).sub_const (q : ℂ)).inv hz
  have e1 : (fun w : ℂ => 1 / (w - (q : ℂ))) = (fun w : ℂ => (w - (q : ℂ))⁻¹) :=
    funext fun w => one_div _
  have e2 : -(1 / (z - (q : ℂ)) ^ 2) = -1 / (z - (q : ℂ)) ^ 2 := by ring
  rw [e1, e2]
  exact h

/-- **Holomorphy of the Cauchy transform off ℝ.** For a probability measure `μ` on ℝ and
`Im z₀ ≠ 0`, `Gfull μ` has derivative `∫ −1/(z₀ − q)² dμ(q)` at `z₀`. -/
lemma Gfull_hasDerivAt (μ : Measure ℝ) [IsProbabilityMeasure μ] {z0 : ℂ} (hz0 : z0.im ≠ 0) :
    HasDerivAt (Gfull μ) (∫ q, -(1 / (z0 - (q : ℂ)) ^ 2) ∂μ) z0 := by
  set d : ℝ := |z0.im| / 2 with hd
  have hdpos : 0 < d := div_pos (abs_pos.mpr hz0) two_pos
  -- on the ball of radius d around z0, |Im z| > d
  have hball : ∀ z ∈ ball z0 d, d < |z.im| := by
    intro z hz
    have h1 : ‖z - z0‖ < d := by
      have := hz
      rw [mem_ball, dist_eq_norm] at this
      exact this
    have h4 := abs_sub_abs_le_abs_sub z0.im z.im
    have h5 : |z0.im - z.im| = |z.im - z0.im| := abs_sub_comm _ _
    have h6 : |z.im - z0.im| ≤ ‖z - z0‖ := by
      have := Complex.abs_im_le_norm (z - z0)
      simpa using this
    linarith
  have hne : ∀ z ∈ ball z0 d, ∀ q : ℝ, z - (q : ℂ) ≠ 0 := by
    intro z hz q
    have hz' : z.im ≠ 0 := by
      have := hball z hz
      intro h0
      rw [h0, abs_zero] at this
      linarith
    exact sub_ofReal_ne_zero hz' q
  -- continuity in q for fixed z in the ball
  have hcont : ∀ z ∈ ball z0 d, Continuous (fun q : ℝ => 1 / (z - (q : ℂ))) :=
    fun z hz => continuous_const.div (continuous_const.sub Complex.continuous_ofReal)
      (fun q => hne z hz q)
  have hcont' : ∀ z ∈ ball z0 d, Continuous (fun q : ℝ => -(1 / (z - (q : ℂ)) ^ 2)) :=
    fun z hz => (continuous_const.div ((continuous_const.sub Complex.continuous_ofReal).pow 2)
      (fun q => pow_ne_zero 2 (hne z hz q))).neg
  -- uniform bounds on the ball
  have hF'bd : ∀ z ∈ ball z0 d, ∀ q : ℝ, ‖-(1 / (z - (q : ℂ)) ^ 2)‖ ≤ 1 / d ^ 2 := by
    intro z hz q
    have hnorm : d < ‖z - (q : ℂ)‖ := lt_of_lt_of_le (hball z hz) (abs_im_le_norm_sub_ofReal z q)
    rw [norm_neg, norm_div, norm_one, norm_pow]
    have h1 : d ^ 2 ≤ ‖z - (q : ℂ)‖ ^ 2 := pow_le_pow_left₀ hdpos.le hnorm.le 2
    exact div_le_div_of_nonneg_left zero_le_one (by positivity) h1
  have hF0bd : ∀ q : ℝ, ‖1 / (z0 - (q : ℂ))‖ ≤ 1 / d := by
    intro q
    have hnorm : d ≤ ‖z0 - (q : ℂ)‖ :=
      (lt_of_lt_of_le (hball z0 (mem_ball_self hdpos)) (abs_im_le_norm_sub_ofReal z0 q)).le
    rw [norm_div, norm_one]
    exact div_le_div_of_nonneg_left zero_le_one hdpos hnorm
  have hF_meas : ∀ᶠ z in 𝓝 z0,
      AEStronglyMeasurable (fun q : ℝ => 1 / (z - (q : ℂ))) μ :=
    Filter.eventually_of_mem (ball_mem_nhds z0 hdpos)
      fun z hz => (hcont z hz).aestronglyMeasurable
  have hF_int : Integrable (fun q : ℝ => 1 / (z0 - (q : ℂ))) μ :=
    Integrable.of_bound (hcont z0 (mem_ball_self hdpos)).aestronglyMeasurable (1 / d)
      (ae_of_all μ fun q => hF0bd q)
  have hF'_meas : AEStronglyMeasurable (fun q : ℝ => -(1 / (z0 - (q : ℂ)) ^ 2)) μ :=
    (hcont' z0 (mem_ball_self hdpos)).aestronglyMeasurable
  have h_bound : ∀ᵐ (q : ℝ) ∂μ, ∀ z : ℂ, z ∈ ball z0 d →
      ‖-(1 / (z - (q : ℂ)) ^ 2)‖ ≤ 1 / d ^ 2 :=
    ae_of_all μ fun q z hz => hF'bd z hz q
  have h_diff : ∀ᵐ (q : ℝ) ∂μ, ∀ z : ℂ, z ∈ ball z0 d →
      HasDerivAt (fun w : ℂ => 1 / (w - (q : ℂ))) (-(1 / (z - (q : ℂ)) ^ 2)) z :=
    ae_of_all μ fun q z hz => hasDerivAt_one_div_sub_ofReal (hne z hz q)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun (z : ℂ) (q : ℝ) => 1 / (z - (q : ℂ)))
    (F' := fun (z : ℂ) (q : ℝ) => -(1 / (z - (q : ℂ)) ^ 2))
    (x₀ := z0) (s := ball z0 d) (bound := fun _ => 1 / d ^ 2)
    (ball_mem_nhds z0 hdpos) hF_meas hF_int hF'_meas h_bound (integrable_const _) h_diff
  exact key.2

/-- `Gfull μ` is holomorphic on `{Im z ≠ 0}`. -/
lemma Gfull_differentiableOn_offReal (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    DifferentiableOn ℂ (Gfull μ) {z : ℂ | z.im ≠ 0} :=
  fun z hz => (Gfull_hasDerivAt μ hz).differentiableAt.differentiableWithinAt

/-- `GN q` is holomorphic on `{Im z ≠ 0}` (the nodes `q_j` are real). -/
lemma GN_differentiableOn_offReal {N : ℕ} (q : Fin N → ℝ) :
    DifferentiableOn ℂ (GN q) {z : ℂ | z.im ≠ 0} := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  unfold GN
  refine DifferentiableAt.const_mul ?_ _
  refine DifferentiableAt.fun_sum fun j _ => ?_
  exact (differentiableAt_const _).div ((differentiableAt_id.sub_const _))
    (sub_ofReal_ne_zero hz (q j))

/-! ## 3. Maximum modulus on an open rectangle in the upper half plane -/

/-- Open rectangle `(a1,a2) × (b1,b2)` in `ℂ`. -/
def openRect (a1 a2 b1 b2 : ℝ) : Set ℂ :=
  {z | a1 < z.re ∧ z.re < a2 ∧ b1 < z.im ∧ z.im < b2}

lemma openRect_isOpen (a1 a2 b1 b2 : ℝ) : IsOpen (openRect a1 a2 b1 b2) := by
  have h1 : IsOpen {z : ℂ | a1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen {z : ℂ | z.re < a2} := isOpen_lt Complex.continuous_re continuous_const
  have h3 : IsOpen {z : ℂ | b1 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have h4 : IsOpen {z : ℂ | z.im < b2} := isOpen_lt Complex.continuous_im continuous_const
  simp only [openRect, Set.ofPred_and]
  exact h1.inter (h2.inter (h3.inter h4))

/-- Closed rectangle, containing the closure of `openRect`. -/
def closedRect (a1 a2 b1 b2 : ℝ) : Set ℂ :=
  {z | a1 ≤ z.re ∧ z.re ≤ a2 ∧ b1 ≤ z.im ∧ z.im ≤ b2}

lemma closure_openRect_subset (a1 a2 b1 b2 : ℝ) :
    closure (openRect a1 a2 b1 b2) ⊆ closedRect a1 a2 b1 b2 := by
  apply closure_minimal
  · intro z hz
    exact ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩
  · have c1 : IsClosed {z : ℂ | a1 ≤ z.re} := isClosed_le continuous_const Complex.continuous_re
    have c2 : IsClosed {z : ℂ | z.re ≤ a2} := isClosed_le Complex.continuous_re continuous_const
    have c3 : IsClosed {z : ℂ | b1 ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
    have c4 : IsClosed {z : ℂ | z.im ≤ b2} := isClosed_le Complex.continuous_im continuous_const
    simp only [closedRect, Set.ofPred_and]
    exact c1.inter (c2.inter (c3.inter c4))

lemma openRect_isBounded (a1 a2 b1 b2 : ℝ) : Bornology.IsBounded (openRect a1 a2 b1 b2) := by
  refine isBounded_iff_forall_norm_le.mpr ⟨|a1| + |a2| + |b1| + |b2|, fun z hz => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have hre : |z.re| ≤ |a1| + |a2| := abs_le.mpr ⟨by linarith [neg_abs_le a1, abs_nonneg a2],
    by linarith [le_abs_self a2, abs_nonneg a1]⟩
  have him : |z.im| ≤ |b1| + |b2| := abs_le.mpr ⟨by linarith [neg_abs_le b1, abs_nonneg b2],
    by linarith [le_abs_self b2, abs_nonneg b1]⟩
  have := Complex.norm_le_abs_re_add_abs_im z
  linarith

/-- Frontier of the open rectangle lies on its four sides. -/
lemma frontier_openRect_sides {a1 a2 b1 b2 : ℝ} {z : ℂ} (hz : z ∈ frontier (openRect a1 a2 b1 b2)) :
    z.re = a1 ∨ z.re = a2 ∨ z.im = b1 ∨ z.im = b2 := by
  rw [frontier, (openRect_isOpen a1 a2 b1 b2).interior_eq] at hz
  obtain ⟨hcl, hnU⟩ := hz
  obtain ⟨h1, h2, h3, h4⟩ := closure_openRect_subset a1 a2 b1 b2 hcl
  by_contra hne
  simp only [not_or] at hne
  apply hnU
  exact ⟨lt_of_le_of_ne h1 (fun e => hne.1 e.symm), lt_of_le_of_ne h2 hne.2.1,
    lt_of_le_of_ne h3 (fun e => hne.2.2.1 e.symm), lt_of_le_of_ne h4 hne.2.2.2⟩

/-- **Maximum modulus step on an open rectangle in the upper half plane.** If `f` is holomorphic
on `{Im z > 0}` and `‖f‖ ≤ C` on the frontier of the open rectangle `(a1,a2) × (b1,b2)` with
`0 < b1`, then `‖f‖ ≤ C` on the closure of the rectangle. -/
theorem maxmod_openRect {f : ℂ → ℂ} {a1 a2 b1 b2 C : ℝ} (hb : 0 < b1)
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hC : ∀ z ∈ frontier (openRect a1 a2 b1 b2), ‖f z‖ ≤ C) :
    ∀ z ∈ closure (openRect a1 a2 b1 b2), ‖f z‖ ≤ C := by
  have hsub : openRect a1 a2 b1 b2 ⊆ {z : ℂ | 0 < z.im} :=
    fun z hz => lt_trans hb hz.2.2.1
  have hcl_half : closure (openRect a1 a2 b1 b2) ⊆ {z : ℂ | 0 < z.im} := by
    have hclosed : closure (openRect a1 a2 b1 b2) ⊆ {z : ℂ | b1 ≤ z.im} := by
      apply closure_minimal
      · intro z hz
        exact hz.2.2.1.le
      · exact isClosed_le continuous_const Complex.continuous_im
    intro z hz
    exact lt_of_lt_of_le hb (hclosed hz)
  have hdc : DiffContOnCl ℂ f (openRect a1 a2 b1 b2) :=
    ⟨hf.mono hsub, hf.continuousOn.mono hcl_half⟩
  intro z hz
  exact Complex.norm_le_of_forall_mem_frontier_norm_le (openRect_isBounded a1 a2 b1 b2) hdc hC hz

/-- Version with the boundary bound stated on the four closed sides (the form in which the grid
event and the extrapolation estimate supply the boundary control). -/
theorem maxmod_openRect_sides {f : ℂ → ℂ} {a1 a2 b1 b2 C : ℝ} (hb : 0 < b1)
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hC : ∀ z : ℂ, (z.re = a1 ∨ z.re = a2 ∨ z.im = b1 ∨ z.im = b2) →
      a1 ≤ z.re → z.re ≤ a2 → b1 ≤ z.im → z.im ≤ b2 → ‖f z‖ ≤ C) :
    ∀ z ∈ closure (openRect a1 a2 b1 b2), ‖f z‖ ≤ C := by
  apply maxmod_openRect hb hf
  intro z hz
  obtain ⟨h1, h2, h3, h4⟩ := closure_openRect_subset a1 a2 b1 b2
    (frontier_subset_closure hz)
  exact hC z (frontier_openRect_sides hz) h1 h2 h3 h4

/-- **Strip step for `G_N − G`.** Maximum modulus for `Gfull μ − GN q` on an open rectangle in the
upper half plane, with the boundary bound on the sides. Holomorphy of both terms is proved above;
only the boundary bound is a hypothesis. -/
theorem maxmod_Gfull_sub_GN {N : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] (q : Fin N → ℝ)
    {a1 a2 b1 b2 C : ℝ} (hb : 0 < b1)
    (hC : ∀ z : ℂ, (z.re = a1 ∨ z.re = a2 ∨ z.im = b1 ∨ z.im = b2) →
      a1 ≤ z.re → z.re ≤ a2 → b1 ≤ z.im → z.im ≤ b2 → ‖Gfull μ z - GN q z‖ ≤ C) :
    ∀ z ∈ closure (openRect a1 a2 b1 b2), ‖Gfull μ z - GN q z‖ ≤ C := by
  have hG : DifferentiableOn ℂ (Gfull μ) {z : ℂ | 0 < z.im} :=
    (Gfull_differentiableOn_offReal μ).mono fun z hz => hz.ne'
  have hN : DifferentiableOn ℂ (GN q) {z : ℂ | 0 < z.im} :=
    (GN_differentiableOn_offReal q).mono fun z hz => hz.ne'
  exact maxmod_openRect_sides hb (hG.sub hN) hC

/-! ## 4. Cauchy derivative bound (first order) -/

/-- **Cauchy estimate at the center.** If `f` is holomorphic on `{Im z > 0}`, the closed ball
`closedBall c R` lies in the upper half plane, and `‖f‖ ≤ C` on the sphere, then
`‖f'(c)‖ ≤ C/R`. -/
theorem deriv_bound_of_sphere {f : ℂ → ℂ} {c : ℂ} {R C : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hball : closedBall c R ⊆ {z : ℂ | 0 < z.im})
    (hC : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) :
    ‖deriv f c‖ ≤ C / R := by
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR
  · exact ⟨hf.mono (ball_subset_closedBall.trans hball),
      hf.continuousOn.mono ((Metric.closure_ball_subset_closedBall).trans hball)⟩
  · exact hC

/-- The Cauchy estimate applied to `G_N − G` on a ball in the upper half plane. -/
theorem deriv_Gfull_sub_GN_bound {N : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] (q : Fin N → ℝ)
    {c : ℂ} {R C : ℝ} (hR : 0 < R) (hball : closedBall c R ⊆ {z : ℂ | 0 < z.im})
    (hC : ∀ z ∈ sphere c R, ‖Gfull μ z - GN q z‖ ≤ C) :
    ‖deriv (fun z => Gfull μ z - GN q z) c‖ ≤ C / R := by
  have hG : DifferentiableOn ℂ (Gfull μ) {z : ℂ | 0 < z.im} :=
    (Gfull_differentiableOn_offReal μ).mono fun z hz => hz.ne'
  have hN : DifferentiableOn ℂ (GN q) {z : ℂ | 0 < z.im} :=
    (GN_differentiableOn_offReal q).mono fun z hz => hz.ne'
  exact deriv_bound_of_sphere hR (hG.sub hN) hball hC

/-! ## 5. Closure geometry: the closed rectangle lies in the closure of the open rectangle -/

lemma closedRect_subset_closure_openRect {a1 a2 b1 b2 : ℝ} (ha : a1 < a2) (hb : b1 < b2) :
    closedRect a1 a2 b1 b2 ⊆ closure (openRect a1 a2 b1 b2) := by
  intro z hz
  obtain ⟨h1, h2, h3, h4⟩ := hz
  let f : ℝ → ℂ := fun t =>
    (((1 - t) * ((a1 + a2) / 2) + t * z.re : ℝ) : ℂ)
      + (((1 - t) * ((b1 + b2) / 2) + t * z.im : ℝ) : ℂ) * Complex.I
  have hfc : Continuous f := by
    simp only [f]
    fun_prop
  have hf1 : f 1 = z := by
    apply Complex.ext <;> simp [f]
  have hT : Filter.Tendsto f (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds z) := by
    have := (hfc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
    rwa [hf1] at this
  have hev : ∀ᶠ t in nhdsWithin (1 : ℝ) (Set.Iio 1), f t ∈ openRect a1 a2 b1 b2 := by
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have hu : 0 < 1 - t := by linarith
    have p1 : 0 < (1 - t) * ((a1 + a2) / 2 - a1) := mul_pos hu (by linarith)
    have p2 : 0 ≤ t * (z.re - a1) := mul_nonneg ht0.le (by linarith)
    have p3 : 0 < (1 - t) * (a2 - (a1 + a2) / 2) := mul_pos hu (by linarith)
    have p4 : 0 ≤ t * (a2 - z.re) := mul_nonneg ht0.le (by linarith)
    have q1 : 0 < (1 - t) * ((b1 + b2) / 2 - b1) := mul_pos hu (by linarith)
    have q2 : 0 ≤ t * (z.im - b1) := mul_nonneg ht0.le (by linarith)
    have q3 : 0 < (1 - t) * (b2 - (b1 + b2) / 2) := mul_pos hu (by linarith)
    have q4 : 0 ≤ t * (b2 - z.im) := mul_nonneg ht0.le (by linarith)
    simp only [openRect, Set.mem_ofPred_eq, f, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  exact mem_closure_of_tendsto hT hev

/-! ## 6. Boundary control of the upper strip and the neighbourhood of `Γ_N` -/

/-- The rectangle `Γ_N` with endpoints `±a` and heights `±h` (its boundary, source notation). -/
def GammaN (a h : ℝ) : Set ℂ :=
  {w | (w.re = a ∨ w.re = -a) ∧ |w.im| ≤ h} ∪ {w | (w.im = h ∨ w.im = -h) ∧ |w.re| ≤ a}

/-- The closed `ρ`-neighbourhood of `Γ_N`. -/
def NbhdN (a h ρ : ℝ) : Set ℂ := {z | ∃ w ∈ GammaN a h, ‖z - w‖ ≤ ρ}

/-- Every point of the `ρ`-neighbourhood of `Γ_N` lies in one of the four pieces: the two
vertical source rectangles at `±a`, or the upper/lower strip rectangles. -/
lemma nbhd_cover {a h ρ : ℝ} (hρ : 0 ≤ ρ) {z : ℂ} (hz : z ∈ NbhdN a h ρ) :
    z ∈ srcRect a ρ h ∨ z ∈ srcRect (-a) ρ h ∨
      z ∈ closedRect (-a - 2 * ρ) (a + 2 * ρ) (h - 2 * ρ) (h + 2 * ρ) ∨
      z ∈ closedRect (-a - 2 * ρ) (a + 2 * ρ) (-h - 2 * ρ) (-h + 2 * ρ) := by
  obtain ⟨w, hw, hdist⟩ := hz
  have hre : |z.re - w.re| ≤ ρ := by
    have h1 := Complex.abs_re_le_norm (z - w)
    simp only [Complex.sub_re] at h1
    exact h1.trans hdist
  have him : |z.im - w.im| ≤ ρ := by
    have h1 := Complex.abs_im_le_norm (z - w)
    simp only [Complex.sub_im] at h1
    exact h1.trans hdist
  rcases hw with ⟨hwr, hwi⟩ | ⟨hwi, hwr⟩
  · -- vertical piece of Γ_N: |w.re| = a, |w.im| ≤ h
    have hzim : |z.im| ≤ h + 2 * ρ := by
      have h1 := abs_le.mp hwi
      have h2 := abs_le.mp him
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    rcases hwr with hr | hr
    · left
      show |z.re - a| ≤ 2 * ρ ∧ |z.im| ≤ h + 2 * ρ
      refine ⟨?_, hzim⟩
      rw [hr] at hre
      exact le_trans hre (by linarith)
    · right; left
      show |z.re - -a| ≤ 2 * ρ ∧ |z.im| ≤ h + 2 * ρ
      refine ⟨?_, hzim⟩
      rw [hr] at hre
      exact le_trans hre (by linarith)
  · -- horizontal piece of Γ_N: w.im = ±h, |w.re| ≤ a
    have h1 := abs_le.mp hwr
    have h2 := abs_le.mp hre
    have h3 := abs_le.mp him
    rcases hwi with hi | hi
    · right; right; left
      show -a - 2 * ρ ≤ z.re ∧ z.re ≤ a + 2 * ρ ∧ h - 2 * ρ ≤ z.im ∧ z.im ≤ h + 2 * ρ
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
    · right; right; right
      show -a - 2 * ρ ≤ z.re ∧ z.re ≤ a + 2 * ρ ∧ -h - 2 * ρ ≤ z.im ∧ z.im ≤ -h + 2 * ρ
      refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- Arithmetic: the boundary constants are bounded by `2K(ε + R^{-b})`, with
`K = max (max 1 |C_m|) |C_{m,p}|`, provided `R ≥ 1`, `b ≤ m+2`, `b ≤ 2p`. -/
lemma max_bound_arith {Cm Cp ε R : ℝ} {m p b : ℕ} (hR1 : 1 ≤ R) (hε : 0 ≤ ε)
    (hb : b ≤ m + 2) (hb2 : b ≤ 2 * p) :
    max ε (Cm * ε + Cm * (1 / R ^ (m + 2)) + Cp * (1 / R ^ (2 * p)))
      ≤ 2 * max (max 1 |Cm|) |Cp| * (ε + 1 / R ^ b) := by
  set K := max (max 1 |Cm|) |Cp| with hKdef
  have hK1 : 1 ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have hKCm : |Cm| ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  have hKCp : |Cp| ≤ K := le_max_right _ _
  have hRpos : 0 < R := by linarith
  have hxb : 0 ≤ 1 / R ^ b := by positivity
  have hx1 : 1 / R ^ (m + 2) ≤ 1 / R ^ b :=
    one_div_le_one_div_of_le (pow_pos hRpos b) (pow_le_pow_right₀ hR1 hb)
  have hx2 : 1 / R ^ (2 * p) ≤ 1 / R ^ b :=
    one_div_le_one_div_of_le (pow_pos hRpos b) (pow_le_pow_right₀ hR1 hb2)
  have hKε : ε ≤ K * ε := le_mul_of_one_le_left hε hK1
  have hK0 : 0 ≤ K := by linarith
  have hKε0 : 0 ≤ K * ε := mul_nonneg hK0 hε
  have hKx : 0 ≤ K * (1 / R ^ b) := mul_nonneg hK0 hxb
  have t1 : Cm * ε ≤ K * ε := mul_le_mul_of_nonneg_right ((le_abs_self Cm).trans hKCm) hε
  have t2 : Cm * (1 / R ^ (m + 2)) ≤ K * (1 / R ^ b) :=
    calc Cm * (1 / R ^ (m + 2)) ≤ |Cm| * (1 / R ^ (m + 2)) :=
          mul_le_mul_of_nonneg_right (le_abs_self Cm) (by positivity)
      _ ≤ |Cm| * (1 / R ^ b) := mul_le_mul_of_nonneg_left hx1 (abs_nonneg _)
      _ ≤ K * (1 / R ^ b) := mul_le_mul_of_nonneg_right hKCm hxb
  have t3 : Cp * (1 / R ^ (2 * p)) ≤ K * (1 / R ^ b) :=
    calc Cp * (1 / R ^ (2 * p)) ≤ |Cp| * (1 / R ^ (2 * p)) :=
          mul_le_mul_of_nonneg_right (le_abs_self Cp) (by positivity)
      _ ≤ |Cp| * (1 / R ^ b) := mul_le_mul_of_nonneg_left hx2 (abs_nonneg _)
      _ ≤ K * (1 / R ^ b) := mul_le_mul_of_nonneg_right hKCp hxb
  apply max_le
  · nlinarith
  · nlinarith

/-- **Upper strip bound.** On the upper strip rectangle `(−a−2ρ, a+2ρ) × (h−2ρ, h+2ρ)` (with
`0 < h−2ρ`), the error `‖G − G_N‖` is at most `max ε B` provided it is at most `ε` on the
horizontal segments (`segSet`) and at most `B` on both vertical source rectangles. The interior
bound is the maximum-modulus step; the four sides are the hypotheses. -/
theorem upper_strip_bound (μ : Measure ℝ) [IsProbabilityMeasure μ] {N : ℕ} (q : Fin N → ℝ)
    {a ρ h ε B : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hb : 0 < h - 2 * ρ)
    (hseg : ∀ z ∈ segSet a ρ h, ‖Gfull μ z - GN q z‖ ≤ ε)
    (hDp : ∀ z ∈ srcRect a ρ h, ‖Gfull μ z - GN q z‖ ≤ B)
    (hDm : ∀ z ∈ srcRect (-a) ρ h, ‖Gfull μ z - GN q z‖ ≤ B) :
    ∀ z ∈ closedRect (-a - 2 * ρ) (a + 2 * ρ) (h - 2 * ρ) (h + 2 * ρ),
      ‖Gfull μ z - GN q z‖ ≤ max ε B := by
  have hsub := closedRect_subset_closure_openRect (a1 := -a - 2 * ρ) (a2 := a + 2 * ρ)
    (b1 := h - 2 * ρ) (b2 := h + 2 * ρ) (by linarith) (by linarith)
  have hC : ∀ z : ℂ, (z.re = -a - 2 * ρ ∨ z.re = a + 2 * ρ ∨ z.im = h - 2 * ρ ∨ z.im = h + 2 * ρ) →
      -a - 2 * ρ ≤ z.re → z.re ≤ a + 2 * ρ → h - 2 * ρ ≤ z.im → z.im ≤ h + 2 * ρ →
      ‖Gfull μ z - GN q z‖ ≤ max ε B := by
    intro z hside h1 h2 h3 h4
    rcases hside with hr | hr | hi | hi
    · have hzm : z ∈ srcRect (-a) ρ h := by
        show |z.re - -a| ≤ 2 * ρ ∧ |z.im| ≤ h + 2 * ρ
        refine ⟨?_, ?_⟩
        · rw [hr, abs_le]; constructor <;> linarith
        · rw [abs_le]; constructor <;> linarith
      exact (hDm z hzm).trans (le_max_right _ _)
    · have hzp : z ∈ srcRect a ρ h := by
        show |z.re - a| ≤ 2 * ρ ∧ |z.im| ≤ h + 2 * ρ
        refine ⟨?_, ?_⟩
        · rw [hr, abs_le]; constructor <;> linarith
        · rw [abs_le]; constructor <;> linarith
      exact (hDp z hzp).trans (le_max_right _ _)
    · have hzs : z ∈ segSet a ρ h :=
        ⟨⟨by linarith, by linarith⟩, 0, by simp [gridHeight, hi]⟩
      exact (hseg z hzs).trans (le_max_left _ _)
    · have hzs : z ∈ segSet a ρ h :=
        ⟨⟨by linarith, by linarith⟩, 2, by simp [gridHeight, hi]⟩
      exact (hseg z hzs).trans (le_max_left _ _)
  have hmax := maxmod_Gfull_sub_GN μ q (a1 := -a - 2 * ρ) (a2 := a + 2 * ρ)
    (b1 := h - 2 * ρ) (b2 := h + 2 * ρ) (C := max ε B) hb hC
  intro z hz
  exact hmax z (hsub hz)

/-- **Q7A:eq:Gneighbor, wired (on the event `E_N`).** Let the source hypotheses hold: the cut gap
`δ` for the classical law at both cuts `±a` (`hsupp`, `hsuppN`), the uniform variance bound
`hms` (`Q7A:eq:ms`) at heights `y ≥ η₀`, the node moments (`hμint`), the rectangle geometry
`ρ < δ/4`, `0 < η₀ ≤ h − 2ρ`, `h + 4ρ < H`, `2H ≤ R`, `2(η₀+1+m) ≤ R`, and `2R ≤ |a|`.
Then on `E_N` (roots in `[−R,R]`, node errors `≤ ε` at both cuts, `|G − G_N| ≤ ε` on the
segments), for every `z` in the closed `ρ`-neighbourhood of `Γ_N`,
`|G(z) − G_N(z)| ≤ 2K(ε + R^{-b})` with `K = max (max 1 |C_m|) |C_{m,p}|`, where
`C_m = srcCm`, `C_{m,p} = srcCmp` are the literal extrapolation constants of PROP-016 and
`b ≤ m+2`, `b ≤ 2p` (the source's "constants use finitely many moments determined by `b`").
The only inputs are the source hypotheses above and the event `E_N`; no conclusion is assumed. -/
theorem gneighbor_on_EN {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (hN : 0 < N) (q : Ω → Fin N → ℝ) (hq : Measurable q)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (m p b : ℕ)
    (η0 δ ρ h H R a ε Cms : ℝ)
    (hη0 : 0 < η0) (hρ : 0 < ρ) (hρδ : ρ < δ / 4) (hηh : η0 ≤ h - 2 * ρ)
    (hb0 : 0 < h - 2 * ρ) (hH : h + 4 * ρ < H) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hRH : 2 * H ≤ R) (hRH1 : 2 * (η0 + 1 + m) ≤ R)
    (ha : 0 < a) (hcut : 2 * R ≤ |a|) (hε : 0 ≤ ε)
    (hμint : Integrable (fun x : ℝ => x ^ (2 * p)) μ)
    (hsupp : ∀ᵐ x ∂μ, δ ≤ |x - a|) (hsuppN : ∀ᵐ x ∂μ, δ ≤ |x + a|)
    (hms : ∀ x y : ℝ, η0 ≤ y → ∫ ω, ‖Gfull μ ((x : ℂ) + (y : ℂ) * Complex.I)
        - GN (q ω) ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 ∂P ≤ Cms / ((N : ℝ) * y ^ 2))
    (hb : b ≤ m + 2) (hb2 : b ≤ 2 * p)
    (ω : Ω) (hω : ω ∈ EN μ q R a ρ h η0 ε m) :
    ∀ z ∈ NbhdN a h ρ, ‖Gfull μ z - GN (q ω) z‖ ≤
      2 * max (max 1 |srcCm η0 H Cms m|) |srcCmp η0 H δ ρ m μ p| * (ε + 1 / R ^ b) := by
  obtain ⟨hroots, hnodeA, hnodeN, hseg⟩ := hω
  have hηh' : η0 < h := by linarith
  have hsn : ∀ k : Fin (m + 1), srcNodes η0 m k
      = (((η0 + 1 + ((k : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I := fun k => rfl
  have him : ∀ (x : ℝ) (k : Fin (m + 1)),
      (((x : ℂ)) + srcNodes η0 m k).im = η0 + 1 + ((k : ℕ) : ℝ) := by
    intro x k
    rw [hsn k]
    simp
  have hpos : ∀ k : Fin (m + 1), ∀ x : ℝ, (((x : ℂ)) + srcNodes η0 m k).im ≠ 0 := by
    intro k x
    rw [him x k]
    have := (Nat.cast_nonneg ((k : ℕ)) : (0 : ℝ) ≤ ((k : ℕ) : ℝ))
    linarith
  -- integrability of the squared node errors (both cuts)
  have hsq : ∀ (x : ℝ) (k : Fin (m + 1)), Integrable (fun ω' =>
      ‖Gfull μ ((x : ℂ) + srcNodes η0 m k) - GN (q ω') ((x : ℂ) + srcNodes η0 m k)‖ ^ 2) P :=
    fun x k => sq_integrable_of_im_ne P hN q hq μ _ (hpos k x)
  -- variance at the nodes, from the uniform bound `hms`
  have hvar : ∀ (x : ℝ) (k : Fin (m + 1)), ∫ ω', ‖Gfull μ ((x : ℂ) + srcNodes η0 m k)
      - GN (q ω') ((x : ℂ) + srcNodes η0 m k)‖ ^ 2 ∂P
        ≤ Cms / ((N : ℝ) * (η0 + 1 + ((k : ℕ) : ℝ)) ^ 2) := by
    intro x k
    rw [hsn k]
    exact hms_all P q μ η0 Cms hms x _
      (le_trans (by have := (Nat.cast_nonneg ((k : ℕ)) : (0 : ℝ) ≤ ((k : ℕ) : ℝ)); linarith)
        (le_abs_self _))
  -- extrapolation at the cut `a` and at the cut `-a`
  have hcutN : 2 * R ≤ |-a| := by rw [abs_neg]; exact hcut
  have hsuppA : ∀ᵐ x ∂μ, δ ≤ |x - a| := hsupp
  have hsuppM : ∀ᵐ x ∂μ, δ ≤ |x - (-a)| := hsuppN.mono fun x hx => by rw [sub_neg_eq_add]; exact hx
  obtain ⟨hDA, -⟩ := prop016_literal P hN q μ m η0 δ ρ h H R a p hη0 hρ hρδ hηh' hH hR hRH hRH1
    hcut hμint hsuppA Cms (fun k => hsq a k) (fun k => hvar a k)
  obtain ⟨hDM, -⟩ := prop016_literal P hN q μ m η0 δ ρ h H R (-a) p hη0 hρ hρδ hηh' hH hR hRH hRH1
    hcutN hμint hsuppM Cms (fun k => hsq (-a) k) (fun k => hvar (-a) k)
  set Cm := srcCm η0 H Cms m with hCm
  set Cp := srcCmp η0 H δ ρ m μ p with hCp
  set B := Cm * ε + Cm * (1 / R ^ (m + 2)) + Cp * (1 / R ^ (2 * p)) with hB
  have hDp : ∀ z ∈ srcRect a ρ h, ‖Gfull μ z - GN (q ω) z‖ ≤ B :=
    hDA ω hroots ε hε hnodeA
  have hDm : ∀ z ∈ srcRect (-a) ρ h, ‖Gfull μ z - GN (q ω) z‖ ≤ B :=
    hDM ω hroots ε hε hnodeN
  have hsegε : ∀ z ∈ segSet a ρ h, ‖Gfull μ z - GN (q ω) z‖ ≤ ε :=
    fun z hz => hseg z hz
  have hup := upper_strip_bound μ (q ω) ha hρ hb0 hsegε hDp hDm
  intro z hz
  rcases nbhd_cover hρ.le hz with h1 | h1 | h1 | h1
  · exact (hDp z h1).trans ((le_max_right _ _).trans (max_bound_arith hR1 hε hb hb2))
  · exact (hDm z h1).trans ((le_max_right _ _).trans (max_bound_arith hR1 hε hb hb2))
  · exact (hup z h1).trans (max_bound_arith hR1 hε hb hb2)
  · have hc : starRingEnd ℂ z ∈ closedRect (-a - 2 * ρ) (a + 2 * ρ) (h - 2 * ρ) (h + 2 * ρ) := by
      obtain ⟨c1, c2, c3, c4⟩ := h1
      show -a - 2 * ρ ≤ (starRingEnd ℂ z).re ∧ (starRingEnd ℂ z).re ≤ a + 2 * ρ ∧
        h - 2 * ρ ≤ (starRingEnd ℂ z).im ∧ (starRingEnd ℂ z).im ≤ h + 2 * ρ
      simp only [Complex.conj_re, Complex.conj_im]
      refine ⟨c1, c2, ?_, ?_⟩ <;> linarith
    rw [← err_conj μ (q ω) z]
    exact (hup _ hc).trans (max_bound_arith hR1 hε hb hb2)

/-! ## 7. Derivative clause, `j = 0`: Taylor-log, exponentiation, transfer symbol -/

/-- Gneighbor constant `K = max (max 1 |C_m|) |C_{m,p}|` (PROP-016 literal constants). -/
noncomputable def KGN (η0 δ ρ H Cms : ℝ) (m p : ℕ) (μ : Measure ℝ) : ℝ :=
  max (max 1 |srcCm η0 H Cms m|) |srcCmp η0 H δ ρ m μ p|

/-- Inner radius `r = min(h−2ρ, δ−2ρ, a−2ρ−R)`: distance of the neighbourhood from the real axis
(horizontal pieces), from the classical support (vertical pieces), and from the roots
(vertical pieces, `|q_j| ≤ R`). -/
def rNbhd (a h ρ R δ : ℝ) : ℝ := min (h - 2 * ρ) (min (δ - 2 * ρ) (a - 2 * ρ - R))

/-- Source transfer symbol with `c = κ/N`:
`s_N(z;q) = ∏(1 + ic/(z−q_j)) + e(z) ∏(1 − ic/(z−q_j))`, `e(z) = e^{iLz}`.
The second product is written `1 + i(−κ)/N/(z−q_j)`, i.e. `1 − ic/(z−q_j)`. -/
noncomputable def sNsrc (κ L : ℝ) {N : ℕ} (q : Fin N → ℝ) (z : ℂ) : ℂ :=
  (∏ j, (1 + Complex.I * (κ : ℂ) / (N : ℂ) / (z - (q j : ℂ))))
    + Complex.exp (Complex.I * (L : ℂ) * z)
      * ∏ j, (1 + Complex.I * ((-κ : ℝ) : ℂ) / (N : ℂ) / (z - (q j : ℂ)))

/-- Limit symbol `s = A + e/A`, `A = e^{iκG}`, `e(z) = e^{iLz}`. -/
noncomputable def sLimsrc (κ L : ℝ) (μ : Measure ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * (κ : ℂ) * Gfull μ z)
    + Complex.exp (Complex.I * (L : ℂ) * z) / Complex.exp (Complex.I * (κ : ℂ) * Gfull μ z)

lemma one_add_ne_zero_of_norm_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) : 1 + w ≠ 0 := by
  intro h
  have hw1 : w = -1 := by linear_combination h
  rw [hw1, norm_neg, norm_one] at hw
  norm_num at hw

lemma prod_one_add_eq_exp {N : ℕ} (w : Fin N → ℂ) (hw : ∀ j, 1 + w j ≠ 0) :
    ∏ j, (1 + w j) = Complex.exp (∑ j, Complex.log (1 + w j)) := by
  rw [Complex.exp_sum]
  exact Finset.prod_congr rfl fun j _ => (Complex.exp_log (hw j)).symm

lemma coeff_norm_le (N : ℕ) (c z : ℂ) (q : ℝ) {d : ℝ} (hd0 : 0 < d) (hd : d ≤ ‖z - (q : ℂ)‖) :
    ‖(c / (N : ℂ)) / (z - (q : ℂ))‖ ≤ (‖c‖ / (N : ℝ)) / d := by
  have hcN : ‖c / (N : ℂ)‖ = ‖c‖ / (N : ℝ) := by rw [norm_div, Complex.norm_natCast]
  rw [norm_div, hcN]
  exact div_le_div_of_nonneg_left (by positivity) hd0 hd

/-- Taylor-log sum with uniform separation `d ≤ |z − q_j|` and `‖c‖/N ≤ d/2`. -/
lemma logSum_GN_approx_dist {N : ℕ} (hN : N ≠ 0) (q : Fin N → ℝ) (c z : ℂ) {d : ℝ}
    (hd0 : 0 < d) (hd : ∀ j, d ≤ ‖z - (q j : ℂ)‖) (hc : ‖c‖ / (N : ℝ) ≤ d / 2) :
    ‖(∑ j, Complex.log (1 + (c / (N : ℂ)) / (z - (q j : ℂ)))) - c * GN q z‖
      ≤ ‖c‖ ^ 2 / ((N : ℝ) * d ^ 2) := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hdne : d ≠ 0 := hd0.ne'
  have hnorm : ∀ j, ‖(c / (N : ℂ)) / (z - (q j : ℂ))‖ ≤ (‖c‖ / (N : ℝ)) / d :=
    fun j => coeff_norm_le N c z (q j) hd0 (hd j)
  have hw : ∀ j, ‖(c / (N : ℂ)) / (z - (q j : ℂ))‖ ≤ 1 / 2 := by
    intro j
    refine (hnorm j).trans ?_
    rw [div_le_iff₀ hd0]
    linarith
  have hsum : ∑ j, (c / (N : ℂ)) / (z - (q j : ℂ)) = c * GN q z := by
    unfold GN
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have key : ∑ j, (Complex.log (1 + (c / (N : ℂ)) / (z - (q j : ℂ)))
      - (c / (N : ℂ)) / (z - (q j : ℂ)))
      = (∑ j, Complex.log (1 + (c / (N : ℂ)) / (z - (q j : ℂ)))) - c * GN q z := by
    rw [Finset.sum_sub_distrib, hsum]
  have hbound := logTaylor_sum_le (fun j => (c / (N : ℂ)) / (z - (q j : ℂ))) hw
  have hsq : ∑ j, ‖(c / (N : ℂ)) / (z - (q j : ℂ))‖ ^ 2 ≤ ‖c‖ ^ 2 / ((N : ℝ) * d ^ 2) := by
    calc ∑ j, ‖(c / (N : ℂ)) / (z - (q j : ℂ))‖ ^ 2
        ≤ ∑ _j : Fin N, ((‖c‖ / (N : ℝ)) / d) ^ 2 :=
          Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hnorm j) 2
      _ = (N : ℝ) * ((‖c‖ / (N : ℝ)) / d) ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ‖c‖ ^ 2 / ((N : ℝ) * d ^ 2) := by
          field_simp
  rw [← key]
  exact hbound.trans hsq

/-- `|exp u − exp v| ≤ 2|u−v|·|exp v|` when `|u−v| ≤ 1`. -/
lemma exp_sub_exp_le {u v : ℂ} (h : ‖u - v‖ ≤ 1) :
    ‖Complex.exp u - Complex.exp v‖ ≤ 2 * ‖u - v‖ * ‖Complex.exp v‖ := by
  have e1 : Complex.exp u = Complex.exp v * Complex.exp (u - v) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have e2 : Complex.exp u - Complex.exp v = Complex.exp v * (Complex.exp (u - v) - 1) := by
    rw [e1]
    ring
  rw [e2, norm_mul]
  calc ‖Complex.exp v‖ * ‖Complex.exp (u - v) - 1‖ ≤ ‖Complex.exp v‖ * (2 * ‖u - v‖) :=
        mul_le_mul_of_nonneg_left (Complex.norm_exp_sub_one_le h) (norm_nonneg _)
    _ = 2 * ‖u - v‖ * ‖Complex.exp v‖ := by ring

/-- `|exp(i c w)| ≤ exp(|c|·|Im w|)` for real `c`. -/
lemma norm_exp_I_mul_re (c : ℝ) (w : ℂ) :
    ‖Complex.exp (Complex.I * (c : ℂ) * w)‖ ≤ Real.exp (|c| * |w.im|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : (Complex.I * (c : ℂ) * w).re = -(c * w.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  calc -(c * w.im) ≤ |c * w.im| := neg_le_abs _
    _ = |c| * |w.im| := abs_mul _ _

/-- Uniform bound on the full Cauchy transform when every point of the support is at distance
at least `r` from `z`. -/
lemma norm_Gfull_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (z : ℂ) {r : ℝ} (hr : 0 < r)
    (hx : ∀ᵐ (x : ℝ) ∂μ, r ≤ ‖z - (x : ℂ)‖) : ‖Gfull μ z‖ ≤ 1 / r := by
  unfold Gfull
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x : ℝ => 1 / (z - (x : ℂ)))
    (C := 1 / r) (by
      filter_upwards [hx] with x hx'
      rw [norm_div, norm_one]
      exact div_le_div_of_nonneg_left zero_le_one hr hx')
  simpa using h

/-- Taylor-log comparison with `exp(i κ' G)`, for either sign `κ'`. -/
lemma prod_exp_close {N : ℕ} (hN : N ≠ 0) (q : Fin N → ℝ) (μ : Measure ℝ) (κ' : ℝ) (z : ℂ)
    {r η : ℝ} (hr : 0 < r) (hd : ∀ j, r ≤ ‖z - (q j : ℂ)‖)
    (hc : |κ'| / (N : ℝ) ≤ r / 2) (hη : ‖GN q z - Gfull μ z‖ ≤ η)
    (hsm : |κ'| ^ 2 / ((N : ℝ) * r ^ 2) + |κ'| * η ≤ 1) :
    ‖(∏ j, (1 + Complex.I * (κ' : ℂ) / (N : ℂ) / (z - (q j : ℂ))))
        - Complex.exp (Complex.I * (κ' : ℂ) * Gfull μ z)‖
      ≤ 2 * (|κ'| ^ 2 / ((N : ℝ) * r ^ 2) + |κ'| * η)
          * ‖Complex.exp (Complex.I * (κ' : ℂ) * Gfull μ z)‖ := by
  have hcn : ‖Complex.I * (κ' : ℂ)‖ = |κ'| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hcN : ‖Complex.I * (κ' : ℂ)‖ / (N : ℝ) ≤ r / 2 := by rw [hcn]; exact hc
  have hw : ∀ j, ‖(Complex.I * (κ' : ℂ) / (N : ℂ)) / (z - (q j : ℂ))‖ ≤ 1 / 2 := by
    intro j
    refine (coeff_norm_le N (Complex.I * (κ' : ℂ)) z (q j) hr (hd j)).trans ?_
    rw [div_le_iff₀ hr]
    linarith
  have hprod : ∏ j, (1 + Complex.I * (κ' : ℂ) / (N : ℂ) / (z - (q j : ℂ)))
      = Complex.exp (∑ j, Complex.log (1 + Complex.I * (κ' : ℂ) / (N : ℂ) / (z - (q j : ℂ)))) :=
    prod_one_add_eq_exp _ fun j => one_add_ne_zero_of_norm_le (hw j)
  rw [hprod]
  have hT := logSum_GN_approx_dist hN q (Complex.I * (κ' : ℂ)) z hr hd hcN
  rw [hcn] at hT
  set u := ∑ j, Complex.log (1 + Complex.I * (κ' : ℂ) / (N : ℂ) / (z - (q j : ℂ))) with hu
  set v := Complex.I * (κ' : ℂ) * Gfull μ z with hv
  have huv : u - v = (u - Complex.I * (κ' : ℂ) * GN q z)
      + Complex.I * (κ' : ℂ) * (GN q z - Gfull μ z) := by
    rw [hv]; ring
  have hnuv : ‖u - v‖ ≤ |κ'| ^ 2 / ((N : ℝ) * r ^ 2) + |κ'| * η := by
    rw [huv]
    refine (norm_add_le _ _).trans (add_le_add hT ?_)
    rw [norm_mul, hcn]
    exact mul_le_mul_of_nonneg_left hη (abs_nonneg _)
  have hle1 : ‖u - v‖ ≤ 1 := hnuv.trans hsm
  have hexp := exp_sub_exp_le hle1
  calc ‖Complex.exp u - Complex.exp v‖ ≤ 2 * ‖u - v‖ * ‖Complex.exp v‖ := hexp
    _ ≤ 2 * (|κ'| ^ 2 / ((N : ℝ) * r ^ 2) + |κ'| * η) * ‖Complex.exp v‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnuv (by norm_num)) (norm_nonneg _)

/-- Points of the neighbourhood of `Γ_N`: uniform distance `≥ r` from the classical support
(a.s.) and from the roots (when `|q_j| ≤ R`), and `|Im z| ≤ h + 2ρ`. -/
lemma nbhd_dist {N : ℕ} (q : Fin N → ℝ) (μ : Measure ℝ) {a h ρ R δ : ℝ} (ha : 0 < a)
    (hρ : 0 < ρ) (hb0 : 0 < h - 2 * ρ) (hsupp : ∀ᵐ x ∂μ, δ ≤ |x - a|)
    (hsuppN : ∀ᵐ x ∂μ, δ ≤ |x + a|) {z : ℂ} (hz : z ∈ NbhdN a h ρ) :
    (∀ᵐ (x : ℝ) ∂μ, rNbhd a h ρ R δ ≤ ‖z - (x : ℂ)‖) ∧
    (∀ j, |q j| ≤ R → rNbhd a h ρ R δ ≤ ‖z - (q j : ℂ)‖) ∧
    |z.im| ≤ h + 2 * ρ := by
  have hr_b : rNbhd a h ρ R δ ≤ h - 2 * ρ := min_le_left _ _
  have hr_d : rNbhd a h ρ R δ ≤ δ - 2 * ρ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hr_a : rNbhd a h ρ R δ ≤ a - 2 * ρ - R := le_trans (min_le_right _ _) (min_le_right _ _)
  have roots_of_re : a - 2 * ρ ≤ |z.re| → ∀ j, |q j| ≤ R →
      rNbhd a h ρ R δ ≤ ‖z - (q j : ℂ)‖ := by
    intro hzr j hj
    refine le_trans hr_a ?_
    have h2 := Complex.abs_re_le_norm (z - (q j : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re] at h2
    have h3 := abs_sub_abs_le_abs_sub z.re (q j)
    linarith
  have real_of_im : h - 2 * ρ ≤ |z.im| → ∀ x : ℝ, rNbhd a h ρ R δ ≤ ‖z - (x : ℂ)‖ := by
    intro hI x
    refine le_trans (le_trans hr_b hI) ?_
    have h2 := Complex.abs_im_le_norm (z - (x : ℂ))
    simpa using h2
  rcases nbhd_cover hρ.le hz with h1 | h1 | h1 | h1
  · -- vertical piece at `+a`
    obtain ⟨hA1, hA2⟩ := h1
    have hzr : a - 2 * ρ ≤ |z.re| := by
      have h1' := abs_sub_abs_le_abs_sub a z.re
      rw [abs_of_pos ha] at h1'
      have h2 : |a - z.re| = |z.re - a| := abs_sub_comm _ _
      linarith
    exact ⟨hsupp.mono fun x hx => le_trans hr_d (srcRect_support_dist a ρ h δ z ⟨hA1, hA2⟩ x hx),
      roots_of_re hzr, hA2⟩
  · -- vertical piece at `−a`
    obtain ⟨hA1, hA2⟩ := h1
    have hzr : a - 2 * ρ ≤ |z.re| := by
      have h1' := abs_sub_abs_le_abs_sub (-a) z.re
      rw [abs_neg, abs_of_pos ha] at h1'
      have h2 : |-a - z.re| = |z.re - -a| := abs_sub_comm _ _
      linarith
    exact ⟨hsuppN.mono fun x hx => le_trans hr_d
        (srcRect_support_dist (-a) ρ h δ z ⟨hA1, hA2⟩ x (by rw [sub_neg_eq_add]; exact hx)),
      roots_of_re hzr, hA2⟩
  · -- upper strip piece
    obtain ⟨c1, c2, c3, c4⟩ := h1
    have hI : h - 2 * ρ ≤ |z.im| := le_trans c3 (le_abs_self _)
    exact ⟨ae_of_all μ (real_of_im hI), fun j _ => real_of_im hI (q j),
      abs_le.mpr ⟨by linarith, c4⟩⟩
  · -- lower strip piece
    obtain ⟨c1, c2, c3, c4⟩ := h1
    have hI : h - 2 * ρ ≤ |z.im| := le_trans (by linarith) (neg_le_abs z.im)
    exact ⟨ae_of_all μ (real_of_im hI), fun j _ => real_of_im hI (q j),
      abs_le.mpr ⟨by linarith, by linarith⟩⟩

/-- **Derivative clause, `j = 0`, on the event `E_N`.** Under the Gneighbor hypotheses, the
Taylor-log step (with `κ/N` coupling, `N` large: `|κ|/N ≤ r/2`) and the smallness regime
`|κ|²/(N r²) + |κ|·η ≤ 1` (with `η` the Gneighbor bound), for every `z` of the neighbourhood of
`Γ_N`:
`|s_N(z) − s(z)| ≤ C₀ (ε + R^{-b} + N^{-1})`, with
`C₀ = 2 e^{|κ|/r} (1 + e^{|L|(h+2ρ)}) max(κ²/r², |κ|·2K)`, `r = rNbhd`, `K = KGN`.
This is `Q7A:eq:derivative` for `j = 0`. Higher `j` are NOT covered here. -/
theorem derivative_j0_on_EN {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (hN : 0 < N) (q : Ω → Fin N → ℝ) (hq : Measurable q)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (m p b : ℕ)
    (η0 δ ρ h H R a ε Cms κ L : ℝ)
    (hη0 : 0 < η0) (hρ : 0 < ρ) (hρδ : ρ < δ / 4) (hηh : η0 ≤ h - 2 * ρ)
    (hb0 : 0 < h - 2 * ρ) (hH : h + 4 * ρ < H) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hRH : 2 * H ≤ R) (hRH1 : 2 * (η0 + 1 + m) ≤ R) (hR2ρ : 2 * ρ < R)
    (ha : 0 < a) (hcut : 2 * R ≤ |a|) (hε : 0 ≤ ε)
    (hμint : Integrable (fun x : ℝ => x ^ (2 * p)) μ)
    (hsupp : ∀ᵐ x ∂μ, δ ≤ |x - a|) (hsuppN : ∀ᵐ x ∂μ, δ ≤ |x + a|)
    (hms : ∀ x y : ℝ, η0 ≤ y → ∫ ω, ‖Gfull μ ((x : ℂ) + (y : ℂ) * Complex.I)
        - GN (q ω) ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 ∂P ≤ Cms / ((N : ℝ) * y ^ 2))
    (hb : b ≤ m + 2) (hb2 : b ≤ 2 * p)
    (hNbig : |κ| / (N : ℝ) ≤ rNbhd a h ρ R δ / 2)
    (hsmall : |κ| ^ 2 / ((N : ℝ) * rNbhd a h ρ R δ ^ 2)
        + |κ| * (2 * KGN η0 δ ρ H Cms m p μ * (ε + 1 / R ^ b)) ≤ 1)
    (ω : Ω) (hω : ω ∈ EN μ q R a ρ h η0 ε m) :
    ∀ z ∈ NbhdN a h ρ, ‖sNsrc κ L (q ω) z - sLimsrc κ L μ z‖ ≤
      2 * Real.exp (|κ| * (1 / rNbhd a h ρ R δ)) * (1 + Real.exp (|L| * (h + 2 * ρ)))
        * max (κ ^ 2 / rNbhd a h ρ R δ ^ 2) (|κ| * (2 * KGN η0 δ ρ H Cms m p μ))
        * (ε + 1 / R ^ b + 1 / (N : ℝ)) := by
  have hacut : 2 * R ≤ a := by rwa [abs_of_pos ha] at hcut
  have hr : 0 < rNbhd a h ρ R δ := by
    unfold rNbhd
    exact lt_min hb0 (lt_min (by linarith) (by linarith))
  have hG := gneighbor_on_EN P hN q hq μ m p b η0 δ ρ h H R a ε Cms hη0 hρ hρδ hηh hb0 hH hR hR1
    hRH hRH1 ha hcut hε hμint hsupp hsuppN hms hb hb2 ω hω
  obtain ⟨hroots, -, -, -⟩ := hω
  intro z hz
  obtain ⟨hGa, hGr, hIm⟩ := nbhd_dist (R := R) (q ω) μ ha hρ hb0 hsupp hsuppN hz
  have hGb : ‖Gfull μ z‖ ≤ 1 / rNbhd a h ρ R δ := norm_Gfull_le μ z hr hGa
  have hd : ∀ j, rNbhd a h ρ R δ ≤ ‖z - (q ω j : ℂ)‖ := fun j => hGr j (hroots j)
  have hη : ‖GN (q ω) z - Gfull μ z‖ ≤ 2 * KGN η0 δ ρ H Cms m p μ * (ε + 1 / R ^ b) := by
    rw [norm_sub_rev]
    exact hG z hz
  have hPp := prod_exp_close hN.ne' (q ω) μ κ z hr hd hNbig hη hsmall
  have hPm := prod_exp_close hN.ne' (q ω) μ (-κ) z hr hd (by rw [abs_neg]; exact hNbig) hη
    (by rw [abs_neg]; exact hsmall)
  rw [abs_neg] at hPm
  have hA : ‖Complex.exp (Complex.I * (κ : ℂ) * Gfull μ z)‖
      ≤ Real.exp (|κ| * (1 / rNbhd a h ρ R δ)) := by
    refine (norm_exp_I_mul_re κ (Gfull μ z)).trans ?_
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans hGb) (abs_nonneg _)
  have hB : ‖Complex.exp (Complex.I * ((-κ : ℝ) : ℂ) * Gfull μ z)‖
      ≤ Real.exp (|κ| * (1 / rNbhd a h ρ R δ)) := by
    refine (norm_exp_I_mul_re (-κ) (Gfull μ z)).trans ?_
    apply Real.exp_le_exp.mpr
    rw [abs_neg]
    exact mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans hGb) (abs_nonneg _)
  have he : ‖Complex.exp (Complex.I * (L : ℂ) * z)‖ ≤ Real.exp (|L| * (h + 2 * ρ)) := by
    refine (norm_exp_I_mul_re L z).trans ?_
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hIm (abs_nonneg _)
  have hsplit : sNsrc κ L (q ω) z - sLimsrc κ L μ z =
      ((∏ j, (1 + Complex.I * (κ : ℂ) / (N : ℂ) / (z - (q ω j : ℂ))))
          - Complex.exp (Complex.I * (κ : ℂ) * Gfull μ z))
        + Complex.exp (Complex.I * (L : ℂ) * z) *
          ((∏ j, (1 + Complex.I * ((-κ : ℝ) : ℂ) / (N : ℂ) / (z - (q ω j : ℂ))))
            - Complex.exp (Complex.I * ((-κ : ℝ) : ℂ) * Gfull μ z)) := by
    have hBeq : Complex.exp (Complex.I * ((-κ : ℝ) : ℂ) * Gfull μ z)
        = (Complex.exp (Complex.I * (κ : ℂ) * Gfull μ z))⁻¹ := by
      rw [← Complex.exp_neg]
      congr 1
      push_cast
      ring
    unfold sNsrc sLimsrc
    rw [hBeq, div_eq_mul_inv]
    ring
  -- arithmetic of the constants
  set r := rNbhd a h ρ R δ with hrdef
  set K := KGN η0 δ ρ H Cms m p μ with hKdef
  set T := |κ| ^ 2 / ((N : ℝ) * r ^ 2) + |κ| * (2 * K * (ε + 1 / R ^ b)) with hTdef
  set C2 := max (κ ^ 2 / r ^ 2) (|κ| * (2 * K)) with hC2def
  have hK1 : 1 ≤ K := le_max_of_le_left (le_max_left _ _)
  have hεR : 0 ≤ ε + 1 / R ^ b := add_nonneg hε (by positivity)
  have hT0 : 0 ≤ T := by
    rw [hTdef]
    have h1 : 0 ≤ |κ| ^ 2 / ((N : ℝ) * r ^ 2) := by positivity
    have h2 : 0 ≤ |κ| * (2 * K * (ε + 1 / R ^ b)) :=
      mul_nonneg (abs_nonneg _) (mul_nonneg (by linarith) hεR)
    exact add_nonneg h1 h2
  have hC2nn : 0 ≤ C2 := le_trans (div_nonneg (sq_nonneg _) (sq_nonneg _)) (le_max_left _ _)
  have e1 : |κ| ^ 2 / ((N : ℝ) * r ^ 2) ≤ C2 * (1 / (N : ℝ)) := by
    have : |κ| ^ 2 / ((N : ℝ) * r ^ 2) = κ ^ 2 / r ^ 2 * (1 / (N : ℝ)) := by
      rw [sq_abs]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have e2 : |κ| * (2 * K * (ε + 1 / R ^ b)) ≤ C2 * (ε + 1 / R ^ b) := by
    have : |κ| * (2 * K * (ε + 1 / R ^ b)) = (|κ| * (2 * K)) * (ε + 1 / R ^ b) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hεR
  have hTle : T ≤ C2 * (ε + 1 / R ^ b + 1 / (N : ℝ)) := by
    have : C2 * (ε + 1 / R ^ b + 1 / (N : ℝ)) = C2 * (ε + 1 / R ^ b) + C2 * (1 / (N : ℝ)) := by
      ring
    rw [this, hTdef]
    linarith
  -- assemble
  have hX0 : 0 ≤ Real.exp (|κ| * (1 / r)) := (Real.exp_pos _).le
  have hY0 : 0 ≤ 1 + Real.exp (|L| * (h + 2 * ρ)) := by
    have := (Real.exp_pos (|L| * (h + 2 * ρ))).le
    linarith
  have hPpS : ‖(∏ j, (1 + Complex.I * (κ : ℂ) / (N : ℂ) / (z - (q ω j : ℂ))))
      - Complex.exp (Complex.I * (κ : ℂ) * Gfull μ z)‖
      ≤ 2 * T * ‖Complex.exp (Complex.I * (κ : ℂ) * Gfull μ z)‖ := hPp
  have hPmS : ‖(∏ j, (1 + Complex.I * ((-κ : ℝ) : ℂ) / (N : ℂ) / (z - (q ω j : ℂ))))
      - Complex.exp (Complex.I * ((-κ : ℝ) : ℂ) * Gfull μ z)‖
      ≤ 2 * T * ‖Complex.exp (Complex.I * ((-κ : ℝ) : ℂ) * Gfull μ z)‖ := hPm
  rw [hsplit]
  calc ‖((∏ j, (1 + Complex.I * (κ : ℂ) / (N : ℂ) / (z - (q ω j : ℂ))))
          - Complex.exp (Complex.I * (κ : ℂ) * Gfull μ z))
        + Complex.exp (Complex.I * (L : ℂ) * z) *
          ((∏ j, (1 + Complex.I * ((-κ : ℝ) : ℂ) / (N : ℂ) / (z - (q ω j : ℂ))))
            - Complex.exp (Complex.I * ((-κ : ℝ) : ℂ) * Gfull μ z))‖
      ≤ ‖(∏ j, (1 + Complex.I * (κ : ℂ) / (N : ℂ) / (z - (q ω j : ℂ))))
          - Complex.exp (Complex.I * (κ : ℂ) * Gfull μ z)‖
        + ‖Complex.exp (Complex.I * (L : ℂ) * z)‖ *
          ‖(∏ j, (1 + Complex.I * ((-κ : ℝ) : ℂ) / (N : ℂ) / (z - (q ω j : ℂ))))
            - Complex.exp (Complex.I * ((-κ : ℝ) : ℂ) * Gfull μ z)‖ :=
        (norm_add_le _ _).trans (le_of_eq (by rw [norm_mul]))
    _ ≤ 2 * T * ‖Complex.exp (Complex.I * (κ : ℂ) * Gfull μ z)‖
        + ‖Complex.exp (Complex.I * (L : ℂ) * z)‖
          * (2 * T * ‖Complex.exp (Complex.I * ((-κ : ℝ) : ℂ) * Gfull μ z)‖) :=
        add_le_add hPpS (mul_le_mul_of_nonneg_left hPmS (norm_nonneg _))
    _ ≤ 2 * T * Real.exp (|κ| * (1 / r)) + Real.exp (|L| * (h + 2 * ρ))
          * (2 * T * Real.exp (|κ| * (1 / r))) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hA (by linarith)
        · exact mul_le_mul he (mul_le_mul_of_nonneg_left hB (by linarith))
            (mul_nonneg (by linarith) (norm_nonneg _)) (Real.exp_pos _).le
    _ = 2 * Real.exp (|κ| * (1 / r)) * (1 + Real.exp (|L| * (h + 2 * ρ))) * T := by ring
    _ ≤ 2 * Real.exp (|κ| * (1 / r)) * (1 + Real.exp (|L| * (h + 2 * ρ))) *
          (C2 * (ε + 1 / R ^ b + 1 / (N : ℝ))) :=
        mul_le_mul_of_nonneg_left hTle (by positivity)
    _ = 2 * Real.exp (|κ| * (1 / r)) * (1 + Real.exp (|L| * (h + 2 * ρ))) * C2
          * (ε + 1 / R ^ b + 1 / (N : ℝ)) := by ring

/-! ## 8. Holomorphy at points with positive distance to the support and the roots;
higher derivatives by Cauchy on the smaller neighbourhood `NbhdN a h (ρ/2)` -/

/-- Holomorphy of the Cauchy transform at `z₀` under a uniform a.e. distance bound `r ≤ |z₀ − x|`
(this covers points off `ℝ` and points on `ℝ` whose distance to the support is positive). -/
lemma Gfull_hasDerivAt_of_dist (μ : Measure ℝ) [IsProbabilityMeasure μ] {z0 : ℂ} {r : ℝ}
    (hr : 0 < r) (hx : ∀ᵐ (x : ℝ) ∂μ, r ≤ ‖z0 - (x : ℂ)‖) :
    HasDerivAt (Gfull μ) (∫ x, -(1 / (z0 - (x : ℂ)) ^ 2) ∂μ) z0 := by
  set d : ℝ := r / 2 with hd
  have hdpos : 0 < d := by rw [hd]; positivity
  have hball : ∀ᵐ (x : ℝ) ∂μ, ∀ w ∈ ball z0 d, d ≤ ‖w - (x : ℂ)‖ := by
    filter_upwards [hx] with x hx' w hw
    rw [mem_ball, dist_eq_norm] at hw
    have h1 : ‖z0 - (x : ℂ)‖ - ‖z0 - w‖ ≤ ‖(z0 - (x : ℂ)) - (z0 - w)‖ := norm_sub_norm_le _ _
    have h2 : (z0 - (x : ℂ)) - (z0 - w) = w - (x : ℂ) := by ring
    rw [h2, norm_sub_rev z0 w] at h1
    linarith
  have hne : ∀ᵐ (x : ℝ) ∂μ, ∀ w ∈ ball z0 d, w - (x : ℂ) ≠ 0 := by
    filter_upwards [hball] with x hx' w hw h0
    have := hx' w hw
    rw [h0, norm_zero] at this
    linarith
  have hmeas : ∀ w : ℂ, Measurable (fun x : ℝ => 1 / (w - (x : ℂ))) := fun w =>
    measurable_const.div (measurable_const.sub Complex.measurable_ofReal)
  have hF0_int : Integrable (fun x : ℝ => 1 / (z0 - (x : ℂ))) μ :=
    Integrable.of_bound (hmeas z0).aestronglyMeasurable (1 / r) (by
      filter_upwards [hx] with x hx'
      rw [norm_div, norm_one]
      exact div_le_div_of_nonneg_left zero_le_one hr hx')
  have hF'_meas : AEStronglyMeasurable (fun x : ℝ => -(1 / (z0 - (x : ℂ)) ^ 2)) μ :=
    ((measurable_const.div ((measurable_const.sub Complex.measurable_ofReal).pow_const 2)).neg
      ).aestronglyMeasurable
  have h_bound : ∀ᵐ (x : ℝ) ∂μ, ∀ w ∈ ball z0 d, ‖-(1 / (w - (x : ℂ)) ^ 2)‖ ≤ 1 / d ^ 2 := by
    filter_upwards [hball] with x hx' w hw
    have h1 := hx' w hw
    rw [norm_neg, norm_div, norm_one, norm_pow]
    exact div_le_div_of_nonneg_left zero_le_one (by positivity) (pow_le_pow_left₀ hdpos.le h1 2)
  have h_diff : ∀ᵐ (x : ℝ) ∂μ, ∀ w ∈ ball z0 d,
      HasDerivAt (fun w' : ℂ => 1 / (w' - (x : ℂ))) (-(1 / (w - (x : ℂ)) ^ 2)) w := by
    filter_upwards [hne] with x hx' w hw
    exact hasDerivAt_one_div_sub_ofReal (hx' w hw)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun (w : ℂ) (x : ℝ) => 1 / (w - (x : ℂ)))
    (F' := fun (w : ℂ) (x : ℝ) => -(1 / (w - (x : ℂ)) ^ 2))
    (x₀ := z0) (s := ball z0 d) (bound := fun _ => 1 / d ^ 2)
    (ball_mem_nhds z0 hdpos)
    (Filter.Eventually.of_forall fun w => (hmeas w).aestronglyMeasurable)
    hF0_int hF'_meas h_bound (integrable_const _) h_diff
  exact key.2

/-- Points of `NbhdN a h ρ₁` shifted by at most `ρ₂` lie in `NbhdN a h (ρ₁ + ρ₂)`. -/
lemma NbhdN_add {a h ρ₁ ρ₂ : ℝ} {z w : ℂ} (hz : z ∈ NbhdN a h ρ₁) (hw : ‖w - z‖ ≤ ρ₂) :
    w ∈ NbhdN a h (ρ₁ + ρ₂) := by
  obtain ⟨v, hv, hd⟩ := hz
  refine ⟨v, hv, ?_⟩
  have e : w - v = (w - z) + (z - v) := by ring
  rw [e]
  exact (norm_add_le _ _).trans (by linarith)

/-- The transfer symbol difference `s_N − s` is holomorphic at every point where the distance to the
classical support and to the roots is bounded below by `r > 0`. -/
lemma sNsrc_sLimsrc_differentiableAt {N : ℕ} (κ L : ℝ) (q : Fin N → ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {w : ℂ} {r : ℝ} (hr : 0 < r)
    (hx : ∀ᵐ (x : ℝ) ∂μ, r ≤ ‖w - (x : ℂ)‖) (hq : ∀ j, r ≤ ‖w - (q j : ℂ)‖) (_hN : N ≠ 0) :
    DifferentiableAt ℂ (fun w' => sNsrc κ L q w' - sLimsrc κ L μ w') w := by
  have hne : ∀ j, w - (q j : ℂ) ≠ 0 := fun j h0 => by
    have := hq j
    rw [h0, norm_zero] at this
    linarith
  have hG : DifferentiableAt ℂ (Gfull μ) w := (Gfull_hasDerivAt_of_dist μ hr hx).differentiableAt
  have hexpG : DifferentiableAt ℂ (fun w' => Complex.exp (Complex.I * (κ : ℂ) * Gfull μ w')) w :=
    (hG.const_mul (Complex.I * (κ : ℂ))).cexp
  have hexpL : DifferentiableAt ℂ (fun w' => Complex.exp (Complex.I * (L : ℂ) * w')) w :=
    ((differentiableAt_id.const_mul (Complex.I * (L : ℂ))).cexp)
  have hprod : ∀ c : ℂ, DifferentiableAt ℂ
      (fun w' => ∏ j, (1 + c / (N : ℂ) / (w' - (q j : ℂ)))) w := by
    intro c
    refine DifferentiableAt.fun_finsetProd (fun j _ => ?_)
    exact (differentiableAt_const _).add
      ((differentiableAt_const _).div (differentiableAt_id.sub_const _) (hne j))
  have hP := hprod (Complex.I * (κ : ℂ))
  have hM := hprod (Complex.I * ((-κ : ℝ) : ℂ))
  have hsN : DifferentiableAt ℂ (fun w' => sNsrc κ L q w') w := by
    unfold sNsrc
    exact hP.add (hexpL.mul hM)
  have hsA : DifferentiableAt ℂ (fun w' => sLimsrc κ L μ w') w := by
    unfold sLimsrc
    exact hexpG.add (hexpL.div hexpG (Complex.exp_ne_zero _))
  exact hsN.sub hsA

/-- **Derivative clause, all orders `j`, on the smaller neighbourhood.** Under the same hypotheses
as `derivative_j0_on_EN`, for `z ∈ NbhdN a h (ρ/2)` (a genuinely smaller set: circles of radius
`ρ/2` about `z` stay in `NbhdN a h ρ`, where the `j = 0` bound holds), Cauchy's estimate gives
`|∂_z^n (s_N − s)(z)| ≤ n! · C₀ (ε + R^{-b} + N^{-1}) / (ρ/2)^n`, with `C₀` the constant of
`derivative_j0_on_EN`. Holomorphy at each point of the closed circle ball is proved from
`nbhd_dist` (distance to the classical support and the roots). -/
theorem derivative_jn_on_smaller {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    {N : ℕ} (hN : 0 < N) (q : Ω → Fin N → ℝ) (hq : Measurable q)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (m p b : ℕ)
    (η0 δ ρ h H R a ε Cms κ L : ℝ)
    (hη0 : 0 < η0) (hρ : 0 < ρ) (hρδ : ρ < δ / 4) (hηh : η0 ≤ h - 2 * ρ)
    (hb0 : 0 < h - 2 * ρ) (hH : h + 4 * ρ < H) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hRH : 2 * H ≤ R) (hRH1 : 2 * (η0 + 1 + m) ≤ R) (hR2ρ : 2 * ρ < R)
    (ha : 0 < a) (hcut : 2 * R ≤ |a|) (hε : 0 ≤ ε)
    (hμint : Integrable (fun x : ℝ => x ^ (2 * p)) μ)
    (hsupp : ∀ᵐ x ∂μ, δ ≤ |x - a|) (hsuppN : ∀ᵐ x ∂μ, δ ≤ |x + a|)
    (hms : ∀ x y : ℝ, η0 ≤ y → ∫ ω, ‖Gfull μ ((x : ℂ) + (y : ℂ) * Complex.I)
        - GN (q ω) ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 ∂P ≤ Cms / ((N : ℝ) * y ^ 2))
    (hb : b ≤ m + 2) (hb2 : b ≤ 2 * p)
    (hNbig : |κ| / (N : ℝ) ≤ rNbhd a h ρ R δ / 2)
    (hsmall : |κ| ^ 2 / ((N : ℝ) * rNbhd a h ρ R δ ^ 2)
        + |κ| * (2 * KGN η0 δ ρ H Cms m p μ * (ε + 1 / R ^ b)) ≤ 1)
    (ω : Ω) (hω : ω ∈ EN μ q R a ρ h η0 ε m) :
    ∀ z ∈ NbhdN a h (ρ / 2), ∀ n : ℕ,
      ‖iteratedDeriv n (fun w => sNsrc κ L (q ω) w - sLimsrc κ L μ w) z‖ ≤
        n.factorial * (2 * Real.exp (|κ| * (1 / rNbhd a h ρ R δ)) * (1 + Real.exp (|L| * (h + 2 * ρ)))
          * max (κ ^ 2 / rNbhd a h ρ R δ ^ 2) (|κ| * (2 * KGN η0 δ ρ H Cms m p μ))
          * (ε + 1 / R ^ b + 1 / (N : ℝ))) / (ρ / 2) ^ n := by
  have hroots : ∀ j, |q ω j| ≤ R := by
    obtain ⟨h1, -⟩ := hω
    exact h1
  have hr : 0 < rNbhd a h ρ R δ := by
    have hacut : 2 * R ≤ a := by rwa [abs_of_pos ha] at hcut
    unfold rNbhd
    exact lt_min hb0 (lt_min (by linarith) (by linarith))
  -- holomorphy and the `j = 0` bound on the closed circle balls
  have hdiff : ∀ z ∈ NbhdN a h (ρ / 2), ∀ w ∈ closedBall z (ρ / 2),
      DifferentiableAt ℂ (fun w' => sNsrc κ L (q ω) w' - sLimsrc κ L μ w') w ∧
      w ∈ NbhdN a h ρ := by
    intro z hz w hw
    have hwd : ‖w - z‖ ≤ ρ / 2 := by
      rw [mem_closedBall, dist_eq_norm] at hw
      exact hw
    have hwN : w ∈ NbhdN a h (ρ / 2 + ρ / 2) := NbhdN_add hz hwd
    rw [show ρ / 2 + ρ / 2 = ρ by ring] at hwN
    obtain ⟨hGa, hGr, -⟩ := nbhd_dist (R := R) (q ω) μ ha hρ hb0 hsupp hsuppN hwN
    exact ⟨sNsrc_sLimsrc_differentiableAt κ L (q ω) μ hr hGa (fun j => hGr j (hroots j)) hN.ne',
      hwN⟩
  intro z hz n
  have ht : 0 < ρ / 2 := half_pos hρ
  have hf : DiffContOnCl ℂ (fun w => sNsrc κ L (q ω) w - sLimsrc κ L μ w) (ball z (ρ / 2)) :=
    ⟨fun w hw => (hdiff z hz w (ball_subset_closedBall hw)).1.differentiableWithinAt,
      fun w hw => (hdiff z hz w (closure_ball_subset_closedBall hw)).1.continuousAt.continuousWithinAt⟩
  have hC : ∀ w ∈ sphere z (ρ / 2), ‖(fun w => sNsrc κ L (q ω) w - sLimsrc κ L μ w) w‖ ≤
      2 * Real.exp (|κ| * (1 / rNbhd a h ρ R δ)) * (1 + Real.exp (|L| * (h + 2 * ρ)))
        * max (κ ^ 2 / rNbhd a h ρ R δ ^ 2) (|κ| * (2 * KGN η0 δ ρ H Cms m p μ))
        * (ε + 1 / R ^ b + 1 / (N : ℝ)) := by
    intro w hw
    have hwN : w ∈ NbhdN a h ρ := (hdiff z hz w (sphere_subset_closedBall hw)).2
    exact derivative_j0_on_EN P hN q hq μ m p b η0 δ ρ h H R a ε Cms κ L hη0 hρ hρδ hηh hb0 hH
      hR hR1 hRH hRH1 hR2ρ ha hcut hε hμint hsupp hsuppN hms hb hb2 hNbig hsmall ω hω w hwN
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n ht hf hC

/-! ## 9. Quantifier repair: Lipschitz bounds without smallness; constants in a fixed radius `r`

These are additive: the earlier theorems (with `hsmall`, `rNbhd`) are kept unchanged. The new
versions take a radius `r` with `0 < r ≤ rNbhd a h ρ R δ`; the constants then depend on `r` only.
No smallness of `ε`, `R`, or `|κ|²/N` is needed (the exponential Lipschitz bound below replaces the
earlier `‖u − v‖ ≤ 1` hypothesis). -/

/-- `|exp u − exp v| ≤ exp(max(Re u, Re v))·|u − v|`, for all `u v : ℂ`. -/
lemma exp_sub_exp_le_max (u v : ℂ) :
    ‖Complex.exp u - Complex.exp v‖ ≤ Real.exp (max u.re v.re) * ‖u - v‖ := by
  have hbd : ∀ x ∈ segment ℝ v u, ‖deriv Complex.exp x‖ ≤ Real.exp (max u.re v.re) := by
    intro x hx
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hx
    rw [Complex.deriv_exp, Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have h1 : v.re ≤ max u.re v.re := le_max_right _ _
    have h2 : u.re ≤ max u.re v.re := le_max_left _ _
    have hM : a * max u.re v.re + b * max u.re v.re = max u.re v.re := by
      rw [← add_mul, hab, one_mul]
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    linarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb, hM]
  exact Convex.norm_image_sub_le_of_norm_deriv_le (fun _ _ => Complex.differentiableAt_exp) hbd
    (convex_segment v u) (left_mem_segment ℝ v u) (right_mem_segment ℝ v u)

/-- `Re log(1+w) ≤ ‖w‖` for `‖w‖ ≤ 1/2`. -/
lemma re_log_one_add_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) : (Complex.log (1 + w)).re ≤ ‖w‖ := by
  rw [Complex.log_re]
  have hpos : 0 < ‖1 + w‖ := norm_pos_iff.mpr (one_add_ne_zero_of_norm_le hw)
  have h1 : Real.log ‖1 + w‖ ≤ ‖1 + w‖ - 1 := Real.log_le_sub_one_of_pos hpos
  have h2 : ‖1 + w‖ ≤ 1 + ‖w‖ := by
    have := norm_add_le (1 : ℂ) w
    rwa [norm_one] at this
  linarith

/-- Taylor comparison with `exp(i κ' G)` without any smallness of `|κ'|²/N` or `η`:
`‖∏(1 + i κ'/(N(z−q_j))) − exp(iκ'G(z))‖ ≤ exp(|κ'|/r)·(κ'²/(N r²) + |κ'| η)`. -/
lemma prod_exp_close_lip {N : ℕ} (hN : N ≠ 0) (q : Fin N → ℝ) (μ : Measure ℝ) (κ' : ℝ) (z : ℂ)
    {r η : ℝ} (hr : 0 < r) (hd : ∀ j, r ≤ ‖z - (q j : ℂ)‖)
    (hc : |κ'| / (N : ℝ) ≤ r / 2) (hη : ‖GN q z - Gfull μ z‖ ≤ η)
    (hG : ‖Gfull μ z‖ ≤ 1 / r) :
    ‖(∏ j, (1 + Complex.I * (κ' : ℂ) / (N : ℂ) / (z - (q j : ℂ))))
        - Complex.exp (Complex.I * (κ' : ℂ) * Gfull μ z)‖
      ≤ Real.exp (|κ'| / r) * (|κ'| ^ 2 / ((N : ℝ) * r ^ 2) + |κ'| * η) := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hcn : ‖Complex.I * (κ' : ℂ)‖ = |κ'| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hcN : ‖Complex.I * (κ' : ℂ)‖ / (N : ℝ) ≤ r / 2 := by rw [hcn]; exact hc
  have hw : ∀ j, ‖(Complex.I * (κ' : ℂ) / (N : ℂ)) / (z - (q j : ℂ))‖ ≤ 1 / 2 := by
    intro j
    refine (coeff_norm_le N (Complex.I * (κ' : ℂ)) z (q j) hr (hd j)).trans ?_
    rw [div_le_iff₀ hr]
    linarith
  have hprod : ∏ j, (1 + Complex.I * (κ' : ℂ) / (N : ℂ) / (z - (q j : ℂ)))
      = Complex.exp (∑ j, Complex.log (1 + Complex.I * (κ' : ℂ) / (N : ℂ) / (z - (q j : ℂ)))) :=
    prod_one_add_eq_exp _ fun j => one_add_ne_zero_of_norm_le (hw j)
  rw [hprod]
  have hT := logSum_GN_approx_dist hN q (Complex.I * (κ' : ℂ)) z hr hd hcN
  rw [hcn] at hT
  have hure : (∑ j, Complex.log (1 + Complex.I * (κ' : ℂ) / (N : ℂ) / (z - (q j : ℂ)))).re
      ≤ |κ'| / r := by
    rw [Complex.re_sum]
    calc ∑ j, (Complex.log (1 + Complex.I * (κ' : ℂ) / (N : ℂ) / (z - (q j : ℂ)))).re
        ≤ ∑ j, ‖(Complex.I * (κ' : ℂ) / (N : ℂ)) / (z - (q j : ℂ))‖ :=
          Finset.sum_le_sum fun j _ => re_log_one_add_le (hw j)
      _ ≤ ∑ _j : Fin N, (|κ'| / (N : ℝ)) / r := by
          refine Finset.sum_le_sum fun j _ => ?_
          have h1 := coeff_norm_le N (Complex.I * (κ' : ℂ)) z (q j) hr (hd j)
          rw [hcn] at h1
          exact h1
      _ = |κ'| / r := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  have hvre : (Complex.I * (κ' : ℂ) * Gfull μ z).re ≤ |κ'| / r := by
    have hre : (Complex.I * (κ' : ℂ) * Gfull μ z).re = -(κ' * (Gfull μ z).im) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    calc -(κ' * (Gfull μ z).im) ≤ |κ' * (Gfull μ z).im| := neg_le_abs _
      _ = |κ'| * |(Gfull μ z).im| := abs_mul _ _
      _ ≤ |κ'| * (1 / r) :=
          mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans hG) (abs_nonneg _)
      _ = |κ'| / r := by ring
  have hnuv : ‖(∑ j, Complex.log (1 + Complex.I * (κ' : ℂ) / (N : ℂ) / (z - (q j : ℂ))))
      - Complex.I * (κ' : ℂ) * Gfull μ z‖ ≤ |κ'| ^ 2 / ((N : ℝ) * r ^ 2) + |κ'| * η := by
    have huv : (∑ j, Complex.log (1 + Complex.I * (κ' : ℂ) / (N : ℂ) / (z - (q j : ℂ))))
        - Complex.I * (κ' : ℂ) * Gfull μ z
        = ((∑ j, Complex.log (1 + Complex.I * (κ' : ℂ) / (N : ℂ) / (z - (q j : ℂ))))
            - Complex.I * (κ' : ℂ) * GN q z)
          + Complex.I * (κ' : ℂ) * (GN q z - Gfull μ z) := by ring
    rw [huv]
    refine (norm_add_le _ _).trans (add_le_add hT ?_)
    rw [norm_mul, hcn]
    exact mul_le_mul_of_nonneg_left hη (abs_nonneg _)
  have key := exp_sub_exp_le_max (∑ j, Complex.log (1 + Complex.I * (κ' : ℂ) / (N : ℂ) / (z - (q j : ℂ))))
    (Complex.I * (κ' : ℂ) * Gfull μ z)
  have hmax := max_le hure hvre
  exact key.trans (mul_le_mul (Real.exp_le_exp.mpr hmax) hnuv (norm_nonneg _) (Real.exp_pos _).le)

/-- `|∏ … − …|` constant algebra: `|κ|²/(N r²) + |κ|·2K(ε+x) ≤ C₂ (ε + x + 1/N)` with
`C₂ = max(κ²/r², |κ|·2K)`. -/
lemma T_le_C2 {κ r K ε x : ℝ} {N : ℕ} (hN : 0 < N) (hr : 0 < r) (hK : 0 ≤ K) (hε : 0 ≤ ε + x)
    (hx : 0 ≤ x) :
    |κ| ^ 2 / ((N : ℝ) * r ^ 2) + |κ| * (2 * K * (ε + x))
      ≤ max (κ ^ 2 / r ^ 2) (|κ| * (2 * K)) * (ε + x + 1 / (N : ℝ)) := by
  set C2 := max (κ ^ 2 / r ^ 2) (|κ| * (2 * K)) with hC2
  have hC2nn : 0 ≤ C2 := le_trans (div_nonneg (sq_nonneg _) (sq_nonneg _)) (le_max_left _ _)
  have e1 : |κ| ^ 2 / ((N : ℝ) * r ^ 2) ≤ C2 * (1 / (N : ℝ)) := by
    have : |κ| ^ 2 / ((N : ℝ) * r ^ 2) = κ ^ 2 / r ^ 2 * (1 / (N : ℝ)) := by
      rw [sq_abs]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have e2 : |κ| * (2 * K * (ε + x)) ≤ C2 * (ε + x) := by
    have : |κ| * (2 * K * (ε + x)) = (|κ| * (2 * K)) * (ε + x) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hε
  have e3 : C2 * (ε + x + 1 / (N : ℝ)) = C2 * (ε + x) + C2 * (1 / (N : ℝ)) := by ring
  rw [e3]
  linarith

/-- **Derivative clause, `j = 0`, fixed-radius constants.** For any radius `0 < r ≤ rNbhd`
and `N` with `|κ|/N ≤ r/2` (no smallness of `ε`, `R`, `N` beyond this), for every `z` of the
neighbourhood of `Γ_N` on `E_N`:
`|s_N(z) − s(z)| ≤ e^{|κ|/r}(1 + e^{|L|(h+2ρ)}) max(κ²/r², |κ|·2K)(ε + R^{-b} + N^{-1})`. -/
theorem derivative_j0_on_EN_r {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    {N : ℕ} (hN : 0 < N) (q : Ω → Fin N → ℝ) (hq : Measurable q)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (m p b : ℕ)
    (η0 δ ρ h H R a ε Cms κ L r : ℝ)
    (hη0 : 0 < η0) (hρ : 0 < ρ) (hρδ : ρ < δ / 4) (hηh : η0 ≤ h - 2 * ρ)
    (hb0 : 0 < h - 2 * ρ) (hH : h + 4 * ρ < H) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hRH : 2 * H ≤ R) (hRH1 : 2 * (η0 + 1 + m) ≤ R) (hR2ρ : 2 * ρ < R)
    (ha : 0 < a) (hcut : 2 * R ≤ |a|) (hε : 0 ≤ ε)
    (hμint : Integrable (fun x : ℝ => x ^ (2 * p)) μ)
    (hsupp : ∀ᵐ x ∂μ, δ ≤ |x - a|) (hsuppN : ∀ᵐ x ∂μ, δ ≤ |x + a|)
    (hms : ∀ x y : ℝ, η0 ≤ y → ∫ ω, ‖Gfull μ ((x : ℂ) + (y : ℂ) * Complex.I)
        - GN (q ω) ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 ∂P ≤ Cms / ((N : ℝ) * y ^ 2))
    (hb : b ≤ m + 2) (hb2 : b ≤ 2 * p)
    (hr : 0 < r) (hr_le : r ≤ rNbhd a h ρ R δ)
    (hNbig : |κ| / (N : ℝ) ≤ r / 2)
    (ω : Ω) (hω : ω ∈ EN μ q R a ρ h η0 ε m) :
    ∀ z ∈ NbhdN a h ρ, ‖sNsrc κ L (q ω) z - sLimsrc κ L μ z‖ ≤
      Real.exp (|κ| / r) * (1 + Real.exp (|L| * (h + 2 * ρ)))
        * max (κ ^ 2 / r ^ 2) (|κ| * (2 * KGN η0 δ ρ H Cms m p μ))
        * (ε + 1 / R ^ b + 1 / (N : ℝ)) := by
  have hG := gneighbor_on_EN P hN q hq μ m p b η0 δ ρ h H R a ε Cms hη0 hρ hρδ hηh hb0 hH hR hR1
    hRH hRH1 ha hcut hε hμint hsupp hsuppN hms hb hb2 ω hω
  have hroots : ∀ j, |q ω j| ≤ R := by
    obtain ⟨h1, -⟩ := hω
    exact h1
  intro z hz
  obtain ⟨hGa, hGr, hIm⟩ := nbhd_dist (R := R) (q ω) μ ha hρ hb0 hsupp hsuppN hz
  have hGb : ‖Gfull μ z‖ ≤ 1 / r :=
    (norm_Gfull_le μ z (lt_of_lt_of_le hr hr_le) hGa).trans (one_div_le_one_div_of_le hr hr_le)
  have hd : ∀ j, r ≤ ‖z - (q ω j : ℂ)‖ := fun j => le_trans hr_le (hGr j (hroots j))
  have hη : ‖GN (q ω) z - Gfull μ z‖ ≤ 2 * KGN η0 δ ρ H Cms m p μ * (ε + 1 / R ^ b) := by
    rw [norm_sub_rev]
    exact hG z hz
  have hPp := prod_exp_close_lip hN.ne' (q ω) μ κ z hr hd hNbig hη hGb
  have hPm := prod_exp_close_lip hN.ne' (q ω) μ (-κ) z hr hd (by rw [abs_neg]; exact hNbig) hη hGb
  rw [abs_neg] at hPm
  have he : ‖Complex.exp (Complex.I * (L : ℂ) * z)‖ ≤ Real.exp (|L| * (h + 2 * ρ)) := by
    refine (norm_exp_I_mul_re L z).trans (Real.exp_le_exp.mpr ?_)
    exact mul_le_mul_of_nonneg_left hIm (abs_nonneg _)
  have hsplit : sNsrc κ L (q ω) z - sLimsrc κ L μ z =
      ((∏ j, (1 + Complex.I * (κ : ℂ) / (N : ℂ) / (z - (q ω j : ℂ))))
          - Complex.exp (Complex.I * (κ : ℂ) * Gfull μ z))
        + Complex.exp (Complex.I * (L : ℂ) * z) *
          ((∏ j, (1 + Complex.I * ((-κ : ℝ) : ℂ) / (N : ℂ) / (z - (q ω j : ℂ))))
            - Complex.exp (Complex.I * ((-κ : ℝ) : ℂ) * Gfull μ z)) := by
    have hBeq : Complex.exp (Complex.I * ((-κ : ℝ) : ℂ) * Gfull μ z)
        = (Complex.exp (Complex.I * (κ : ℂ) * Gfull μ z))⁻¹ := by
      rw [← Complex.exp_neg]
      congr 1
      push_cast
      ring
    unfold sNsrc sLimsrc
    rw [hBeq, div_eq_mul_inv]
    ring
  set K := KGN η0 δ ρ H Cms m p μ with hKdef
  have hK0 : 0 ≤ K := le_trans zero_le_one (le_trans (le_max_left _ _) (le_max_left _ _))
  have hεR : 0 ≤ ε + 1 / R ^ b := add_nonneg hε (by positivity)
  have hT := T_le_C2 (κ := κ) (r := r) (K := K) (ε := ε) (x := 1 / R ^ b) hN hr hK0 hεR
    (by positivity)
  have hX0 : 0 ≤ Real.exp (|κ| / r) := (Real.exp_pos _).le
  have hY0 : 0 ≤ 1 + Real.exp (|L| * (h + 2 * ρ)) := by
    have := (Real.exp_pos (|L| * (h + 2 * ρ))).le
    linarith
  have hPpS : ‖(∏ j, (1 + Complex.I * (κ : ℂ) / (N : ℂ) / (z - (q ω j : ℂ))))
      - Complex.exp (Complex.I * (κ : ℂ) * Gfull μ z)‖
      ≤ Real.exp (|κ| / r) * (|κ| ^ 2 / ((N : ℝ) * r ^ 2) + |κ| * (2 * K * (ε + 1 / R ^ b)))
        := by
    have := hPp
    have hη' : |κ| * ‖GN (q ω) z - Gfull μ z‖ ≤ |κ| * (2 * K * (ε + 1 / R ^ b)) :=
      mul_le_mul_of_nonneg_left hη (abs_nonneg _)
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_left (by linarith) hX0
  have hPmS : ‖(∏ j, (1 + Complex.I * ((-κ : ℝ) : ℂ) / (N : ℂ) / (z - (q ω j : ℂ))))
      - Complex.exp (Complex.I * ((-κ : ℝ) : ℂ) * Gfull μ z)‖
      ≤ Real.exp (|κ| / r) * (|κ| ^ 2 / ((N : ℝ) * r ^ 2) + |κ| * (2 * K * (ε + 1 / R ^ b))) := by
    refine hPm.trans ?_
    exact mul_le_mul_of_nonneg_left (by linarith) hX0
  -- the exponential factor
  have hTle : |κ| ^ 2 / ((N : ℝ) * r ^ 2) + |κ| * (2 * K * (ε + 1 / R ^ b))
      ≤ max (κ ^ 2 / r ^ 2) (|κ| * (2 * K)) * (ε + 1 / R ^ b + 1 / (N : ℝ)) := hT
  have hXT : 0 ≤ |κ| ^ 2 / ((N : ℝ) * r ^ 2) + |κ| * (2 * K * (ε + 1 / R ^ b)) := by
    have h1 : 0 ≤ |κ| ^ 2 / ((N : ℝ) * r ^ 2) := by positivity
    have h2 : 0 ≤ |κ| * (2 * K * (ε + 1 / R ^ b)) :=
      mul_nonneg (abs_nonneg _) (mul_nonneg (by linarith) hεR)
    linarith
  rw [hsplit]
  calc ‖((∏ j, (1 + Complex.I * (κ : ℂ) / (N : ℂ) / (z - (q ω j : ℂ))))
          - Complex.exp (Complex.I * (κ : ℂ) * Gfull μ z))
        + Complex.exp (Complex.I * (L : ℂ) * z) *
          ((∏ j, (1 + Complex.I * ((-κ : ℝ) : ℂ) / (N : ℂ) / (z - (q ω j : ℂ))))
            - Complex.exp (Complex.I * ((-κ : ℝ) : ℂ) * Gfull μ z))‖
      ≤ ‖(∏ j, (1 + Complex.I * (κ : ℂ) / (N : ℂ) / (z - (q ω j : ℂ))))
          - Complex.exp (Complex.I * (κ : ℂ) * Gfull μ z)‖
        + ‖Complex.exp (Complex.I * (L : ℂ) * z)‖ *
          ‖(∏ j, (1 + Complex.I * ((-κ : ℝ) : ℂ) / (N : ℂ) / (z - (q ω j : ℂ))))
            - Complex.exp (Complex.I * ((-κ : ℝ) : ℂ) * Gfull μ z)‖ :=
        (norm_add_le _ _).trans (le_of_eq (by rw [norm_mul]))
    _ ≤ Real.exp (|κ| / r) * (|κ| ^ 2 / ((N : ℝ) * r ^ 2) + |κ| * (2 * K * (ε + 1 / R ^ b)))
        + Real.exp (|L| * (h + 2 * ρ)) *
          (Real.exp (|κ| / r) * (|κ| ^ 2 / ((N : ℝ) * r ^ 2) + |κ| * (2 * K * (ε + 1 / R ^ b)))) :=
        add_le_add hPpS (mul_le_mul he hPmS (norm_nonneg _) (Real.exp_pos _).le)
    _ = Real.exp (|κ| / r) * (1 + Real.exp (|L| * (h + 2 * ρ)))
          * (|κ| ^ 2 / ((N : ℝ) * r ^ 2) + |κ| * (2 * K * (ε + 1 / R ^ b))) := by ring
    _ ≤ Real.exp (|κ| / r) * (1 + Real.exp (|L| * (h + 2 * ρ)))
          * (max (κ ^ 2 / r ^ 2) (|κ| * (2 * K)) * (ε + 1 / R ^ b + 1 / (N : ℝ))) :=
        mul_le_mul_of_nonneg_left hTle (mul_nonneg hX0 hY0)
    _ = Real.exp (|κ| / r) * (1 + Real.exp (|L| * (h + 2 * ρ)))
        * max (κ ^ 2 / r ^ 2) (|κ| * (2 * K)) * (ε + 1 / R ^ b + 1 / (N : ℝ)) := by ring

/-- **Derivative clause, all orders `n`, fixed-radius constants**, on the smaller neighbourhood
`NbhdN a h (ρ/2)`, by Cauchy on circles of radius `ρ/2` (inside `NbhdN a h ρ`). -/
theorem derivative_jn_on_smaller_r {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    {N : ℕ} (hN : 0 < N) (q : Ω → Fin N → ℝ) (hq : Measurable q)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (m p b : ℕ)
    (η0 δ ρ h H R a ε Cms κ L r : ℝ)
    (hη0 : 0 < η0) (hρ : 0 < ρ) (hρδ : ρ < δ / 4) (hηh : η0 ≤ h - 2 * ρ)
    (hb0 : 0 < h - 2 * ρ) (hH : h + 4 * ρ < H) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hRH : 2 * H ≤ R) (hRH1 : 2 * (η0 + 1 + m) ≤ R) (hR2ρ : 2 * ρ < R)
    (ha : 0 < a) (hcut : 2 * R ≤ |a|) (hε : 0 ≤ ε)
    (hμint : Integrable (fun x : ℝ => x ^ (2 * p)) μ)
    (hsupp : ∀ᵐ x ∂μ, δ ≤ |x - a|) (hsuppN : ∀ᵐ x ∂μ, δ ≤ |x + a|)
    (hms : ∀ x y : ℝ, η0 ≤ y → ∫ ω, ‖Gfull μ ((x : ℂ) + (y : ℂ) * Complex.I)
        - GN (q ω) ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 ∂P ≤ Cms / ((N : ℝ) * y ^ 2))
    (hb : b ≤ m + 2) (hb2 : b ≤ 2 * p)
    (hr : 0 < r) (hr_le : r ≤ rNbhd a h ρ R δ)
    (hNbig : |κ| / (N : ℝ) ≤ r / 2)
    (ω : Ω) (hω : ω ∈ EN μ q R a ρ h η0 ε m) :
    ∀ z ∈ NbhdN a h (ρ / 2), ∀ n : ℕ,
      ‖iteratedDeriv n (fun w => sNsrc κ L (q ω) w - sLimsrc κ L μ w) z‖ ≤
        n.factorial * (Real.exp (|κ| / r) * (1 + Real.exp (|L| * (h + 2 * ρ)))
          * max (κ ^ 2 / r ^ 2) (|κ| * (2 * KGN η0 δ ρ H Cms m p μ))
          * (ε + 1 / R ^ b + 1 / (N : ℝ))) / (ρ / 2) ^ n := by
  have hroots : ∀ j, |q ω j| ≤ R := by
    obtain ⟨h1, -⟩ := hω
    exact h1
  have hdiff : ∀ z ∈ NbhdN a h (ρ / 2), ∀ w ∈ closedBall z (ρ / 2),
      DifferentiableAt ℂ (fun w' => sNsrc κ L (q ω) w' - sLimsrc κ L μ w') w ∧
      w ∈ NbhdN a h ρ := by
    intro z hz w hw
    have hwd : ‖w - z‖ ≤ ρ / 2 := by
      rw [mem_closedBall, dist_eq_norm] at hw
      exact hw
    have hwN : w ∈ NbhdN a h (ρ / 2 + ρ / 2) := NbhdN_add hz hwd
    rw [show ρ / 2 + ρ / 2 = ρ by ring] at hwN
    obtain ⟨hGa, hGr, -⟩ := nbhd_dist (R := R) (q ω) μ ha hρ hb0 hsupp hsuppN hwN
    exact ⟨sNsrc_sLimsrc_differentiableAt κ L (q ω) μ (lt_of_lt_of_le hr hr_le) hGa
      (fun j => hGr j (hroots j)) hN.ne', hwN⟩
  intro z hz n
  have ht : 0 < ρ / 2 := half_pos hρ
  have hf : DiffContOnCl ℂ (fun w => sNsrc κ L (q ω) w - sLimsrc κ L μ w) (ball z (ρ / 2)) :=
    ⟨fun w hw => (hdiff z hz w (ball_subset_closedBall hw)).1.differentiableWithinAt,
      fun w hw => (hdiff z hz w (closure_ball_subset_closedBall hw)).1.continuousAt.continuousWithinAt⟩
  have hC : ∀ w ∈ sphere z (ρ / 2), ‖(fun w => sNsrc κ L (q ω) w - sLimsrc κ L μ w) w‖ ≤
      Real.exp (|κ| / r) * (1 + Real.exp (|L| * (h + 2 * ρ)))
        * max (κ ^ 2 / r ^ 2) (|κ| * (2 * KGN η0 δ ρ H Cms m p μ))
        * (ε + 1 / R ^ b + 1 / (N : ℝ)) := by
    intro w hw
    have hwN : w ∈ NbhdN a h ρ := (hdiff z hz w (sphere_subset_closedBall hw)).2
    exact derivative_j0_on_EN_r P hN q hq μ m p b η0 δ ρ h H R a ε Cms κ L r hη0 hρ hρδ hηh hb0 hH
      hR hR1 hRH hRH1 hR2ρ ha hcut hε hμint hsupp hsuppN hms hb hb2 hr hr_le hNbig ω hω w hwN
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n ht hf hC

end QuantumNLS.ResolventNeighborhood
