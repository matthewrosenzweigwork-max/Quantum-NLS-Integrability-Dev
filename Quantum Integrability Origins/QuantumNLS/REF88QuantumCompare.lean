import Mathlib
import QuantumNLS.REF88QuantumLabels

/-!
# REF88QuantumCompare: every finite-support rounding has the same limiting quantile (R-EF8C2837, item (iii), step S1, part 2)

Source: `source-text/chapters/global/physical_cubic.tex` (sha256 `64ec3e02...`), printed lines 232-262.

Printed step -> Lean:
* "The root-label confinement `|p_i - q_i| <= 2 sqrt(K/L)` controls the free-label second-moment tails: for
  `R >= 4 sqrt(K/L)`, `N^{-1} sum_{|p_i|>R} p_i^2 <= 4 N^{-1} sum_{|q_i|>R/2} q_i^2`":
  `tail_plab_le` (accepted REG-002 `IndividualRootBound.mean_field_root_bound_roots`; the printed `R >= 4 sqrt(K/L)`
  is used in the slightly stronger form `R >= 8 sqrt(K/L)`, which is all that is needed since only `R -> infinity` matters);
* the second-moment tails of the root quantiles are small because the root quantiles converge in `L^2`: `tail_le_W2`;
* "On bounded labels, the full occupation convergence in `l^1` gives convergence of the discrete measures. The tail bound and
  finite-set truncation then give `L^2` quantile convergence": `REF88QuantumLabels.clip_weak` + `comparison`;
* "The finite-root label contraction ... compares these samples with every deterministic rounding of the same `x`, so
  those roundings have the same limiting `Q`" and "The coupling estimate ... bounds the normalized root change by
  `|sqrt K_j - sqrt K|/sqrt L`": `comparison`, the final theorem: a sample sequence `m^n` (occupations `-> x` in `l^1`,
  root empirical measures `-> rho` in `W2`, at coupling `K`) forces every rounding `eta^n` (supported in a fixed finite
  set, occupations `-> x` in `l^1`) at couplings `kappa_n -> K` to have root empirical measures `-> rho` in `W2`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators

namespace QuantumNLS.REF88QuantumCompare

open QuantumNLS.REF88QuantumLabels QuantumNLS.BetheLabels QuantumNLS.QuantileTransport

variable {L : ℝ}

theorem le_of_sq_le {a b : ℝ≥0∞} (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  have h' : a ^ (2 : ℝ) ≤ b ^ (2 : ℝ) := by simpa only [ENNReal.rpow_two] using h
  exact (ENNReal.rpow_le_rpow_iff (by norm_num)).1 h'

theorem tailMoment_eq (σ : Measure ℝ) (R : ℝ) :
    tailMoment σ R = ∫⁻ x, {x : ℝ | R < |x|}.indicator (fun x => ENNReal.ofReal (x ^ 2)) x ∂σ := by
  unfold tailMoment
  exact (lintegral_indicator (measurableSet_tail R) _).symm

theorem tailMoment_empirical {N : ℕ} (x : Fin N → ℝ) (R : ℝ) :
    tailMoment (empirical N x) R =
      ∑ j, (N : ℝ≥0∞)⁻¹ * {x : ℝ | R < |x|}.indicator (fun x => ENNReal.ofReal (x ^ 2)) (x j) := by
  rw [tailMoment_eq]
  unfold empirical
  rw [lintegral_finsetSum_measure]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

theorem indicator_le_pt (p q R : ℝ) (hR : 0 ≤ R) (hpq : |p - q| ≤ R / 2) :
    {x : ℝ | R < |x|}.indicator (fun x => ENNReal.ofReal (x ^ 2)) p ≤
      4 * {x : ℝ | R / 2 < |x|}.indicator (fun x => ENNReal.ofReal (x ^ 2)) q := by
  by_cases hp : R < |p|
  · have hq : R / 2 < |q| := by
      have := abs_sub_abs_le_abs_sub p q
      linarith
    rw [indicator_of_mem (show p ∈ {x : ℝ | R < |x|} from hp),
      indicator_of_mem (show q ∈ {x : ℝ | R / 2 < |x|} from hq)]
    have h1 : p ^ 2 ≤ 4 * q ^ 2 := by
      have h3 : |p| ≤ 2 * |q| := by
        have := abs_sub_abs_le_abs_sub p q
        linarith
      calc p ^ 2 = |p| ^ 2 := (sq_abs p).symm
        _ ≤ (2 * |q|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
        _ = 4 * q ^ 2 := by rw [mul_pow, sq_abs]; ring
    calc ENNReal.ofReal (p ^ 2) ≤ ENNReal.ofReal (4 * q ^ 2) := ENNReal.ofReal_le_ofReal h1
      _ = 4 * ENNReal.ofReal (q ^ 2) := by
        rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
  · rw [indicator_of_notMem (show p ∉ {x : ℝ | R < |x|} from hp)]
    exact bot_le

/-- The printed tail bound `N⁻¹ ∑_{|p_i|>R} p_i² ≤ 4 N⁻¹ ∑_{|q_i|>R/2} q_i²`. -/
theorem tail_plab_le {N : ℕ} (hN : 0 < N) (hL : 0 < L) {K : ℝ} (hK : 0 < K) (a : MArr N) {R : ℝ}
    (hR : 4 * Real.sqrt (K / L) ≤ R) :
    tailMoment (empirical N (plab L a)) R ≤
      4 * tailMoment (empirical N (arrRoots L (K / N) a)) (R / 2) := by
  have hR0 : 0 ≤ R := le_trans (by positivity) hR
  rw [tailMoment_empirical, tailMoment_empirical, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hb := IndividualRootBound.mean_field_root_bound_roots (Nat.one_le_iff_ne_zero.2 hN.ne') hL hK
    (ncorr a) (ncorr_mono a) j
  have hb2 : 2 * Real.sqrt ((K / L) * (1 - 1 / (N : ℝ))) ≤ 2 * Real.sqrt (K / L) := by
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have : (K / L) * (1 - 1 / (N : ℝ)) ≤ K / L := by
      have : 0 ≤ (K / L) * (1 / (N : ℝ)) := by positivity
      nlinarith
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt this) (by norm_num)
  have hpq : |plab L a j - arrRoots L (K / N) a j| ≤ R / 2 := by
    have e : arrRoots L (K / N) a j = BetheSmooth.roots L (ncorr a) (K / (N : ℝ)) j := rfl
    rw [abs_sub_comm, e]
    unfold plab
    linarith
  have := indicator_le_pt (plab L a j) (arrRoots L (K / N) a j) R hR0 hpq
  calc (N : ℝ≥0∞)⁻¹ * {x : ℝ | R < |x|}.indicator (fun x => ENNReal.ofReal (x ^ 2)) (plab L a j)
      ≤ (N : ℝ≥0∞)⁻¹ * (4 * {x : ℝ | R / 2 < |x|}.indicator (fun x => ENNReal.ofReal (x ^ 2))
          (arrRoots L (K / N) a j)) := mul_le_mul' le_rfl this
    _ = 4 * ((N : ℝ≥0∞)⁻¹ * {x : ℝ | R / 2 < |x|}.indicator (fun x => ENNReal.ofReal (x ^ 2))
          (arrRoots L (K / N) a j)) := by ring

theorem W2_sq_eq_cost (σ τ : Measure ℝ) [IsProbabilityMeasure σ] [IsProbabilityMeasure τ] :
    W2 σ τ ^ (2 : ℝ) = cost (quantileCoupling σ τ) := by
  rw [W2_eq_qm, ← ENNReal.rpow_mul, cost_quantileCoupling]
  norm_num

lemma h_clip_sq_le (S x y : ℝ) (hS : 0 ≤ S) :
    ENNReal.ofReal ((x - clip (S / 2) x) ^ 2) ≤
      2 * ENNReal.ofReal ((y - clip (S / 2) y) ^ 2) + 8 * ENNReal.ofReal (|x - y| ^ 2) := by
  have hlip : |(x - clip (S / 2) x) - (y - clip (S / 2) y)| ≤ 2 * |x - y| := by
    have h1 := abs_clip_sub_clip_le (S / 2) x y
    have : (x - clip (S / 2) x) - (y - clip (S / 2) y) = (x - y) - (clip (S / 2) x - clip (S / 2) y) := by ring
    rw [this]
    refine (abs_sub _ _).trans ?_
    linarith
  have h2 : (x - clip (S / 2) x) ^ 2 ≤ 2 * (y - clip (S / 2) y) ^ 2 + 8 * |x - y| ^ 2 := by
    have h3 : |x - clip (S / 2) x| ≤ |y - clip (S / 2) y| + 2 * |x - y| := by
      have := abs_sub_abs_le_abs_sub (x - clip (S / 2) x) (y - clip (S / 2) y)
      linarith
    have h4 : (x - clip (S / 2) x) ^ 2 = |x - clip (S / 2) x| ^ 2 := (sq_abs _).symm
    rw [h4]
    have h5 : (y - clip (S / 2) y) ^ 2 = |y - clip (S / 2) y| ^ 2 := (sq_abs _).symm
    rw [h5]
    nlinarith [abs_nonneg (y - clip (S / 2) y), abs_nonneg (x - y), abs_nonneg (x - clip (S / 2) x),
      sq_nonneg (|y - clip (S / 2) y| - 2 * |x - y|)]
  calc ENNReal.ofReal ((x - clip (S / 2) x) ^ 2)
      ≤ ENNReal.ofReal (2 * (y - clip (S / 2) y) ^ 2 + 8 * |x - y| ^ 2) := ENNReal.ofReal_le_ofReal h2
    _ = _ := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_mul (by norm_num)]
      norm_num

lemma tail_pt_le (S x : ℝ) (hS : 0 ≤ S) :
    {x : ℝ | S < |x|}.indicator (fun x => ENNReal.ofReal (x ^ 2)) x ≤
      4 * ENNReal.ofReal ((x - clip (S / 2) x) ^ 2) := by
  by_cases hx : S < |x|
  · rw [indicator_of_mem (show x ∈ {x : ℝ | S < |x|} from hx)]
    have : x ^ 2 ≤ 4 * (x - clip (S / 2) x) ^ 2 := by
      rcases lt_abs.1 hx with h | h
      · have : clip (S / 2) x = S / 2 := by
          unfold clip
          rw [min_eq_right (by linarith), max_eq_right (by linarith)]
        rw [this]; nlinarith
      · have : clip (S / 2) x = -(S / 2) := by
          unfold clip
          rw [min_eq_left (by linarith), max_eq_left (by linarith)]
        rw [this]; nlinarith
    calc ENNReal.ofReal (x ^ 2) ≤ ENNReal.ofReal (4 * (x - clip (S / 2) x) ^ 2) :=
          ENNReal.ofReal_le_ofReal this
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
  · rw [indicator_of_notMem (show x ∉ {x : ℝ | S < |x|} from hx)]
    exact bot_le

lemma clip_sq_le_tail_pt (S y : ℝ) (hS : 0 ≤ S) :
    ENNReal.ofReal ((y - clip (S / 2) y) ^ 2) ≤
      {x : ℝ | S / 2 < |x|}.indicator (fun x => ENNReal.ofReal (x ^ 2)) y := by
  by_cases hy : S / 2 < |y|
  · rw [indicator_of_mem (show y ∈ {x : ℝ | S / 2 < |x|} from hy)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← sq_abs (y - clip (S / 2) y), ← sq_abs y]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_sub_clip_le (by linarith) y) 2
  · rw [indicator_of_notMem (show y ∉ {x : ℝ | S / 2 < |x|} from hy)]
    rw [clip_of_abs_le (not_lt.1 hy)]
    simp

/-- The second-moment tail of `σ` is controlled by `W2(σ, ρ)` and the tail of `ρ`. -/
theorem tail_le_W2 (σ ρ : Measure ℝ) [IsProbabilityMeasure σ] [IsProbabilityMeasure ρ] {S : ℝ}
    (hS : 0 ≤ S) :
    tailMoment σ S ≤ 32 * W2 σ ρ ^ 2 + 8 * tailMoment ρ (S / 2) := by
  set π := quantileCoupling σ ρ with hπ
  have hc := isCoupling_quantileCoupling σ ρ
  have hmeas : Measurable fun x : ℝ => ENNReal.ofReal ((x - clip (S / 2) x) ^ 2) :=
    ENNReal.measurable_ofReal.comp ((measurable_id.sub (continuous_clip _).measurable).pow_const 2)
  have hcost : cost π = W2 σ ρ ^ 2 := by
    rw [hπ, ← W2_sq_eq_cost, ENNReal.rpow_two]
  have h1 : tailMoment σ S ≤ 4 * ∫⁻ x, ENNReal.ofReal ((x - clip (S / 2) x) ^ 2) ∂σ := by
    rw [tailMoment_eq, ← lintegral_const_mul _ hmeas]
    exact lintegral_mono fun x => tail_pt_le S x hS
  have h2 : ∫⁻ x, ENNReal.ofReal ((x - clip (S / 2) x) ^ 2) ∂σ =
      ∫⁻ p, ENNReal.ofReal ((p.1 - clip (S / 2) p.1) ^ 2) ∂π := by
    rw [← hc.2.1, lintegral_map hmeas measurable_fst]
  have h3 : ∫⁻ p, ENNReal.ofReal ((p.1 - clip (S / 2) p.1) ^ 2) ∂π ≤
      2 * ∫⁻ y, ENNReal.ofReal ((y - clip (S / 2) y) ^ 2) ∂ρ + 8 * cost π := by
    have hmeas2 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal ((p.2 - clip (S / 2) p.2) ^ 2) :=
      hmeas.comp measurable_snd
    have hmeas3 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (|p.1 - p.2| ^ 2) :=
      ENNReal.measurable_ofReal.comp ((measurable_fst.sub measurable_snd).abs.pow_const 2)
    calc ∫⁻ p, ENNReal.ofReal ((p.1 - clip (S / 2) p.1) ^ 2) ∂π
        ≤ ∫⁻ p, (2 * ENNReal.ofReal ((p.2 - clip (S / 2) p.2) ^ 2) +
            8 * ENNReal.ofReal (|p.1 - p.2| ^ 2)) ∂π :=
          lintegral_mono fun p => h_clip_sq_le S p.1 p.2 hS
      _ = 2 * ∫⁻ p, ENNReal.ofReal ((p.2 - clip (S / 2) p.2) ^ 2) ∂π +
            8 * ∫⁻ p, ENNReal.ofReal (|p.1 - p.2| ^ 2) ∂π := by
          rw [lintegral_add_left (hmeas2.const_mul 2), lintegral_const_mul _ hmeas2,
            lintegral_const_mul _ hmeas3]
      _ = _ := by
          rw [cost]
          congr 2
          rw [← hc.2.2, lintegral_map hmeas measurable_snd]
  have h4 : ∫⁻ y, ENNReal.ofReal ((y - clip (S / 2) y) ^ 2) ∂ρ ≤ tailMoment ρ (S / 2) := by
    rw [tailMoment_eq]
    exact lintegral_mono fun y => clip_sq_le_tail_pt S y hS
  calc tailMoment σ S ≤ 4 * ∫⁻ x, ENNReal.ofReal ((x - clip (S / 2) x) ^ 2) ∂σ := h1
    _ ≤ 4 * (2 * ∫⁻ y, ENNReal.ofReal ((y - clip (S / 2) y) ^ 2) ∂ρ + 8 * cost π) := by
        rw [h2]; exact mul_le_mul' le_rfl h3
    _ ≤ 4 * (2 * tailMoment ρ (S / 2) + 8 * W2 σ ρ ^ 2) := by
        rw [hcost]
        exact mul_le_mul' le_rfl (add_le_add (mul_le_mul' le_rfl h4) le_rfl)
    _ = 32 * W2 σ ρ ^ 2 + 8 * tailMoment ρ (S / 2) := by ring

theorem ncorr_mem {N : ℕ} (a : MArr N) (F : Finset ℤ) (hF : ∀ k, k ∉ F → a.1 k = 0) (j : Fin N) :
    ncorr a j ∈ F := by
  by_contra h
  have h0 := hF _ h
  rw [← ncorr_count a (ncorr a j)] at h0
  have : j ∈ Finset.univ.filter fun i => ncorr a i = ncorr a j := by simp
  exact absurd h0 (Finset.card_pos.2 ⟨j, this⟩).ne'


theorem tendsto_ofReal_zero {f : ℕ → ℝ} (h : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun n => ENNReal.ofReal (f n)) atTop (𝓝 0) := by
  simpa using ENNReal.tendsto_ofReal h

/-- **Every finite-support rounding has the quantile limit of the sample.**  A sample sequence `m^n ∈ M_{n+1}`
(occupations `→ p` in `ℓ¹`, root empirical measures at coupling `K` converging to `ρ` in `W2`) forces every rounding
`η^n ∈ M_{n+1}` supported in a fixed finite set with occupations `→ p` in `ℓ¹`, at couplings `κ_n → K`, to have root
empirical measures converging to `ρ` in `W2`. -/
theorem comparison (hL : 0 < L) {K : ℝ} (hK : 0 < K) (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hρ : HasFiniteSecondMoment ρ) (p : PMF ℤ)
    (m : ∀ n : ℕ, MArr (n + 1))
    (hm1 : Tendsto (fun n : ℕ => ∑' k, |(((m n).1 k : ℕ) : ℝ) / ((n : ℝ) + 1) - (p k).toReal|)
      atTop (𝓝 0))
    (hm2 : Tendsto (fun n : ℕ => W2 (empirical (n + 1) (arrRoots L (K / ((n : ℝ) + 1)) (m n))) ρ)
      atTop (𝓝 0))
    (η : ∀ n : ℕ, MArr (n + 1)) (F : Finset ℤ) (hF : ∀ n k, k ∉ F → (η n).1 k = 0)
    (hη : Tendsto (fun n : ℕ => ∑' k, |(((η n).1 k : ℕ) : ℝ) / ((n : ℝ) + 1) - (p k).toReal|)
      atTop (𝓝 0))
    (κs : ℕ → ℝ) (hκs : Tendsto κs atTop (𝓝 K)) (hpos : ∀ n, 0 < κs n) :
    Tendsto (fun n : ℕ => W2 (empirical (n + 1) (arrRoots L (κs n / ((n : ℝ) + 1)) (η n))) ρ)
      atTop (𝓝 0) := by
  have prob : ∀ (n : ℕ) (x : Fin (n + 1) → ℝ), IsProbabilityMeasure (empirical (n + 1) x) :=
    fun n x => isProbabilityMeasure_empirical (Nat.succ_pos n) x
  have hB2 : Tendsto (fun n : ℕ => ENNReal.ofReal (|Real.sqrt (κs n) - Real.sqrt K| / Real.sqrt L))
      atTop (𝓝 0) := by
    refine tendsto_ofReal_zero ?_
    have h := (Real.continuous_sqrt.tendsto K).comp hκs
    have h2 := ((h.sub_const (Real.sqrt K)).abs).div_const (Real.sqrt L)
    simpa using h2
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hεt : ε = ⊤
  · exact Eventually.of_forall fun n => hεt ▸ le_top
  obtain ⟨e, he, rfl⟩ : ∃ e : ℝ, 0 < e ∧ ε = ENNReal.ofReal e :=
    ⟨ε.toReal, ENNReal.toReal_pos hε.ne' hεt, (ENNReal.ofReal_toReal hεt).symm⟩
  set δ : ℝ := e / 5 with hδdef
  have hδ : 0 < δ := by positivity
  set R0 : ℝ := ∑ k ∈ F, |2 * Real.pi * (k : ℝ) / L| with hR0
  -- the choice of the cut-off `R`
  have hτ : Tendsto (fun R : ℝ => 32 * tailMoment ρ (R / 2 / 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => R / 2 / 2) atTop atTop :=
      (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2)).atTop_div_const (by norm_num)
    have h2 := (tendsto_tailMoment ρ hρ).comp h1
    simpa using ENNReal.Tendsto.const_mul h2 (Or.inr (by norm_num : (32 : ℝ≥0∞) ≠ ⊤))
  obtain ⟨R, hRτ, hR1, hR2⟩ : ∃ R : ℝ, 32 * tailMoment ρ (R / 2 / 2) ≤ ENNReal.ofReal (δ ^ 2 / 2) ∧
      4 * Real.sqrt (K / L) ≤ R ∧ R0 ≤ R :=
    ((ENNReal.tendsto_nhds_zero.1 hτ _ (ENNReal.ofReal_pos.2 (by positivity))).and
      ((eventually_ge_atTop (4 * Real.sqrt (K / L))).and (eventually_ge_atTop R0))).exists
  have hR0' : 0 ≤ R := le_trans (by positivity) hR1
  have hRpos : ∀ n : ℕ, ∀ x : Fin (n + 1) → ℝ, IsProbabilityMeasure ((empirical (n + 1) x).map (clip R)) :=
    fun n x => by
      haveI := prob n x
      infer_instance
  -- the eventual smallness statements
  have hw1 := clip_weak hL hR0' p η hη
  have hw2 := clip_weak hL hR0' p m hm1
  have e1 : ∀ᶠ n : ℕ in atTop, W2 (empirical (n + 1) (fun j => clip R (plab L (η n) j)))
      (limMeas L R p) ≤ ENNReal.ofReal δ := ENNReal.tendsto_nhds_zero.1 hw1 _ (ENNReal.ofReal_pos.2 hδ)
  have e2 : ∀ᶠ n : ℕ in atTop, W2 (empirical (n + 1) (fun j => clip R (plab L (m n) j)))
      (limMeas L R p) ≤ ENNReal.ofReal δ := ENNReal.tendsto_nhds_zero.1 hw2 _ (ENNReal.ofReal_pos.2 hδ)
  have e3 : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (|Real.sqrt (κs n) - Real.sqrt K| / Real.sqrt L) ≤
      ENNReal.ofReal δ := ENNReal.tendsto_nhds_zero.1 hB2 _ (ENNReal.ofReal_pos.2 hδ)
  have e4 : ∀ᶠ n : ℕ in atTop, W2 (empirical (n + 1) (arrRoots L (K / ((n : ℝ) + 1)) (m n))) ρ ≤
      ENNReal.ofReal (δ / 16) := ENNReal.tendsto_nhds_zero.1 hm2 _ (ENNReal.ofReal_pos.2 (by positivity))
  filter_upwards [e1, e2, e3, e4] with n h1 h2 h3 h4
  have hN : 0 < n + 1 := Nat.succ_pos n
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  haveI := prob n (arrRoots L (κs n / ((n : ℝ) + 1)) (η n))
  haveI := prob n (arrRoots L (κs n / ((n : ℝ) + 1)) (m n))
  haveI := prob n (arrRoots L (K / ((n : ℝ) + 1)) (m n))
  haveI := prob n (plab L (η n))
  haveI := prob n (plab L (m n))
  haveI := hRpos n (plab L (η n))
  haveI := hRpos n (plab L (m n))
  have hKn : 0 < K / ((n : ℝ) + 1) := by positivity
  have hcn : 0 < κs n / ((n : ℝ) + 1) := div_pos (hpos n) (by positivity)
  -- root chain
  have c1 : W2 (empirical (n + 1) (arrRoots L (κs n / ((n : ℝ) + 1)) (η n))) ρ ≤
      W2 (empirical (n + 1) (arrRoots L (κs n / ((n : ℝ) + 1)) (η n)))
        (empirical (n + 1) (arrRoots L (κs n / ((n : ℝ) + 1)) (m n))) +
      W2 (empirical (n + 1) (arrRoots L (κs n / ((n : ℝ) + 1)) (m n)))
        (empirical (n + 1) (arrRoots L (K / ((n : ℝ) + 1)) (m n))) +
      W2 (empirical (n + 1) (arrRoots L (K / ((n : ℝ) + 1)) (m n))) ρ := by
    refine (W2_triangle _ (empirical (n + 1) (arrRoots L (κs n / ((n : ℝ) + 1)) (m n))) _).trans ?_
    rw [add_assoc]
    refine add_le_add le_rfl ?_
    exact W2_triangle _ (empirical (n + 1) (arrRoots L (K / ((n : ℝ) + 1)) (m n))) _
  have c2 := W2_roots_le hN hL hcn (η n) (m n)
  have c3 : W2 (empirical (n + 1) (arrRoots L (κs n / ((n : ℝ) + 1)) (m n)))
      (empirical (n + 1) (arrRoots L (K / ((n : ℝ) + 1)) (m n))) ≤
      ENNReal.ofReal (|Real.sqrt (κs n) - Real.sqrt K| / Real.sqrt L) := by
    have := W2_coupling_le hN hL (K₀ := K) (K₁ := κs n) hK (hpos n) (m n)
    simpa only [Nat.cast_add, Nat.cast_one] using this
  -- label chain
  set μη := empirical (n + 1) (plab L (η n)) with hμη
  set μm := empirical (n + 1) (plab L (m n)) with hμm
  have hcη : μη.map (clip R) = empirical (n + 1) (fun j => clip R (plab L (η n) j)) :=
    map_clip_empirical R _
  have hcm : μm.map (clip R) = empirical (n + 1) (fun j => clip R (plab L (m n) j)) :=
    map_clip_empirical R _
  have d1 : W2 μη μm ≤ W2 μη (μη.map (clip R)) + (W2 (μη.map (clip R)) (limMeas L R p) +
      (W2 (limMeas L R p) (μm.map (clip R)) + W2 (μm.map (clip R)) μm)) := by
    refine (W2_triangle _ (μη.map (clip R)) _).trans (add_le_add le_rfl ?_)
    refine (W2_triangle _ (limMeas L R p) _).trans (add_le_add le_rfl ?_)
    exact W2_triangle _ (μm.map (clip R)) _
  -- T1 = 0
  have t1 : W2 μη (μη.map (clip R)) ≤ 0 := by
    have h := W2_clip_sq_le_tail μη hR0'
    have : tailMoment μη R = 0 := by
      rw [hμη, tailMoment_empirical]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [indicator_of_notMem, mul_zero]
      have hj := ncorr_mem (η n) F (hF n) j
      have : |plab L (η n) j| ≤ R0 := by
        unfold plab
        exact Finset.single_le_sum (f := fun k : ℤ => |2 * Real.pi * (k : ℝ) / L|)
          (fun k _ => abs_nonneg _) hj
      intro hlt
      exact absurd (lt_of_lt_of_le hlt (this.trans hR2)) (lt_irrefl _)
    rw [this] at h
    exact le_of_sq_le (by simpa using h)
  -- T3
  have t3 : W2 (limMeas L R p) (μm.map (clip R)) ≤ ENNReal.ofReal δ := by
    rw [W2_comm, hcm]; exact h2
  have t2 : W2 (μη.map (clip R)) (limMeas L R p) ≤ ENNReal.ofReal δ := by
    rw [hcη]; exact h1
  -- T4
  have t4 : W2 (μm.map (clip R)) μm ≤ ENNReal.ofReal δ := by
    have h := W2_clip_sq_le_tail μm hR0'
    have ht := tail_plab_le hN hL hK (m n) hR1
    have ht2 := tail_le_W2 (empirical (n + 1) (arrRoots L (K / ((n + 1 : ℕ) : ℝ)) (m n))) ρ
      (S := R / 2) (by positivity)
    simp only [Nat.cast_add, Nat.cast_one] at ht ht2
    have hb : W2 (empirical (n + 1) (arrRoots L (K / ((n : ℝ) + 1)) (m n))) ρ ^ 2 ≤
        (ENNReal.ofReal (δ / 16)) ^ 2 := pow_le_pow_left' h4 2
    have hfin : W2 μm (μm.map (clip R)) ^ 2 ≤ ENNReal.ofReal δ ^ 2 := by
      calc W2 μm (μm.map (clip R)) ^ 2 ≤ tailMoment μm R := h
        _ ≤ 4 * tailMoment (empirical (n + 1) (arrRoots L (K / ((n : ℝ) + 1)) (m n))) (R / 2) := ht
        _ ≤ 4 * (32 * W2 (empirical (n + 1) (arrRoots L (K / ((n : ℝ) + 1)) (m n))) ρ ^ 2 +
              8 * tailMoment ρ (R / 2 / 2)) := mul_le_mul' le_rfl ht2
        _ ≤ 4 * (32 * ENNReal.ofReal (δ / 16) ^ 2 + 8 * tailMoment ρ (R / 2 / 2)) := by
            gcongr
        _ = 128 * ENNReal.ofReal (δ / 16) ^ 2 + 32 * tailMoment ρ (R / 2 / 2) := by ring
        _ ≤ ENNReal.ofReal (δ ^ 2 / 2) + ENNReal.ofReal (δ ^ 2 / 2) := by
            refine add_le_add ?_ hRτ
            rw [← ENNReal.ofReal_pow (by positivity), show (128 : ℝ≥0∞) = ENNReal.ofReal 128 by simp,
              ← ENNReal.ofReal_mul (by norm_num)]
            refine le_of_eq ?_
            congr 1; ring
        _ = ENNReal.ofReal δ ^ 2 := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_pow hδ.le]
            congr 1; ring
    rw [W2_comm]; exact le_of_sq_le hfin
  have t4' : W2 (μm.map (clip R)) μm ≤ ENNReal.ofReal δ := t4
  have hb4 : W2 (empirical (n + 1) (arrRoots L (K / ((n : ℝ) + 1)) (m n))) ρ ≤ ENNReal.ofReal δ :=
    h4.trans (ENNReal.ofReal_le_ofReal (by linarith))
  calc W2 (empirical (n + 1) (arrRoots L (κs n / ((n : ℝ) + 1)) (η n))) ρ
      ≤ _ := c1
    _ ≤ W2 μη μm + ENNReal.ofReal δ + ENNReal.ofReal δ := by
        refine add_le_add (add_le_add c2 (c3.trans h3)) hb4
    _ ≤ (0 + (ENNReal.ofReal δ + (ENNReal.ofReal δ + ENNReal.ofReal δ))) + ENNReal.ofReal δ +
          ENNReal.ofReal δ := by
        refine add_le_add (add_le_add (d1.trans (add_le_add t1 (add_le_add t2 (add_le_add t3 t4')))) le_rfl) le_rfl
    _ = ENNReal.ofReal e := by
        have h5 : ENNReal.ofReal (5 * δ) = 5 * ENNReal.ofReal δ := by
          rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
        calc (0 + (ENNReal.ofReal δ + (ENNReal.ofReal δ + ENNReal.ofReal δ))) + ENNReal.ofReal δ +
            ENNReal.ofReal δ = 5 * ENNReal.ofReal δ := by ring
          _ = ENNReal.ofReal (5 * δ) := h5.symm
          _ = ENNReal.ofReal e := by congr 1; rw [hδdef]; ring

end QuantumNLS.REF88QuantumCompare

#print axioms QuantumNLS.REF88QuantumCompare.tail_plab_le
#print axioms QuantumNLS.REF88QuantumCompare.tail_le_W2
#print axioms QuantumNLS.REF88QuantumCompare.comparison
