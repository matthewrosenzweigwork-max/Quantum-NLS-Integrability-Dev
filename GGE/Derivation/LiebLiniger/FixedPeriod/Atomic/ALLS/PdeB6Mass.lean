import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB6FejerLim

/-! # Track B, package 3: `L²` mass conservation for `L⁴` Duhamel solutions on an interval

`mass_conservation`: if `u` is continuous on `[a,b]`, `U ∈ L⁴([a,b] × 𝕋)` has slices `U(t,·) = u t` for
a.e. `t ∈ [a,b]`, and the interaction-picture coefficients satisfy
`intA u n t - intA u n s = ∫ₛᵗ intG U n` for all `n` and `s, t ∈ [a,b]`, then `‖u t‖ = ‖u s‖`.

Proof: per mode `|û_n(t)|² - |û_n(s)|² = 2 Re ∫ₛᵗ (-i) conj(û_n) N̂_n` (`PdeB6AC`); Fejér averages
of these identities; as `N → ∞` the left side tends to `‖u t‖² - ‖u s‖²` (dominated convergence for
series) and the right side to `2 Re ∫ₛᵗ (-i) ∫ 2|U|⁴ = 0` (dominated convergence with the uniform
Fejér bound, `PdeB6FejerLim`).
-/

namespace LiebLiniger.FixedPeriod.ALLS.PdeB
open MeasureTheory Filter Topology NlsGge.Pilot NlsGge.NLS38 NlsGge.Birkhoff NlsGge.Sobolev38
open scoped ComplexConjugate ENNReal
set_option autoImplicit false
noncomputable section

attribute [local instance] isProbabilityMeasure_spatial

theorem conj_mul_self_freePhase (t : ℝ) (n : ℤ) : conj (freePhase t n) * freePhase t n = 1 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_freePhase]
  norm_num

theorem conj_intA_mul_intG (u : ℝ → PhysicalL2) (U : ℝ × PhysicalCircle → ℂ) (n : ℤ) (r : ℝ) :
    conj (intA u n r) * intG U n r =
      -Complex.I * (conj (physicalFourier (u r) n) *
        physicalFourier (fun x => cubicNL (U (r, x))) n) := by
  unfold intA intG
  rw [map_mul]
  have h := conj_mul_self_freePhase (-r) n
  linear_combination (-Complex.I * (conj (physicalFourier (u r) n) *
    physicalFourier (fun x => cubicNL (U (r, x))) n)) * h

theorem norm_intA (u : ℝ → PhysicalL2) (n : ℤ) (t : ℝ) :
    ‖intA u n t‖ = ‖physicalFourier (u t) n‖ := by
  rw [intA, norm_mul, norm_freePhase, one_mul]

theorem continuous_physicalFourier_coord (n : ℤ) :
    Continuous fun v : PhysicalL2 => physicalFourier v n :=
  ((carrierCoordCLM (-1) n).comp l2ToHm1).continuous

/-- Hypotheses of the interval mass identity. -/
structure MassHyp (u : ℝ → PhysicalL2) (U : ℝ × PhysicalCircle → ℂ) (a b : ℝ) : Prop where
  cont : ContinuousOn u (Set.Icc a b)
  memLp : MemLp U 4 (slabM a b)
  slice : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Icc a b)),
    (fun x => U (t, x)) =ᵐ[spatialMeasure] (u t : PhysicalCircle → ℂ)
  coeff : ∀ n : ℤ, ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
    intA u n t - intA u n s = ∫ r in s..t, intG U n r

/-- The mode functions `c_n(r) = conj(û_n(r)) N̂_n(r)`. -/
def modeC (u : ℝ → PhysicalL2) (U : ℝ × PhysicalCircle → ℂ) (n : ℤ) (r : ℝ) : ℂ :=
  conj (physicalFourier (u r) n) * physicalFourier (fun x => cubicNL (U (r, x))) n

namespace MassHyp

variable {u : ℝ → PhysicalL2} {U : ℝ × PhysicalCircle → ℂ} {a b : ℝ}

theorem continuousOn_intA (H : MassHyp u U a b) (n : ℤ) :
    ContinuousOn (intA u n) (Set.Icc a b) := by
  unfold intA
  exact ((continuous_freePhase n).comp continuous_neg).continuousOn.mul
    ((continuous_physicalFourier_coord n).comp_continuousOn H.cont)

theorem intervalIntegrable_modeC (H : MassHyp u U a b) (n : ℤ) {s t : ℝ}
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) :
    IntervalIntegrable (fun r => -Complex.I * modeC u U n r) volume s t := by
  have hsub : Set.uIcc s t ⊆ Set.Icc a b := Set.uIcc_subset_Icc hs ht
  have hc : ContinuousOn (fun r => conj (intA u n r)) (Set.uIcc s t) :=
    Complex.continuous_conj.comp_continuousOn ((H.continuousOn_intA n).mono hsub)
  have h := (intervalIntegrable_intG H.memLp n hs ht).continuousOn_mul hc
  refine h.congr (fun r _ => ?_)
  simp only [modeC]
  rw [conj_intA_mul_intG]

/-- Per-mode identity `|û_n(t)|² - |û_n(s)|² = 2 Re ∫ₛᵗ (-i) c_n`. -/
theorem mode_identity (H : MassHyp u U a b) (n : ℤ) {s t : ℝ} (hs : s ∈ Set.Icc a b)
    (ht : t ∈ Set.Icc a b) (hst : s ≤ t) :
    ‖physicalFourier (u t) n‖ ^ 2 - ‖physicalFourier (u s) n‖ ^ 2 =
      2 * (∫ r in s..t, -Complex.I * modeC u U n r).re := by
  have hg : IntegrableOn (intG U n) (Set.Ioc s t) :=
    (integrableOn_intG H.memLp n).mono_set
      (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc hs.1 ht.2))
  have hA : ∀ r ∈ Set.Icc s t, intA u n r = intA u n s + ∫ q in s..r, intG U n q := by
    intro r hr
    have hr' : r ∈ Set.Icc a b := ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩
    rw [← H.coeff n s hs r hr']
    ring
  have h := normSq_indefinite hst hg (intA u n) hA
  rw [norm_intA, norm_intA] at h
  rw [h]
  congr 2
  refine intervalIntegral.integral_congr fun r _ => ?_
  simp only [modeC]
  rw [conj_intA_mul_intG]

end MassHyp

/-! ### Fejér averages of the mode identities -/

/-- `Σ_{j,k<N} F(k-j) = Σ_{|n|≤N} cntZ N n · F(n)`. -/
theorem double_sum_eq (N : ℕ) (F : ℤ → ℝ) :
    (∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, F ((k : ℤ) - j)) =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) N, (cntZ N n : ℝ) * F n := by
  have hF : ∀ j ∈ Finset.range N, ∀ k ∈ Finset.range N, F ((k : ℤ) - j) =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) N, if (k : ℤ) - j = n then F n else 0 := by
    intro j hj k hk
    rw [Finset.mem_range] at hj hk
    have hm : (k : ℤ) - j ∈ Finset.Icc (-(N : ℤ)) N := by
      rw [Finset.mem_Icc]; constructor <;> omega
    rw [Finset.sum_ite_eq]
    simp only [hm, ↓reduceIte]
  rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => hF j hj k hk]
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold cntZ
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> ring

/-- Fejér averages of a nonnegative summable sequence converge to its sum. -/
theorem fejer_mass_tendsto {F : ℤ → ℝ} (hF0 : ∀ n, 0 ≤ F n) {S : ℝ} (hF : HasSum F S) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, F ((k : ℤ) - j))
      atTop (𝓝 S) := by
  set f : ℕ → ℤ → ℝ := fun N n =>
    if n ∈ Finset.Icc (-(N : ℤ)) N then (N : ℝ)⁻¹ * (cntZ N n : ℝ) * F n else 0 with hfdef
  have he : ∀ N : ℕ, (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, F ((k : ℤ) - j) =
      ∑' n, f N n := by
    intro N
    rw [double_sum_eq, tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) N) (fun n hn => by
      simp only [hfdef, hn, ↓reduceIte]), Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [hfdef, hn, ↓reduceIte]
    ring
  simp_rw [he]
  rw [← hF.tsum_eq]
  refine tendsto_tsum_of_dominated_convergence hF.summable (fun n => ?_) ?_
  · have hev : ∀ᶠ N : ℕ in atTop, f N n = (N : ℝ)⁻¹ * (cntZ N n : ℝ) * F n := by
      filter_upwards [eventually_ge_atTop n.natAbs] with N hN
      have hmem : n ∈ Finset.Icc (-(N : ℤ)) N := by
        rw [Finset.mem_Icc]; constructor <;> omega
      simp only [hfdef, hmem, ↓reduceIte]
    rw [tendsto_congr' hev]
    simpa using (fejW_tendsto n).mul_const (F n)
  · filter_upwards [eventually_gt_atTop 0] with N hN n
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    simp only [hfdef]
    split_ifs
    · have h1 : (cntZ N n : ℝ) ≤ N := by exact_mod_cast cntZ_le N n
      have h2 : (0 : ℝ) ≤ cntZ N n := by exact_mod_cast cntZ_nonneg N n
      have hw : (N : ℝ)⁻¹ * (cntZ N n : ℝ) ≤ 1 := by
        rw [inv_mul_le_iff₀ hNr, mul_one]; exact h1
      rw [Real.norm_of_nonneg (by have := hF0 n; positivity)]
      calc (N : ℝ)⁻¹ * (cntZ N n : ℝ) * F n ≤ 1 * F n :=
            mul_le_mul_of_nonneg_right hw (hF0 n)
        _ = F n := one_mul _
    · rw [norm_zero]; exact hF0 n

namespace MassHyp

variable {u : ℝ → PhysicalL2} {U : ℝ × PhysicalCircle → ℂ} {a b : ℝ}

/-- Fejér-averaged mode identity. -/
theorem fejer_identity (H : MassHyp u U a b) (N : ℕ) {s t : ℝ} (hs : s ∈ Set.Icc a b)
    (ht : t ∈ Set.Icc a b) (hst : s ≤ t) :
    (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        ‖physicalFourier (u t) ((k : ℤ) - j)‖ ^ 2 -
      (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        ‖physicalFourier (u s) ((k : ℤ) - j)‖ ^ 2 =
      2 * (∫ r in s..t, -Complex.I *
        fejP N (fun n => physicalFourier (u r) n)
          (fun n => physicalFourier (fun x => cubicNL (U (r, x))) n)).re := by
  have hii : ∀ j k : ℕ, IntervalIntegrable
      (fun r => -Complex.I * modeC u U ((k : ℤ) - j) r) volume s t :=
    fun j k => H.intervalIntegrable_modeC _ hs ht
  have hii2 : ∀ j : ℕ, IntervalIntegrable
      (fun r => ∑ k ∈ Finset.range N, -Complex.I * modeC u U ((k : ℤ) - j) r) volume s t := by
    intro j
    have h := IntervalIntegrable.sum (Finset.range N) (fun k _ => hii j k)
    rw [Finset.sum_fn] at h
    exact h
  have hint : (∫ r in s..t, -Complex.I *
      fejP N (fun n => physicalFourier (u r) n)
        (fun n => physicalFourier (fun x => cubicNL (U (r, x))) n)) =
      ((N : ℝ)⁻¹ : ℂ) * ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        ∫ r in s..t, -Complex.I * modeC u U ((k : ℤ) - j) r := by
    have e : ∀ r, -Complex.I * fejP N (fun n => physicalFourier (u r) n)
        (fun n => physicalFourier (fun x => cubicNL (U (r, x))) n) =
        ((N : ℝ)⁻¹ : ℂ) * ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
          -Complex.I * modeC u U ((k : ℤ) - j) r := fun r => by
      unfold fejP modeC
      push_cast
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
      (fun j _ => hii2 j)]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_finsetSum (fun k _ => hii j k)]
  rw [hint, ← Complex.ofReal_inv, Complex.re_ofReal_mul, ← mul_sub, ← Finset.sum_sub_distrib, Complex.re_sum,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_sub_distrib, Complex.re_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [H.mode_identity _ hs ht hst]
  ring

theorem memLp_slab_prod (H : MassHyp u U a b) :
    MemLp U 4 (((volume : Measure ℝ).restrict (Set.Icc a b)).prod spatialMeasure) := by
  have h := H.memLp
  unfold slabM spacetimeMeasure at h
  rwa [slab_eq] at h

theorem integrable_pow4 (H : MassHyp u U a b) :
    Integrable (fun p => ‖U p‖ ^ 4)
      (((volume : Measure ℝ).restrict (Set.Icc a b)).prod spatialMeasure) := by
  have h := H.memLp_slab_prod.integrable_norm_rpow (by norm_num) (by norm_num)
  simpa using h

theorem ae_memLp_slice (H : MassHyp u U a b) :
    ∀ᵐ r ∂((volume : Measure ℝ).restrict (Set.Icc a b)),
      MemLp (fun x => U (r, x)) 4 spatialMeasure := by
  filter_upwards [H.integrable_pow4.prod_right_ae,
    H.memLp_slab_prod.aestronglyMeasurable.prodMk_left] with r h1 h2
  refine (integrable_norm_rpow_iff h2 (by norm_num) (by norm_num)).1 ?_
  simpa using h1

/-- **Mass conservation on `[a,b]`.** -/
theorem norm_eq (H : MassHyp u U a b) {s t : ℝ} (hs : s ∈ Set.Icc a b)
    (ht : t ∈ Set.Icc a b) (hst : s ≤ t) : ‖u t‖ = ‖u s‖ := by
  set W : ℕ → ℝ → ℂ := fun N r => -Complex.I *
    fejP N (fun n => physicalFourier (u r) n)
      (fun n => physicalFourier (fun x => cubicNL (U (r, x))) n) with hWdef
  set L : ℝ → ℂ := fun r => -Complex.I *
    ∫ x, conj (U (r, x)) * cubicNL (U (r, x)) ∂spatialMeasure with hLdef
  have hsub : Set.Ioc s t ⊆ Set.Icc a b :=
    Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc hs.1 ht.2)
  have hrestr : ∀ {P : ℝ → Prop}, (∀ᵐ r ∂((volume : Measure ℝ).restrict (Set.Icc a b)), P r) →
      ∀ᵐ r ∂((volume : Measure ℝ).restrict (Set.Ioc s t)), P r := fun h =>
    ae_restrict_of_ae_restrict_of_subset hsub h
  -- the Fejér pairing of the solution equals that of the slice for a.e. time
  have hWslice : ∀ᵐ r ∂((volume : Measure ℝ).restrict (Set.Ioc s t)), ∀ N,
      W N r = -Complex.I * fejP N (physicalFourier (fun x => U (r, x)))
        (physicalFourier (fun x => cubicNL (U (r, x)))) := by
    filter_upwards [hrestr H.slice] with r hr N
    simp only [hWdef]
    rw [physicalFourier_congr_ae hr]
  -- right side: dominated convergence
  have hrhs : Tendsto (fun N => ∫ r in s..t, W N r) atTop (𝓝 (∫ r in s..t, L r)) := by
    simp_rw [intervalIntegral.integral_of_le hst]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun r => 2 * ∫ x, ‖U (r, x)‖ ^ 4 ∂spatialMeasure) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun N => ?_
      have hi : IntervalIntegrable (W N) volume s t := by
        have e : W N = fun r => ((N : ℝ)⁻¹ : ℂ) * ∑ j ∈ Finset.range N,
            ∑ k ∈ Finset.range N, -Complex.I * modeC u U ((k : ℤ) - j) r := by
          funext r
          simp only [hWdef]
          unfold fejP modeC
          push_cast
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
        rw [e]
        have h1 : ∀ j : ℕ, IntervalIntegrable (fun r => ∑ k ∈ Finset.range N,
            -Complex.I * modeC u U ((k : ℤ) - j) r) volume s t := by
          intro j
          have h := IntervalIntegrable.sum (Finset.range N)
            (fun k _ => H.intervalIntegrable_modeC ((k : ℤ) - j) hs ht)
          rw [Finset.sum_fn] at h
          exact h
        have h2 := IntervalIntegrable.sum (Finset.range N) (fun j _ => h1 j)
        rw [Finset.sum_fn] at h2
        exact h2.const_mul _
      exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hst).1 hi).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop 0] with N hN
      filter_upwards [hWslice, hrestr H.ae_memLp_slice] with r hr hm
      rw [hr N, norm_mul, norm_neg, Complex.norm_I, one_mul]
      refine (fejP_cubic_bound N hN hm hm one_pos).trans (le_of_eq ?_)
      ring
    · have h1 := (H.integrable_pow4.integral_prod_left).const_mul 2
      exact h1.mono_measure (Measure.restrict_mono hsub le_rfl)
    · filter_upwards [hWslice, hrestr H.ae_memLp_slice] with r hr hm
      simp_rw [hr]
      exact (fejP_cubic_tendsto hm).const_mul _
  -- the limit has zero real part
  have hL : (∫ r in s..t, L r).re = 0 := by
    have e : ∀ r, L r = -Complex.I *
        ((∫ x, 2 * ‖U (r, x)‖ ^ 4 ∂spatialMeasure : ℝ) : ℂ) := fun r => by
      simp only [hLdef]
      rw [← integral_complex_ofReal]
      congr 1
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only
      unfold cubicNL
      have h := Complex.mul_conj (U (r, x))
      rw [Complex.normSq_eq_norm_sq] at h
      push_cast at h ⊢
      linear_combination (2 * ((‖U (r, x)‖ : ℂ) ^ 2)) * h
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
    simp
  -- left side: Fejér averages of the masses
  have hlhs : ∀ v : PhysicalL2, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
      ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, ‖physicalFourier v ((k : ℤ) - j)‖ ^ 2)
      atTop (𝓝 (‖v‖ ^ 2)) := fun v =>
    fejer_mass_tendsto (F := fun n => ‖physicalFourier v n‖ ^ 2) (fun n => by positivity)
      (hasSum_physicalFourier_sq v)
  have hlim := ((hlhs (u t)).sub (hlhs (u s)))
  have hlim2 : Tendsto (fun N => 2 * (∫ r in s..t, W N r).re) atTop
      (𝓝 (2 * (∫ r in s..t, L r).re)) :=
    ((Complex.continuous_re.tendsto _).comp hrhs).const_mul 2
  have heq : (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        ‖physicalFourier (u t) ((k : ℤ) - j)‖ ^ 2 -
      (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        ‖physicalFourier (u s) ((k : ℤ) - j)‖ ^ 2) =
      fun N => 2 * (∫ r in s..t, W N r).re :=
    funext fun N => H.fejer_identity N hs ht hst
  rw [heq] at hlim
  have h0 := tendsto_nhds_unique hlim hlim2
  rw [hL, mul_zero, sub_eq_zero] at h0
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h0

end MassHyp

end

end LiebLiniger.FixedPeriod.ALLS.PdeB
