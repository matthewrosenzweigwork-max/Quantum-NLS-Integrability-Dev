import NlsGge.GK38.Defs
import NlsGge.Spectral.ActualPhysicalL2ZsCoefficientAllEntriesIntegrableMinimumV1
import NlsGge.Spectral.ActualPhysicalUnitRawCoverNorm32V1

/-!
# F1: potential pairs, the real slice and the representative convention (plan section 6.2)

## Convention (checked against the Grebert-Kappeler book, Chapter I, section 1)

* The book extends `φ ∈ L²_c = L²_ℂ × L²_ℂ`, given on `[0,1]` with `⟨φ, ψ⟩ = ∫₀¹ (φ₁ψ̄₁ + φ₂ψ̄₂) dt`
  `(1.6)`, **with period one** to all of `ℝ` (`φ(t+1) = φ(t)`, text before `(1.1)`).  The
  fundamental solution `M(t, λ, φ)` of `(1.2)` is a function on `[0, ∞)`; the unit-period
  monodromy is `M(1)`.  The periodic spectrum of the book's Overview and Chapter II is the
  spectrum on the doubled interval `[0, 2]` with periodic boundary conditions, i.e. the periodic
  and antiperiodic spectra on `[0,1]` together (zeros of `Δ² - 4`, `Δ = tr M(1)`).
* So the **x-interval is `[0,1]` with period one**, and the doubled interval `[0,2]` carries the
  periodic spectrum (`M(2) = M(1)²` by periodicity).  Both `[0,1]` and `[0,2]` occur.
* Repository convention (E02 layer): the potential on the real line is the *selected* Lp
  representative of the degree-two cover, `t ↦ naturalPhysicalCoverL2 u (t : SpectralCircle)`
  (doubled circle `ℝ/2ℤ`).  It is 1-periodic only almost everywhere (an arbitrary `Lp` coercion is
  not pointwise periodic), and `[0,1]` / `[0,2]` integrals are taken w.r.t. Lebesgue measure.
* **Pair convention (this file).** For `φ = (φ₁, φ₂) : PotPair` the representatives are
  `potRepFst38 φ t = naturalPhysicalCoverL2 φ.1 (t : SpectralCircle)`, `potRepSnd38 φ t` likewise
  with `φ.2`.  On the real slice `φ = realSlice u` one has `potRepFst38 (realSlice u) = E02's
  representative of u` by `rfl`, and `potRepSnd38 (realSlice u) =ᵐ star (potRepFst38 (realSlice u))`
  on all of `ℝ` (not pointwise: `naturalPhysicalCoverL2 (star u)` and `star (naturalPhysicalCoverL2 u)`
  are different representatives of the same class).  Consequently every integral against the
  coefficient `zsCoeffPot38 φ z` agrees on the real slice with the corresponding E02 integral
  (`zsCoeffPot38_realSlice_ae`).

## Contents
* `realSlice`: continuity, isometry, closed range, characterization of the range, real-analytic
  composition (`analyticOnNhd_comp_realSlice`), non-`ℂ`-linearity;
* `potRepFst38`/`potRepSnd38`: strong measurability everywhere, a.e. identification with
  `φ_i(t mod 1)`, a.e. 1-periodicity, a.e. linearity, interval integrability on `[0,1]`/`[0,2]`,
  `L²` and `L¹` norm identities/bounds on `[0,1]` and `[0,2]`;
* `zsCoeffPot38`: the coefficient `zsCoeffPair` of the representatives, entrywise
  interval-integrable, a.e. equal to E02's `actualPhysicalL2ZsCoefficient` on the real slice.

Probes (constant potential, plane wave) are in `PairPotentialProbe.lean`.
-/

set_option autoImplicit false

open Filter Topology MeasureTheory
open scoped ENNReal

namespace NlsGge.GK38

noncomputable section

open NlsGge.Pilot NlsGge.Schur NlsGge.Analysis NlsGge.SpectralFoundations

/-! ### The real slice -/

theorem continuous_realSlice : Continuous realSlice := realSlice.continuous

theorem isometry_realSlice : Isometry realSlice :=
  AddMonoidHomClass.isometry_of_norm realSlice norm_realSlice

theorem dist_realSlice (u v : PhysicalL2) : dist (realSlice u) (realSlice v) = dist u v :=
  isometry_realSlice.dist_eq u v

theorem realSlice_zero : realSlice 0 = 0 := map_zero _

theorem realSlice_add (u v : PhysicalL2) : realSlice (u + v) = realSlice u + realSlice v :=
  map_add _ u v

theorem realSlice_sub (u v : PhysicalL2) : realSlice (u - v) = realSlice u - realSlice v :=
  map_sub _ u v

theorem realSlice_neg (u : PhysicalL2) : realSlice (-u) = -realSlice u := map_neg _ u

theorem realSlice_smul_real (c : ℝ) (u : PhysicalL2) : realSlice (c • u) = c • realSlice u :=
  map_smul _ c u

/-- A pair lies on the real slice iff its second component is the conjugate of its first. -/
theorem mem_range_realSlice_iff (φ : PotPair) :
    φ ∈ Set.range realSlice ↔ φ.2 = star φ.1 := by
  constructor
  · rintro ⟨u, rfl⟩; rfl
  · intro h; exact ⟨φ.1, Prod.ext rfl h.symm⟩

/-- The real slice is a closed (real) subspace of `PotPair`. -/
theorem isClosed_range_realSlice : IsClosed (Set.range realSlice) :=
  isometry_realSlice.isClosedEmbedding.isClosed_range

/-- Conjugation is not `ℂ`-linear: `realSlice (i u) = i realSlice u` forces `u = 0`.  (`realSlice`
is only `ℝ`-linear, so the real slice is not a `ℂ`-subspace of `PotPair`.) -/
theorem realSlice_I_smul_eq_iff (u : PhysicalL2) :
    realSlice (Complex.I • u) = Complex.I • realSlice u ↔ u = 0 := by
  have key : star (Complex.I • u) = -(Complex.I • star u) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_star (Complex.I • u), Lp.coeFn_smul Complex.I u,
      Lp.coeFn_neg (Complex.I • star u), Lp.coeFn_smul Complex.I (star u),
      Lp.coeFn_star u] with x h1 h2 h3 h4 h5
    rw [h3, h1, Pi.star_apply, h2, Pi.smul_apply, Pi.neg_apply, h4, Pi.smul_apply, h5,
      Pi.star_apply]
    simp
  constructor
  · intro h
    have h2 := congrArg Prod.snd h
    simp only [realSlice_apply, Prod.smul_mk] at h2
    have h3 : -(Complex.I • star u) = Complex.I • star u := by rw [← key]; exact h2
    have h4 : Complex.I • star u = 0 := by
      have : (2 : ℂ) • (Complex.I • star u) = 0 := by
        rw [two_smul]; nth_rewrite 1 [← h3]; exact neg_add_cancel _
      exact (smul_eq_zero.mp this).resolve_left two_ne_zero
    have h5 : star u = 0 := (smul_eq_zero.mp h4).resolve_left Complex.I_ne_zero
    have := congrArg star h5
    rw [star_star] at this
    exact this.trans (map_zero starLp)
  · rintro rfl; rw [smul_zero, map_zero, smul_zero]

/-- Squared norm of a pair in the book's `ℓ²`-type norm `(1.6)`: `‖φ‖² = ‖φ₁‖² + ‖φ₂‖²`
(`PotPair` carries the equivalent sup norm). -/
def potNormSq38 (φ : PotPair) : ℝ := ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2

theorem potNormSq38_nonneg (φ : PotPair) : 0 ≤ potNormSq38 φ := by
  unfold potNormSq38; positivity

theorem norm_sq_le_potNormSq38 (φ : PotPair) : ‖φ‖ ^ 2 ≤ potNormSq38 φ := by
  unfold potNormSq38
  rw [Prod.norm_def]
  rcases le_total ‖φ.1‖ ‖φ.2‖ with h | h
  · rw [max_eq_right h]; nlinarith [sq_nonneg ‖φ.1‖]
  · rw [max_eq_left h]; nlinarith [sq_nonneg ‖φ.2‖]

theorem potNormSq38_le (φ : PotPair) : potNormSq38 φ ≤ 2 * ‖φ‖ ^ 2 := by
  unfold potNormSq38
  have h1 : ‖φ.1‖ ≤ ‖φ‖ := norm_fst_le φ
  have h2 : ‖φ.2‖ ≤ ‖φ‖ := norm_snd_le φ
  nlinarith [norm_nonneg φ.1, norm_nonneg φ.2]

/-- Parseval-type normalization on the real slice: `‖(u, ū)‖² = 2‖u‖²` (book Theorem 19.3). -/
theorem potNormSq38_realSlice (u : PhysicalL2) : potNormSq38 (realSlice u) = 2 * ‖u‖ ^ 2 := by
  unfold potNormSq38
  rw [realSlice_fst, realSlice_snd, show ‖star u‖ = ‖u‖ from starLp.norm_map u]
  ring

/-- Real-analyticity of a `ℂ`-analytic function of the pair, restricted to the real slice
(used for `u ↦ Δ(u, ū, z)`). -/
theorem analyticOnNhd_comp_realSlice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : PotPair → E} (hf : AnalyticOnNhd ℂ f Set.univ) :
    AnalyticOnNhd ℝ (fun u : PhysicalL2 => f (realSlice u)) Set.univ := fun u _ =>
  ((hf (realSlice u) trivial).restrictScalars (𝕜 := ℝ)).comp (realSlice.analyticAt u)

/-! ### Representatives of the degree-two cover -/

/-- Null sets of the doubled circle pull back to null sets of `ℝ`. -/
theorem ae_real_of_ae_spectral {p : SpectralCircle → Prop}
    (h : ∀ᵐ x ∂spectralHaar, p x) : ∀ᵐ t : ℝ, p (t : SpectralCircle) := by
  have hv : ∀ᵐ x ∂(volume : Measure SpectralCircle), p x := by
    rw [spectral_volume_eq_two_smul]
    exact Measure.ae_smul_measure h (2 : ℝ≥0∞)
  have hk : ∀ k : ℤ, ∀ᵐ t : ℝ ∂volume.restrict (Set.Ioc (0 + k • (2 : ℝ)) (0 + (k + 1) • 2)),
      p (t : SpectralCircle) := fun k =>
    (AddCircle.measurePreserving_mk (2 : ℝ) (0 + k • (2 : ℝ))).quasiMeasurePreserving.ae hv
      |> fun h => by
        convert h using 3
        simp only [zero_add, add_smul, one_smul]
  have hU := iUnion_Ioc_add_zsmul (show (0 : ℝ) < 2 by norm_num) 0
  have := (ae_restrict_iUnion_iff _ _).2 hk
  rwa [hU, Measure.restrict_univ] at this

/-- The selected representative on the real line of the degree-two cover of `f` (the E02
convention `fun t => naturalPhysicalCoverL2 f (t : SpectralCircle)`). -/
def coverRep38 (f : PhysicalL2) (t : ℝ) : ℂ := naturalPhysicalCoverL2 f (t : SpectralCircle)

/-- First and second component representatives of a potential pair. -/
def potRepFst38 (φ : PotPair) : ℝ → ℂ := coverRep38 φ.1

def potRepSnd38 (φ : PotPair) : ℝ → ℂ := coverRep38 φ.2

/-- On the real slice the first representative is exactly E02's. -/
theorem potRepFst38_realSlice (u : PhysicalL2) :
    potRepFst38 (realSlice u) = fun t : ℝ => naturalPhysicalCoverL2 u (t : SpectralCircle) := rfl

theorem stronglyMeasurable_coverRep38 (f : PhysicalL2) : StronglyMeasurable (coverRep38 f) :=
  (Lp.stronglyMeasurable (naturalPhysicalCoverL2 f)).comp_measurable
    (QuotientAddGroup.continuous_mk.measurable)

/-- The representative is `f(t mod 1)` for almost every real `t` (so it is 1-periodic a.e.). -/
theorem coverRep38_ae_phys (f : PhysicalL2) :
    ∀ᵐ t : ℝ, coverRep38 f t = f (t : PhysicalCircle) := by
  have := ae_real_of_ae_spectral (naturalPhysicalCoverL2_ae f)
  filter_upwards [this] with t ht
  exact ht

theorem coverRep38_periodic_ae (f : PhysicalL2) :
    ∀ᵐ t : ℝ, coverRep38 f (t + 1) = coverRep38 f t := by
  have h1 := (measurePreserving_add_right (volume : Measure ℝ) (1 : ℝ)).quasiMeasurePreserving.ae
    (coverRep38_ae_phys f)
  filter_upwards [h1, coverRep38_ae_phys f] with t h1 h2
  rw [h1, h2]
  simp only [AddCircle.coe_add, AddCircle.coe_period, add_zero]

theorem coverRep38_add_ae (f g : PhysicalL2) :
    ∀ᵐ t : ℝ, coverRep38 (f + g) t = coverRep38 f t + coverRep38 g t := by
  have h := ae_real_of_ae_spectral (p := fun x => (naturalPhysicalCoverL2 (f + g)) x =
    naturalPhysicalCoverL2 f x + naturalPhysicalCoverL2 g x)
    (by rw [map_add]; exact Lp.coeFn_add _ _)
  exact h

theorem coverRep38_sub_ae (f g : PhysicalL2) :
    ∀ᵐ t : ℝ, coverRep38 (f - g) t = coverRep38 f t - coverRep38 g t := by
  have h := ae_real_of_ae_spectral (p := fun x => (naturalPhysicalCoverL2 (f - g)) x =
    naturalPhysicalCoverL2 f x - naturalPhysicalCoverL2 g x)
    (by rw [map_sub]; exact Lp.coeFn_sub _ _)
  exact h

theorem coverRep38_smul_ae (c : ℂ) (f : PhysicalL2) :
    ∀ᵐ t : ℝ, coverRep38 (c • f) t = c * coverRep38 f t := by
  have h := ae_real_of_ae_spectral (p := fun x => (naturalPhysicalCoverL2 (c • f)) x =
    c * naturalPhysicalCoverL2 f x)
    (by
      rw [map_smul]
      filter_upwards [Lp.coeFn_smul c (naturalPhysicalCoverL2 f)] with x hx
      rw [hx]; rfl)
  exact h

/-- Conjugation commutes with the cover a.e. (the two representatives differ on a null set). -/
theorem coverRep38_star_ae (f : PhysicalL2) :
    ∀ᵐ t : ℝ, coverRep38 (star f) t = star (coverRep38 f t) := by
  have h1 := naturalPhysicalCover_preserving.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_star f)
  have h := ae_real_of_ae_spectral (p := fun x => (naturalPhysicalCoverL2 (star f)) x =
    star (naturalPhysicalCoverL2 f x))
    (by
      filter_upwards [naturalPhysicalCoverL2_ae (star f), h1, naturalPhysicalCoverL2_ae f]
        with x hx hy hz
      rw [hx]
      simp only [Function.comp_apply] at hy
      rw [hy, hz]
      rfl)
  exact h

/-- On the real slice the second representative is the conjugate of the first (a.e. on `ℝ`; not
pointwise). -/
theorem potRepSnd38_realSlice_ae (u : PhysicalL2) :
    ∀ᵐ t : ℝ, potRepSnd38 (realSlice u) t = star (potRepFst38 (realSlice u) t) :=
  coverRep38_star_ae u

theorem intervalIntegrable_coverRep38_two (f : PhysicalL2) :
    IntervalIntegrable (coverRep38 f) volume 0 2 :=
  naturalPhysicalCoverL2_intervalIntegrable_doubled f

theorem intervalIntegrable_coverRep38_one (f : PhysicalL2) :
    IntervalIntegrable (coverRep38 f) volume 0 1 :=
  (intervalIntegrable_coverRep38_two f).mono_set (by
    rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by norm_num)]
    exact Set.Icc_subset_Icc le_rfl (by norm_num))

theorem intervalIntegrable_coverRep38_sq_two (f : PhysicalL2) :
    IntervalIntegrable (fun t => ‖coverRep38 f t‖ ^ 2) volume 0 2 :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 2)).mpr
    (spectral_integrableOn_norm_sq_doubled_interval (naturalPhysicalCoverL2 f))

theorem intervalIntegrable_coverRep38_sq_one (f : PhysicalL2) :
    IntervalIntegrable (fun t => ‖coverRep38 f t‖ ^ 2) volume 0 1 :=
  (intervalIntegrable_coverRep38_sq_two f).mono_set (by
    rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by norm_num)]
    exact Set.Icc_subset_Icc le_rfl (by norm_num))

/-- `∫₀¹ |f|² = ‖f‖²` for the period-one representative. -/
theorem integral_sq_coverRep38_one (f : PhysicalL2) :
    ∫ t in (0 : ℝ)..1, ‖coverRep38 f t‖ ^ 2 = ‖f‖ ^ 2 := by
  rw [intervalIntegral.integral_of_le (by norm_num)]
  exact actualPhysicalRawCover_unitIntegral_norm_sq32 f

/-- `∫₀² |f|² = 2‖f‖²` on the doubled interval. -/
theorem integral_sq_coverRep38_two (f : PhysicalL2) :
    ∫ t in (0 : ℝ)..2, ‖coverRep38 f t‖ ^ 2 = 2 * ‖f‖ ^ 2 := by
  have h := spectral_norm_sq_doubled_interval (naturalPhysicalCoverL2 f)
  rw [naturalPhysicalCoverL2_norm] at h
  rw [intervalIntegral.integral_of_le (by norm_num)]
  change ∫ x in Set.Ioc (0 : ℝ) 2, ‖naturalPhysicalCoverL2 f (x : SpectralCircle)‖ ^ 2 = _
  rw [h]; ring

/-- Cauchy-Schwarz on an interval: `∫ₐᵇ |g| ≤ √(b-a) √(∫ₐᵇ |g|²)`. -/
theorem integral_norm_le_sqrt_mul {g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hm : AEStronglyMeasurable g volume)
    (hg : IntervalIntegrable (fun t => ‖g t‖ ^ 2) volume a b) :
    ∫ t in a..b, ‖g t‖ ≤ Real.sqrt (b - a) * Real.sqrt (∫ t in a..b, ‖g t‖ ^ 2) := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  have hg' : Integrable (fun t => ‖g t‖ ^ 2) (volume.restrict (Set.Ioc a b)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hg
  have hmeas : AEStronglyMeasurable g (volume.restrict (Set.Ioc a b)) := hm.restrict
  have hmem : MemLp (fun t => ‖g t‖) (ENNReal.ofReal 2) (volume.restrict (Set.Ioc a b)) := by
    have : MemLp g 2 (volume.restrict (Set.Ioc a b)) :=
      (memLp_two_iff_integrable_sq_norm hmeas).mpr hg'
    simpa using this.norm
  have h1 : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) (volume.restrict (Set.Ioc a b)) :=
    memLp_const 1
  have H := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (f := fun _ : ℝ => (1 : ℝ)) (g := fun t => ‖g t‖) (μ := volume.restrict (Set.Ioc a b))
    (Filter.Eventually.of_forall fun _ => zero_le_one)
    (Filter.Eventually.of_forall fun _ => norm_nonneg _) h1 hmem
  simp only [one_mul, Real.one_rpow, integral_const, Measure.real, Measure.restrict_apply_univ,
    Real.volume_Ioc, smul_eq_mul, mul_one] at H
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  simpa [Real.rpow_two, one_div, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] using H

theorem integral_coverRep38_le_one (f : PhysicalL2) :
    ∫ t in (0 : ℝ)..1, ‖coverRep38 f t‖ ≤ ‖f‖ := by
  have h := integral_norm_le_sqrt_mul (g := coverRep38 f) (a := 0) (b := 1) (by norm_num)
    (stronglyMeasurable_coverRep38 f).aestronglyMeasurable (intervalIntegrable_coverRep38_sq_one f)
  rw [integral_sq_coverRep38_one, Real.sqrt_sq (norm_nonneg _)] at h
  simpa using h

theorem integral_coverRep38_le_two (f : PhysicalL2) :
    ∫ t in (0 : ℝ)..2, ‖coverRep38 f t‖ ≤ 2 * ‖f‖ := by
  have h := integral_norm_le_sqrt_mul (g := coverRep38 f) (a := 0) (b := 2) (by norm_num)
    (stronglyMeasurable_coverRep38 f).aestronglyMeasurable (intervalIntegrable_coverRep38_sq_two f)
  rw [integral_sq_coverRep38_two, Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg _)] at h
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [sub_zero] at h
  calc _ ≤ _ := h
    _ = (Real.sqrt 2 * Real.sqrt 2) * ‖f‖ := by ring
    _ = _ := by rw [h2]

/-! ### `L¹` size of a pair and the coefficient -/

/-- `‖φ‖₁ = ∫₀¹ (|φ₁| + |φ₂|)` for the period-one representatives (the `L¹` norm in the
Volterra estimate `‖M(t)‖ ≤ exp(|Im z| t + ‖φ‖₁)`, book Theorem 1.1). -/
def potL1Norm38 (φ : PotPair) : ℝ :=
  ∫ t in (0 : ℝ)..1, (‖potRepFst38 φ t‖ + ‖potRepSnd38 φ t‖)

theorem intervalIntegrable_norm_coverRep38_one (f : PhysicalL2) :
    IntervalIntegrable (fun t => ‖coverRep38 f t‖) volume 0 1 :=
  (intervalIntegrable_coverRep38_one f).norm

theorem intervalIntegrable_norm_coverRep38_two (f : PhysicalL2) :
    IntervalIntegrable (fun t => ‖coverRep38 f t‖) volume 0 2 :=
  (intervalIntegrable_coverRep38_two f).norm

theorem potL1Norm38_nonneg (φ : PotPair) : 0 ≤ potL1Norm38 φ :=
  intervalIntegral.integral_nonneg (by norm_num) fun _ _ => by positivity

theorem potL1Norm38_le (φ : PotPair) : potL1Norm38 φ ≤ ‖φ.1‖ + ‖φ.2‖ := by
  unfold potL1Norm38 potRepFst38 potRepSnd38
  rw [intervalIntegral.integral_add (intervalIntegrable_norm_coverRep38_one φ.1)
    (intervalIntegrable_norm_coverRep38_one φ.2)]
  exact add_le_add (integral_coverRep38_le_one φ.1) (integral_coverRep38_le_one φ.2)

theorem potL1Norm38_le_two_mul (φ : PotPair) : potL1Norm38 φ ≤ 2 * ‖φ‖ := by
  have := potL1Norm38_le φ
  have h1 : ‖φ.1‖ ≤ ‖φ‖ := norm_fst_le φ
  have h2 : ‖φ.2‖ ≤ ‖φ‖ := norm_snd_le φ
  linarith

/-- The same estimate over the doubled interval `[0,2]` (`M(2) = M(1)²`). -/
theorem integral_pot_two_le (φ : PotPair) :
    ∫ t in (0 : ℝ)..2, (‖potRepFst38 φ t‖ + ‖potRepSnd38 φ t‖) ≤ 2 * (‖φ.1‖ + ‖φ.2‖) := by
  unfold potRepFst38 potRepSnd38
  rw [intervalIntegral.integral_add (intervalIntegrable_norm_coverRep38_two φ.1)
    (intervalIntegrable_norm_coverRep38_two φ.2)]
  linarith [integral_coverRep38_le_two φ.1, integral_coverRep38_le_two φ.2]

/-- `L¹` Lipschitz dependence of the representatives on `φ` (for continuity of the Volterra
operator in `φ`): `∫₀¹ (|φ₁ - ψ₁| + |φ₂ - ψ₂|) ≤ ‖φ₁ - ψ₁‖ + ‖φ₂ - ψ₂‖`. -/
theorem potL1Norm38_sub_le (φ ψ : PotPair) :
    ∫ t in (0 : ℝ)..1, (‖potRepFst38 φ t - potRepFst38 ψ t‖ +
        ‖potRepSnd38 φ t - potRepSnd38 ψ t‖) ≤ ‖φ.1 - ψ.1‖ + ‖φ.2 - ψ.2‖ := by
  have hae : (fun t => ‖potRepFst38 φ t - potRepFst38 ψ t‖ +
        ‖potRepSnd38 φ t - potRepSnd38 ψ t‖) =ᵐ[volume]
      fun t => ‖potRepFst38 (φ - ψ) t‖ + ‖potRepSnd38 (φ - ψ) t‖ := by
    filter_upwards [coverRep38_sub_ae φ.1 ψ.1, coverRep38_sub_ae φ.2 ψ.2] with t h1 h2
    simp only [potRepFst38, potRepSnd38, Prod.fst_sub, Prod.snd_sub, h1, h2]
  rw [intervalIntegral.integral_congr_ae (by
    filter_upwards [hae] with t ht _ using ht)]
  have := potL1Norm38_le (φ - ψ)
  simpa [potL1Norm38] using this

/-- The Zakharov-Shabat coefficient of the representatives of `φ` (book `(1.2)`:
`Φ̃ = [[0, iφ₁],[-iφ₂, 0]]`, plus `-zR`). -/
def zsCoeffPot38 (φ : PotPair) (z : ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  zsCoeffPair (potRepFst38 φ) (potRepSnd38 φ) z t

theorem intervalIntegrable_zsCoeffPot38_entry (φ : PotPair) (z : ℂ) (i j : Fin 2) :
    IntervalIntegrable (fun t => zsCoeffPot38 φ z t i j) volume 0 2 := by
  have h1 : IntervalIntegrable (potRepFst38 φ) volume 0 2 := intervalIntegrable_coverRep38_two _
  have h2 : IntervalIntegrable (potRepSnd38 φ) volume 0 2 := intervalIntegrable_coverRep38_two _
  fin_cases i <;> fin_cases j <;> simp only [zsCoeffPot38, zsCoeffPair]
  · exact intervalIntegrable_const
  · simpa using h1.const_mul Complex.I
  · exact (h2.const_mul Complex.I).neg
  · exact intervalIntegrable_const

theorem intervalIntegrable_zsCoeffPot38_entry_one (φ : PotPair) (z : ℂ) (i j : Fin 2) :
    IntervalIntegrable (fun t => zsCoeffPot38 φ z t i j) volume 0 1 :=
  (intervalIntegrable_zsCoeffPot38_entry φ z i j).mono_set (by
    rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by norm_num)]
    exact Set.Icc_subset_Icc le_rfl (by norm_num))

/-- Compatibility with the E02 layer: on the real slice the pair coefficient is a.e. equal to
`actualPhysicalL2ZsCoefficient` (so every integral over `[0,1]` or `[0,2]` agrees). -/
theorem zsCoeffPot38_realSlice_ae (u : PhysicalL2) (z : ℂ) :
    ∀ᵐ t : ℝ, zsCoeffPot38 (realSlice u) z t = actualPhysicalL2ZsCoefficient u z t := by
  filter_upwards [potRepSnd38_realSlice_ae u] with t ht
  unfold zsCoeffPot38 actualPhysicalL2ZsCoefficient
  rw [← zsCoeffPair_real]
  unfold zsCoeffPair
  simp only [ht]
  rfl

end

end NlsGge.GK38
