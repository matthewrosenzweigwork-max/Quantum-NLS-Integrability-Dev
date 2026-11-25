import Mathlib
import QuantumNLS.Prop009FiniteProbes
import QuantumNLS.Prop017Quantum

/-!
# PROP-009 / PROP-026 mixed binding, item (2), part B: the finite-probe event has Born probability tending to one

`mixed_propagation.tex:203-206`: "at each of those finitely many probes, Lemma `lem:B4-high-moments` makes the complement probability
tend to zero".  For the actual model the second-moment input is `Prop017Quantum.ms_actual` (R-09E1EAE9 `concentration_sharp`,
`E|G_N(z) − G(z)|² ≤ Csharp/(N Im z²)` on the high half-plane, accepted), not a new assumption.  New module (imports
`Prop009FiniteProbes`, `Prop017Quantum` read-only).

* `fz_upper`: `|f_z(w) − f_z(v)| ≤ 2κ|w − v|` for `|w|,|v| ≤ 1/Im z` on `HighHalf` (mean value inequality; the upper companion of
  `RootMeasureComplex.fz_lower`);
* `probe_upper`: `|s_N(z) − s(z)| ≤ 3(κ/Im z)²/N + 2κ|G_N(z) − G(z)|` (with `product_error`);
* `probe_prob_tendsto`: for `z` in `HighHalf` and `ε > 0`, `P_{N,u}(|s_N(z) − s(z)| ≥ ε) → 0` (Markov on `ms_actual`);
* `event_compl_tendsto`: for finitely many probes the complement of the probe event has Born probability `→ 0` (union bound);
* `diag_schedule`: the elementary diagonal selection (`∀ j, ∀ᶠ N, P j N` ⇒ `∃ J → ∞, ∀ᶠ N, P (J N) N`) used to build the
  schedule `j(N)` of the source ("use the `j`th collection when `N_j ≤ N < N_{j+1}`").
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace QuantumNLS.Prop009ProbeBorn

open QuantumNLS.PeriodReconstructionCore
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.RootMeasureComplex (fz HighHalf sProd product_error norm_exp_le_four_thirds norm_exp_izL_le)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis IsLimitingRapidityMeasure)
open QuantumNLS.Extrapolation (Gfull)
open QuantumNLS.RootMeasureConcentrationSharp (Csharp)
open QuantumNLS.Prop017Quantum (qAct eta0 ms_actual Gfull_eq GN_eq)
open QuantumNLS.Prop009FiniteProbes (sNf_eq_sProd sf_eq_fz norm_cauchy_le_im)

/-! ### 1. The upper Lipschitz bound and the probe upper bound -/

theorem fz_upper {L κ : ℝ} (hκ : 0 < κ) {z : ℂ} (hz : HighHalf L κ z) {w v : ℂ}
    (hw : ‖w‖ ≤ (z.im)⁻¹) (hv : ‖v‖ ≤ (z.im)⁻¹) :
    ‖fz L κ z w - fz L κ z v‖ ≤ 2 * κ * ‖w - v‖ := by
  have hη : 0 < z.im := by linarith [hz.1]
  have hx : κ * (z.im)⁻¹ ≤ 1 / 4 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hη]; linarith [hz.1]
  have hE : ‖Complex.exp (Complex.I * z * L)‖ ≤ 1 / 16 := norm_exp_izL_le hz
  set E := Complex.exp (Complex.I * z * L) with hEd
  have hd : ∀ y : ℂ, HasDerivAt (fz L κ z)
      (Complex.exp (Complex.I * κ * y) * (Complex.I * κ) +
        -(E * (Complex.exp (-(Complex.I * κ * y)) * (Complex.I * κ)))) y := by
    intro y
    unfold fz
    have h1 := ((hasDerivAt_id y).const_mul (Complex.I * (κ : ℂ))).cexp
    have h2 := ((((hasDerivAt_id y).const_mul (Complex.I * (κ : ℂ))).neg).cexp).const_mul E
    have := h1.add h2
    convert this using 1
    · rfl
    · simp [Pi.neg_apply]
  have hs : Convex ℝ (Metric.closedBall (0 : ℂ) ((z.im)⁻¹)) := convex_closedBall _ _
  have hb : ∀ y ∈ Metric.closedBall (0 : ℂ) ((z.im)⁻¹),
      ‖Complex.exp (Complex.I * κ * y) * (Complex.I * κ) +
        -(E * (Complex.exp (-(Complex.I * κ * y)) * (Complex.I * κ)))‖ ≤ 2 * κ := by
    intro y hy
    have hy' : ‖y‖ ≤ (z.im)⁻¹ := by simpa using hy
    have hik : ‖Complex.I * (κ : ℂ)‖ = κ := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ]
    have hk : ‖Complex.I * κ * y‖ ≤ 1 / 4 := by
      rw [norm_mul, hik]
      calc κ * ‖y‖ ≤ κ * (z.im)⁻¹ := mul_le_mul_of_nonneg_left hy' hκ.le
        _ ≤ 1 / 4 := hx
    have e1 := norm_exp_le_four_thirds hk
    have e2 := norm_exp_le_four_thirds (x := -(Complex.I * κ * y)) (by rwa [norm_neg])
    refine (norm_add_le _ _).trans ?_
    simp only [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hκ]
    have h3 : ‖E‖ * (‖Complex.exp (-(Complex.I * κ * y))‖ * κ) ≤ 1 / 16 * (4 / 3 * κ) := by
      gcongr
    nlinarith [mul_le_mul_of_nonneg_right e1 hκ.le]
  have h := hs.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fz L κ z)
    (f' := fun y => Complex.exp (Complex.I * κ * y) * (Complex.I * κ) +
        -(E * (Complex.exp (-(Complex.I * κ * y)) * (Complex.I * κ))))
    (C := 2 * κ) (fun y _ => (hd y).hasDerivWithinAt) hb
    (x := v) (y := w) (by simpa using hv) (by simpa using hw)
  exact h

theorem probe_upper {L κ : ℝ} (hκ : 0 < κ) {z : ℂ} (hz : HighHalf L κ z) {N : ℕ} (hN : 0 < N)
    (q : Fin N → ℝ) (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    ‖sNf L (κ / N) q z - sf L κ (EmpiricalRapidity.cauchyTransform ρ) z‖ ≤
      3 * (κ / z.im) ^ 2 / N +
        2 * κ * ‖QuantumNLS.RootMeasureComplex.GN N q z - EmpiricalRapidity.cauchyTransform ρ z‖ := by
  have hη : 0 < z.im := by linarith [hz.1]
  have h1 : ‖QuantumNLS.RootMeasureComplex.GN N q z‖ ≤ (z.im)⁻¹ :=
    QuantumNLS.RootMeasureConcentration.norm_GN_le q hη
  have h2 : ‖EmpiricalRapidity.cauchyTransform ρ z‖ ≤ (z.im)⁻¹ := norm_cauchy_le_im ρ hη
  have h3 := fz_upper hκ hz h1 h2
  have h4 := product_error (L := L) hκ hz hN q
  rw [sNf_eq_sProd, sf_eq_fz]
  have e : sProd L κ N q z - fz L κ z (EmpiricalRapidity.cauchyTransform ρ z) =
      (sProd L κ N q z - fz L κ z (QuantumNLS.RootMeasureComplex.GN N q z)) +
        (fz L κ z (QuantumNLS.RootMeasureComplex.GN N q z) -
          fz L κ z (EmpiricalRapidity.cauchyTransform ρ z)) := by ring
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add h4 h3)

/-! ### 2. The probe event has probability tending to one -/

section Prob

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

theorem probe_prob_tendsto (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {z : ℂ} (hz : HighHalf L κ z) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) u hu).real
      {m : MArr N | ε ≤ ‖sNf L (κ / N) (qAct L κ N m) z -
        sf L κ (EmpiricalRapidity.cauchyTransform (μ : Measure ℝ)) z‖}) atTop (𝓝 0) := by
  have hL : 0 < L := Fact.out
  have hη : 0 < z.im := by linarith [hz.1]
  have hyeta : eta0 L κ ≤ z.im :=
    max_le hz.1 (by rw [div_le_iff₀ hL]; linarith [hz.2])
  set y := z.im with hy
  set a : ℝ := (ε / (4 * κ)) ^ 2 with ha
  have ha0 : 0 < a := by positivity
  set x : ℝ := κ / y with hx
  have hzz : ((z.re : ℂ) + (z.im : ℂ) * Complex.I) = z := Complex.re_add_im z
  have hbound : ∀ᶠ N : ℕ in atTop, (bornMeasure (physBasis L hκ N) u hu).real
      {m : MArr N | ε ≤ ‖sNf L (κ / N) (qAct L κ N m) z -
        sf L κ (EmpiricalRapidity.cauchyTransform (μ : Measure ℝ)) z‖} ≤
      (Csharp / (y ^ 2 * a)) * ((N : ℝ)⁻¹) := by
    filter_upwards [eventually_ge_atTop (max 1 ⌈6 * x ^ 2 / ε⌉₊)] with N hN
    have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
    have hNpos : 0 < N := hN1
    have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
    have hN2 : 6 * x ^ 2 / ε ≤ (N : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hN)
    have hsmall : 3 * x ^ 2 / (N : ℝ) ≤ ε / 2 := by
      rw [div_le_iff₀ hNr]
      rw [div_le_iff₀ hε] at hN2
      nlinarith
    set P := bornMeasure (physBasis L hκ N) u hu with hP
    set f : MArr N → ℝ := fun m =>
      ‖Gfull (μ : Measure ℝ) z - QuantumNLS.Extrapolation.GN (qAct L κ N m) z‖ ^ 2 with hf
    have hms := ms_actual hκ u hu hμ hNpos z.re z.im hyeta
    rw [hzz] at hms
    have hf_bound : ∀ m, f m ≤ (2 / y) ^ 2 := by
      intro m
      have g1 : ‖Gfull (μ : Measure ℝ) z‖ ≤ y⁻¹ := by
        rw [Gfull_eq]; exact norm_cauchy_le_im (μ : Measure ℝ) hη
      have g2 : ‖QuantumNLS.Extrapolation.GN (qAct L κ N m) z‖ ≤ y⁻¹ := by
        rw [GN_eq]; exact QuantumNLS.RootMeasureConcentration.norm_GN_le _ hη
      have : ‖Gfull (μ : Measure ℝ) z - QuantumNLS.Extrapolation.GN (qAct L κ N m) z‖ ≤ 2 / y := by
        refine (norm_sub_le _ _).trans ?_
        have : 2 / y = y⁻¹ + y⁻¹ := by ring
        rw [this]; exact add_le_add g1 g2
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    have hf_int : Integrable f P :=
      Integrable.of_bound ((measurable_of_countable f).aestronglyMeasurable) ((2 / y) ^ 2)
        (Eventually.of_forall fun m => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hf_bound m)
    have hmark := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := f)
      (Eventually.of_forall fun m => by positivity) hf_int a
    have hsub : {m : MArr N | ε ≤ ‖sNf L (κ / N) (qAct L κ N m) z -
        sf L κ (EmpiricalRapidity.cauchyTransform (μ : Measure ℝ)) z‖} ⊆ {m | a ≤ f m} := by
      intro m hm
      have hm' : ε ≤ ‖sNf L (κ / N) (qAct L κ N m) z -
          sf L κ (EmpiricalRapidity.cauchyTransform (μ : Measure ℝ)) z‖ := hm
      have hpu := probe_upper (L := L) hκ hz hNpos (qAct L κ N m) (μ : Measure ℝ)
      have h5 : ε / 2 ≤ 2 * κ * ‖QuantumNLS.RootMeasureComplex.GN N (qAct L κ N m) z -
          EmpiricalRapidity.cauchyTransform (μ : Measure ℝ) z‖ := by linarith
      have h6 : ε / (4 * κ) ≤ ‖Gfull (μ : Measure ℝ) z - QuantumNLS.Extrapolation.GN (qAct L κ N m) z‖ := by
        rw [Gfull_eq, GN_eq, norm_sub_rev, div_le_iff₀ (by positivity)]
        have h5' : ε / 2 ≤ 2 * κ * ‖QuantumNLS.RootMeasureComplex.GN N (qAct L κ N m) z -
            QuantumNLS.CauchyUniqueness.cauchyTransform (μ : Measure ℝ) z‖ := h5
        linarith
      show a ≤ f m
      rw [ha, hf]
      exact pow_le_pow_left₀ (by positivity) h6 2
    have hreal : P.real {m : MArr N | ε ≤ ‖sNf L (κ / N) (qAct L κ N m) z -
        sf L κ (EmpiricalRapidity.cauchyTransform (μ : Measure ℝ)) z‖} ≤ P.real {m | a ≤ f m} :=
      measureReal_mono hsub
    have hh2 : a * P.real {m | a ≤ f m} ≤ Csharp / ((N : ℝ) * y ^ 2) := hmark.trans hms
    calc _ ≤ P.real {m | a ≤ f m} := hreal
      _ ≤ Csharp / ((N : ℝ) * y ^ 2) / a := by rw [le_div_iff₀ ha0, mul_comm]; exact hh2
      _ = (Csharp / (y ^ 2 * a)) * ((N : ℝ)⁻¹) := by field_simp
  have hlim : Tendsto (fun N : ℕ => (Csharp / (y ^ 2 * a)) * ((N : ℝ)⁻¹)) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (Csharp / (y ^ 2 * a))
    simpa using this
  exact squeeze_zero' (Eventually.of_forall fun N => measureReal_nonneg) hbound hlim

/-- The probe event: all `m` labels whose transfer eigenvalue is `ε`-close to `s` at every probe. -/
def probeEvent (μ : Measure ℝ) {m : ℕ} (z : Fin m → ℂ) (ε : ℝ) (N : ℕ) : Set (MArr N) :=
  {a : MArr N | ∀ j, ‖sNf L (κ / N) (qAct L κ N a) (z j) - sf L κ (EmpiricalRapidity.cauchyTransform μ) (z j)‖ < ε}

theorem event_compl_tendsto (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {m : ℕ} {z : Fin m → ℂ} (hz : ∀ j, HighHalf L κ (z j))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) u hu).real
      (probeEvent (L := L) (κ := κ) (μ : Measure ℝ) z ε N)ᶜ) atTop (𝓝 0) := by
  have hsum : Tendsto (fun N : ℕ => ∑ j : Fin m, (bornMeasure (physBasis L hκ N) u hu).real
      {a : MArr N | ε ≤ ‖sNf L (κ / N) (qAct L κ N a) (z j) -
        sf L κ (EmpiricalRapidity.cauchyTransform (μ : Measure ℝ)) (z j)‖}) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Fin m))
      (fun j _ => probe_prob_tendsto hκ u hu hμ (hz j) hε)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun N => measureReal_nonneg)
    (Eventually.of_forall fun N => ?_) hsum
  have : (probeEvent (L := L) (κ := κ) (μ : Measure ℝ) z ε N)ᶜ =
      ⋃ j : Fin m, {a : MArr N | ε ≤ ‖sNf L (κ / N) (qAct L κ N a) (z j) -
        sf L κ (EmpiricalRapidity.cauchyTransform (μ : Measure ℝ)) (z j)‖} := by
    ext a
    simp [probeEvent, not_forall, not_lt]
  rw [this]
  exact measureReal_iUnion_fintype_le _

end Prob

/-! ### 3. The diagonal schedule -/

open Classical in
theorem diag_schedule (P : ℕ → ℕ → Prop) (h : ∀ j, ∀ᶠ N in atTop, P j N) :
    ∃ J : ℕ → ℕ, Tendsto J atTop atTop ∧ ∀ᶠ N in atTop, P (J N) N := by
  choose T hT using fun j => eventually_atTop.1 (h j)
  refine ⟨fun N => Nat.findGreatest (fun j => T j ≤ N) N, ?_, ?_⟩
  · refine tendsto_atTop.2 fun K => eventually_atTop.2 ⟨max K (T K), fun N hN => ?_⟩
    exact Nat.le_findGreatest ((le_max_left _ _).trans hN) ((le_max_right _ _).trans hN)
  · refine eventually_atTop.2 ⟨T 0, fun N hN => ?_⟩
    have := Nat.findGreatest_spec (P := fun j => T j ≤ N) (m := 0) (Nat.zero_le N) hN
    exact hT _ N this

end QuantumNLS.Prop009ProbeBorn

#print axioms QuantumNLS.Prop009ProbeBorn.fz_upper
#print axioms QuantumNLS.Prop009ProbeBorn.probe_prob_tendsto
#print axioms QuantumNLS.Prop009ProbeBorn.event_compl_tendsto
#print axioms QuantumNLS.Prop009ProbeBorn.diag_schedule
