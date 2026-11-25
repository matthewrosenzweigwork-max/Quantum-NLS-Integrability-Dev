import Mathlib
import QuantumNLS.Prop009FiniteProbes

/-!
# PROP-009 / PROP-026 mixed binding, item (2), part A: the finite-probe event forces a UNIFORM transfer deviation on fixed contours

New module (imports `Prop009FiniteProbes` a9d14725, `PeriodReconstruction`, `LabelBlock` read-only).  The source (`mixed_propagation.tex:196-218`)
chooses, for each `j ≥ 1`, finitely many probes (Lemma `lem:B4-finite-probes`) "whose good event forces the required root-free
neighbourhoods and transfer deviations below `1/j`" on ALL selected fixed contours.  `Prop009FiniteProbes.finite_probes` supplies the
`O(N^-2)` reconstruction remainder; the present module supplies the deviation form that `eq:MP-fixed-deviation` consumes.

Routing (no EXT-025 contract): the same contradiction argument as `finite_probes`, abstracted once as `probes_generic`
(countable probe family `zp`, violators for `k` probes with tolerance `1/(k+1)`, weak convergence by the accepted
`CauchyLimitCriterion.tendsto_of_cauchy`).  The quantity to be forced is
* `onShell_of_arr`: every DEF-006 label array `m ∈ M_N` carries an `OnShellBethe` configuration with `q = arrRoots L (κ/N) m`
  (the converse of `LabelTightness.toActualConfig`: `roots_solves` + `boseBethe_iff_log`);
* `unif_sdev`: along `rootP(B_k) ⇀ μ`, `N_k → ∞`, and uniformly on a compact `Γ` at distance `≥ d₁` from `supp μ` and from all roots,
  `s_N(z) → s(z)` (`ell_lin`, `unif_conv`, `AN_eq_exp`);
* `finite_probes_dev`: for finitely many fixed contours `Gam (xm i) (xp i) (h i)` (PROP-006 label brackets), every `τ > 0` has finitely
  many high probes, `ε`, `N₀`, `d > 0` such that every on-shell configuration obeying the probe bound `|s_N(z_j) − s(z_j)| < ε`
  has all roots at distance `≥ d` from every contour and `|s_N(w) − s(w)| ≤ τ` on every contour.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace QuantumNLS.Prop009ProbeDev

open QuantumNLS.PeriodReconstructionCore QuantumNLS.PeriodReconstructionBigO QuantumNLS.PeriodReconstruction
open QuantumNLS.LabelJointLimit QuantumNLS.LabelJointWeak QuantumNLS.LabelBlock
open QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts
open QuantumNLS.RootMeasureComplex (HighHalf GN)
open QuantumNLS.Prop009FiniteProbes
open QuantumNLS.BetheLabels QuantumNLS.BetheAdmission QuantumNLS.RootContraction QuantumNLS.BetheSmooth
open QuantumNLS.PeriodReconstructionAsymp (ell_lin)

/-! ### 1. Label arrays carry on-shell configurations -/

theorem onShell_of_arr {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (m : MArr N) :
    ∃ B : OnShellBethe L κ N, B.q = arrRoots L (κ / N) m := by
  have hc : 0 < κ / (N : ℝ) := div_pos hκ (by exact_mod_cast hN)
  set ℓ := labelsEquivArr.symm m with hℓ
  have hs : Solves L (κ / (N : ℝ)) (correctedInt ℓ) (roots L (correctedInt ℓ) (κ / (N : ℝ))) :=
    roots_solves hL hc _
  have hq : StrictMono (roots L (correctedInt ℓ) (κ / (N : ℝ))) := roots_strictMono_labels hL hc ℓ
  have hbose : BoseBethe L (κ / (N : ℝ)) (correctedInt ℓ) (roots L (correctedInt ℓ) (κ / (N : ℝ))) := by
    refine (boseBethe_iff_log (L := L) hc hq (correctedInt ℓ)).2 (fun j => ?_)
    have h1 := hs j
    have h2 : Tmap L (κ / (N : ℝ)) (roots L (correctedInt ℓ) (κ / (N : ℝ))) j =
        logMap L (κ / (N : ℝ)) (roots L (correctedInt ℓ) (κ / (N : ℝ))) j := by
      rw [logMap_erase]; rfl
    rw [h2, h1]
    unfold quantumNumbers
    ring
  exact ⟨⟨roots L (correctedInt ℓ) (κ / (N : ℝ)), correctedInt ℓ, hq, correctedInt_monotone ℓ,
    fun j => hbose j⟩, rfl⟩

/-! ### 2. The generic probe theorem -/

/-- Generic form of the finite-probe contradiction argument.  `P t N B` is a property of a configuration, monotone in the
parameter `t`; if every weakly convergent sequence eventually satisfies `P t` for some `t`, then finitely many probes force `P t`. -/
theorem probes_generic {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ)
    (P : ℕ → ∀ N : ℕ, OnShellBethe L κ N → Prop)
    (hmono : ∀ t t' N (B : OnShellBethe L κ N), t ≤ t' → P t N B → P t' N B)
    (hseq : ∀ (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (B : ∀ k, OnShellBethe L κ (N k)),
      Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 (⟨S.μ, S.isProb⟩ : ProbabilityMeasure ℝ)) →
      Tendsto N atTop atTop → ∃ t, ∀ᶠ k in atTop, P t (N k) (B k)) :
    ∃ m : ℕ, ∃ z : Fin m → ℂ, (∀ j, HighHalf L κ (z j)) ∧ ∃ ε > 0, ∃ N₀ : ℕ, ∃ t : ℕ,
      ∀ (N : ℕ) (_ : 0 < N), N₀ ≤ N → ∀ B : OnShellBethe L κ N,
        (∀ j, ‖sNf L (κ / N) B.q (z j) - sf L κ (EmpiricalRapidity.cauchyTransform S.μ) (z j)‖ < ε) →
        P t N B := by
  have hL := S.hL
  have hκ := S.hκ
  haveI : IsProbabilityMeasure S.μ := S.isProb
  set μ : ProbabilityMeasure ℝ := ⟨S.μ, S.isProb⟩ with hμdef
  by_contra hcon
  set qd : ℕ → ℝ := TopologicalSpace.denseSeq ℝ with hqd
  have hzp := zp_high hL hκ qd
  have key : ∀ k : ℕ, ∃ (N : ℕ) (_ : 0 < N) (_ : k + 1 ≤ N) (B : OnShellBethe L κ N),
      (∀ j : Fin k, ‖sNf L (κ / N) B.q (zp L κ qd j) -
        sf L κ (EmpiricalRapidity.cauchyTransform S.μ) (zp L κ qd j)‖ < 1 / ((k : ℝ) + 1)) ∧
      ¬ P k N B := by
    intro k
    by_contra hk
    apply hcon
    refine ⟨k, fun j => zp L κ qd j, fun j => hzp j, 1 / ((k : ℝ) + 1), by positivity, k + 1, k, ?_⟩
    intro N hN hNge B hB
    by_contra hC
    exact hk ⟨N, hN, hNge, B, hB, hC⟩
  choose N hNpos hNge B hB hnot using key
  have hNtop : Tendsto N atTop atTop :=
    tendsto_atTop_mono (fun k => by have := hNge k; simp only [id]; omega) tendsto_id
  have hconvG : ∀ i : ℕ, Tendsto (fun k => GN (N k) (B k).q (zp L κ qd i)) atTop
      (𝓝 (EmpiricalRapidity.cauchyTransform S.μ (zp L κ qd i))) := by
    intro i
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hx : 0 ≤ 3 * (κ / (zp L κ qd i).im) ^ 2 := by positivity
    have hlim : Tendsto (fun k : ℕ => 2 / κ * (1 / ((k : ℝ) + 1) + 3 * (κ / (zp L κ qd i).im) ^ 2 / (N k : ℝ)))
        atTop (𝓝 (2 / κ * (0 + 0))) := by
      refine Tendsto.const_mul _ (Tendsto.add ?_ ?_)
      · exact tendsto_one_div_add_atTop_nhds_zero_nat
      · exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hNtop)
    refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_ (by simpa using hlim)
    filter_upwards [eventually_gt_atTop i] with k hk
    have h5 := GN_close (L := L) hκ (hzp i) (hNpos k) (B k).q S.μ
    have h6 := (hB k ⟨i, hk⟩).le
    refine h5.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have h7 : ‖sNf L (κ / (N k : ℝ)) (B k).q (zp L κ qd i) -
        sf L κ (EmpiricalRapidity.cauchyTransform S.μ) (zp L κ qd i)‖ ≤ 1 / ((k : ℝ) + 1) := h6
    rw [one_div] at h7
    linarith
  have hρ : ∀ k, ((rootP (B k) (hNpos k) : ProbabilityMeasure ℝ) : Measure ℝ) = emp (B k).q := fun k => rfl
  have hcauchy : ∀ k z, QuantumNLS.CauchyUniqueness.cauchyTransform
      ((rootP (B k) (hNpos k) : ProbabilityMeasure ℝ) : Measure ℝ) z = GN (N k) (B k).q z := by
    intro k z; rw [hρ]; exact cauchy_emp _ _
  have hη : 0 < eta0' L κ := eta0'_pos hκ
  have hconv : Tendsto (fun k => rootP (B k) (hNpos k)) atTop (𝓝 μ) := by
    refine QuantumNLS.CauchyLimitCriterion.tendsto_of_cauchy (η₀ := eta0' L κ) (q := qd)
      (g := QuantumNLS.CauchyUniqueness.cauchyTransform S.μ) (Y := fun j : ℕ => eta0' L κ + j) hη
      (TopologicalSpace.denseRange_denseSeq ℝ) (fun k => rootP (B k) (hNpos k))
      (fun j => by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith) μ (fun k => rfl) ?_ ?_ ?_
    · exact mass_tendsto S.μ hη
    · intro j
      have := hconvG (2 * j + 1)
      rw [zp_odd] at this
      simp_rw [hcauchy]
      exact this
    · intro k0
      have := hconvG (2 * k0)
      rw [zp_even] at this
      simp_rw [hcauchy]
      exact this
  obtain ⟨t, ht⟩ := hseq N hNpos B hconv hNtop
  obtain ⟨k, hk1, hk2⟩ := (ht.and (eventually_ge_atTop t)).exists
  exact hnot k (hmono t k _ _ hk2 hk1)

/-! ### 3. Uniform convergence of the transfer eigenvalue on a contour -/

theorem Gam_im_le {a b h : ℝ} (hh : 0 ≤ h) {z : ℂ} (hz : z ∈ Gam a b h) : |z.im| ≤ h := by
  rcases hz with ⟨-, h2 | h2⟩ | ⟨h2, -⟩
  · rw [h2, abs_neg, abs_of_nonneg hh]
  · rw [h2, abs_of_nonneg hh]
  · exact abs_le.2 ⟨h2.1, h2.2⟩

theorem sNf_sub_sf (L κ : ℝ) (N : ℕ) (q : Fin N → ℝ) (G : ℂ → ℂ) (z : ℂ) :
    sNf L (κ / N) q z - sf L κ G z =
      (ANf (κ / N) q z - Complex.exp (I * (κ : ℂ) * G z)) +
        ef L z * (ANf ((-κ) / N) q z - Complex.exp (I * ((-κ : ℝ) : ℂ) * G z)) := by
  have e1 : Complex.exp (I * ((-κ : ℝ) : ℂ) * G z) = Complex.exp (-(I * (κ : ℂ) * G z)) := by
    congr 1; push_cast; ring
  rw [e1, Complex.exp_neg]
  unfold sNf sf Af
  rw [neg_div]
  simp only [div_eq_mul_inv]
  ring

/-- `A_N(z; a/N) → e^{iaG(z)}` uniformly on `Γ`. -/
theorem ANf_conv {L κ : ℝ} (hκ : 0 < κ) {N : ℕ → ℕ} {hN : ∀ k, 0 < N k} {B : ∀ k, OnShellBethe L κ (N k)}
    {μ : ProbabilityMeasure ℝ} (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ))
    (hNtop : Tendsto N atTop atTop) {Γ : Set ℂ} (hΓ : IsCompact Γ) {d1 : ℝ} (hd1 : 0 < d1)
    (hsupp : ∀ z ∈ Γ, ∀ t ∈ (μ : Measure ℝ).support, d1 ≤ ‖z - t‖)
    (hroot : ∀ᶠ k in atTop, ∀ z ∈ Γ, ∀ j, d1 ≤ ‖z - (B k).q j‖) (a : ℝ) :
    Tendsto (fun p : ℕ × ℂ => ANf (a / N p.1) (B p.1).q p.2 -
      Complex.exp (I * (a : ℂ) * EmpiricalRapidity.cauchyTransform (μ : Measure ℝ) p.2))
      (atTop ×ˢ 𝓟 Γ) (𝓝 0) := by
  set G := EmpiricalRapidity.cauchyTransform (μ : Measure ℝ) with hG
  set F : Filter (ℕ × ℂ) := atTop ×ˢ 𝓟 Γ with hF
  have hU0 := unif_conv hconv hΓ hd1 hsupp hroot
  have hfst : Tendsto (Prod.fst : ℕ × ℂ → ℕ) F atTop := tendsto_fst
  -- the leading term
  have hU : Tendsto (fun p : ℕ × ℂ => (∑ j, I * ((a / N p.1 : ℝ) : ℂ) / (p.2 - ((B p.1).q j : ℂ))) -
      I * (a : ℂ) * G p.2) F (𝓝 0) := by
    have := hU0.const_mul (I * (a : ℂ))
    rw [mul_zero] at this
    refine this.congr' (Eventually.of_forall fun p => ?_)
    show I * (a : ℂ) * (((N p.1 : ℝ)⁻¹ : ℂ) * ∑ j, (p.2 - ((B p.1).q j : ℂ))⁻¹ - G p.2) =
      (∑ j, I * ((a / N p.1 : ℝ) : ℂ) / (p.2 - ((B p.1).q j : ℂ))) - I * (a : ℂ) * G p.2
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast; ring
  -- eventual smallness of the coupling
  have hc0 : Tendsto (fun k => 2 * |a / (N k : ℝ)|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => (N k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hNtop
    have h2 : Tendsto (fun k => a / (N k : ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop h1
    simpa using (h2.abs.const_mul 2)
  have hcsmall : ∀ᶠ k in atTop, 2 * |a / (N k : ℝ)| < d1 := hc0.eventually (gt_mem_nhds hd1)
  -- ℓ_N − iaG → 0
  have hell : Tendsto (fun p : ℕ × ℂ => ellf (a / N p.1) (B p.1).q p.2 - I * (a : ℂ) * G p.2) F (𝓝 0) := by
    have hbnd : Tendsto (fun p : ℕ × ℂ => (|a| / d1) ^ 2 * ((N p.1 : ℝ)⁻¹)) F (𝓝 0) := by
      have h1 : Tendsto (fun k => ((N k : ℝ))⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hNtop)
      have := (h1.comp hfst).const_mul ((|a| / d1) ^ 2)
      simpa using this
    have hlin : Tendsto (fun p : ℕ × ℂ => ellf (a / N p.1) (B p.1).q p.2 -
        ∑ j, I * ((a / N p.1 : ℝ) : ℂ) / (p.2 - ((B p.1).q j : ℂ))) F (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hbnd
      rw [hF, eventually_prod_principal_iff]
      filter_upwards [hroot, hcsmall] with k hk hks z hz
      have hpos : (0 : ℝ) < N k := by exact_mod_cast hN k
      have := ell_lin (c := a / (N k : ℝ)) (d := d1) hd1 (by linarith) (hk z hz)
      refine this.trans (le_of_eq ?_)
      rw [abs_div, abs_of_pos hpos]
      field_simp
    have := hlin.add hU
    simpa using this
  -- exponentiate
  have hex := tendsto_exp_sub_one hell
  set M : ℝ := Real.exp (|a| / d1) with hM
  have hbnd2 : Tendsto (fun p : ℕ × ℂ => M * ‖Complex.exp (ellf (a / N p.1) (B p.1).q p.2 -
      I * (a : ℂ) * G p.2) - 1‖) F (𝓝 0) := by
    have := (hex.norm).const_mul M
    simpa using this
  refine squeeze_zero_norm' ?_ hbnd2
  rw [hF, eventually_prod_principal_iff]
  filter_upwards [hroot, hcsmall] with k hk hks z hz
  have hAN : ANf (a / N k) (B k).q z = Complex.exp (ellf (a / N k) (B k).q z) :=
    AN_eq_exp (fun j => by
      have := hk z hz j
      have h2 : 2 * |a / (N k : ℝ)| < d1 := hks
      linarith)
  have hGb : ‖G z‖ ≤ 1 / d1 := by
    have := norm_cauchy_le (μ : Measure ℝ) hd1 (hsupp z hz)
    exact this
  have hy : ‖Complex.exp (I * (a : ℂ) * G z)‖ ≤ M := by
    rw [Complex.norm_exp, hM]
    refine Real.exp_le_exp.2 ?_
    have h1 : (I * (a : ℂ) * G z).re ≤ ‖I * (a : ℂ) * G z‖ := Complex.re_le_norm _
    refine h1.trans ?_
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |a| * ‖G z‖ ≤ |a| * (1 / d1) := mul_le_mul_of_nonneg_left hGb (abs_nonneg _)
      _ = |a| / d1 := by rw [mul_one_div]
  rw [hAN]
  have hid : Complex.exp (ellf (a / N k) (B k).q z) - Complex.exp (I * (a : ℂ) * G z) =
      Complex.exp (I * (a : ℂ) * G z) * (Complex.exp (ellf (a / N k) (B k).q z - I * (a : ℂ) * G z) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one, add_sub_cancel]
  rw [hid, norm_mul]
  exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)

/-- **Uniform convergence of the transfer eigenvalue** `s_N → s` on `Γ`. -/
theorem unif_sdev {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) {N : ℕ → ℕ} {hN : ∀ k, 0 < N k}
    {B : ∀ k, OnShellBethe L κ (N k)}
    {μ : ProbabilityMeasure ℝ} (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ))
    (hNtop : Tendsto N atTop atTop) {Γ : Set ℂ} (hΓ : IsCompact Γ) {d1 h : ℝ} (hd1 : 0 < d1)
    (hΓim : ∀ z ∈ Γ, |z.im| ≤ h)
    (hsupp : ∀ z ∈ Γ, ∀ t ∈ (μ : Measure ℝ).support, d1 ≤ ‖z - t‖)
    (hroot : ∀ᶠ k in atTop, ∀ z ∈ Γ, ∀ j, d1 ≤ ‖z - (B k).q j‖) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ k in atTop, ∀ z ∈ Γ,
      ‖sNf L (κ / N k) (B k).q z - sf L κ (EmpiricalRapidity.cauchyTransform (μ : Measure ℝ)) z‖ < τ := by
  have h1 := ANf_conv hκ hconv hNtop hΓ hd1 hsupp hroot κ
  have h2 := ANf_conv hκ hconv hNtop hΓ hd1 hsupp hroot (-κ)
  set K : ℝ := Real.exp (L * h) with hK
  have hbnd : Tendsto (fun p : ℕ × ℂ =>
      ‖ANf (κ / N p.1) (B p.1).q p.2 - Complex.exp (I * (κ : ℂ) *
        EmpiricalRapidity.cauchyTransform (μ : Measure ℝ) p.2)‖ +
      K * ‖ANf ((-κ) / N p.1) (B p.1).q p.2 - Complex.exp (I * ((-κ : ℝ) : ℂ) *
        EmpiricalRapidity.cauchyTransform (μ : Measure ℝ) p.2)‖) (atTop ×ˢ 𝓟 Γ) (𝓝 0) := by
    have := h1.norm.add (h2.norm.const_mul K)
    simpa using this
  have hT : Tendsto (fun p : ℕ × ℂ =>
      ‖sNf L (κ / N p.1) (B p.1).q p.2 -
        sf L κ (EmpiricalRapidity.cauchyTransform (μ : Measure ℝ)) p.2‖) (atTop ×ˢ 𝓟 Γ) (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun p => norm_nonneg _) ?_ hbnd
    rw [eventually_prod_principal_iff]
    refine Eventually.of_forall fun k z hz => ?_
    rw [sNf_sub_sf]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    refine add_le_add le_rfl (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    unfold ef
    rw [Complex.norm_exp, hK]
    refine Real.exp_le_exp.2 ?_
    have : (Complex.I * (L : ℂ) * z).re = -(L * z.im) := by simp [Complex.mul_re]
    rw [this]
    have := hΓim z hz
    have h3 : -z.im ≤ |z.im| := neg_le_abs _
    nlinarith [abs_nonneg z.im, hL]
  have := (hT.eventually (gt_mem_nhds hτ))
  rw [eventually_prod_principal_iff] at this
  exact this

/-! ### 4. The distance of a contour from the support -/

theorem gam_supp_dist {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ) {xm xp h : ℝ} (hxm : xm ∈ S.cuts)
    (hxp : xp ∈ S.cuts) (hh : 0 < h) :
    ∃ d0 > 0, ∀ z ∈ Gam xm xp h, ∀ t ∈ S.μ.support, d0 ≤ ‖z - t‖ := by
  obtain ⟨rm, hrm, hbm⟩ := Metric.isOpen_iff.1 Measure.isClosed_support.isOpen_compl xm
    (S.cuts_sub hxm)
  obtain ⟨rp, hrp, hbp⟩ := Metric.isOpen_iff.1 Measure.isClosed_support.isOpen_compl xp
    (S.cuts_sub hxp)
  have hsm : ∀ t ∈ S.μ.support, min rm rp ≤ |t - xm| := fun t ht => by
    by_contra hc; push Not at hc
    exact hbm (by rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_lt_of_le hc (min_le_left _ _)) ht
  have hsp : ∀ t ∈ S.μ.support, min rm rp ≤ |t - xp| := fun t ht => by
    by_contra hc; push Not at hc
    exact hbp (by rw [Metric.mem_ball, Real.dist_eq]; exact lt_of_lt_of_le hc (min_le_right _ _)) ht
  refine ⟨min (min rm rp) h, by positivity, fun z hz t ht => ?_⟩
  exact Gam_dist hh (hsm t ht) (hsp t ht) hz

/-! ### 5. The deviation form of the finite-probe lemma -/

theorem exists_pos_le_all {r : ℕ} (D : Fin r → ℝ) (hD : ∀ i, 0 < D i) : ∃ d : ℝ, 0 < d ∧ ∀ i, d ≤ D i := by
  have hev : ∀ᶠ d : ℝ in 𝓝[>] 0, d ∈ Set.Ioi (0 : ℝ) ∧ ∀ i, d ≤ D i := by
    refine eventually_mem_nhdsWithin.and ?_
    refine eventually_all.2 fun i => ?_
    exact Filter.Eventually.mono (nhdsWithin_le_nhds (Iio_mem_nhds (hD i)) : ∀ᶠ d in 𝓝[>] (0 : ℝ), d < D i)
      fun d hd => le_of_lt hd
  obtain ⟨d, hd1, hd2⟩ := hev.exists
  exact ⟨d, hd1, hd2⟩

/-- **PROP-009, deviation form** (`lem:B4-finite-probes` + `eq:MP-fixed-deviation`): finitely many probes force root-free fixed
contours and `|s_N − s| ≤ τ` on them. -/
theorem finite_probes_dev {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ) {r : ℕ} {n : Fin r → ℤ}
    {xm xp h : Fin r → ℝ}
    (hxm : ∀ i, xm i ∈ S.cuts) (hxp : ∀ i, xp i ∈ S.cuts) (hlt : ∀ i, xm i < xp i) (hh : ∀ i, 0 < h i)
    (h1 : ∀ i, 2 * Real.pi * (n i - 1) < exteriorForce L κ S.μ (xm i))
    (h2 : ∀ i, exteriorForce L κ S.μ (xm i) < 2 * Real.pi * n i)
    (h3 : ∀ i, 2 * Real.pi * n i < exteriorForce L κ S.μ (xp i))
    (h4 : ∀ i, exteriorForce L κ S.μ (xp i) < 2 * Real.pi * (n i + 1)) {τ : ℝ} (hτ : 0 < τ) :
    ∃ m : ℕ, ∃ z : Fin m → ℂ, (∀ j, HighHalf L κ (z j)) ∧ ∃ ε > 0, ∃ N₀ : ℕ, ∃ d > 0,
      ∀ (N : ℕ) (_ : 0 < N), N₀ ≤ N → ∀ B : OnShellBethe L κ N,
        (∀ j, ‖sNf L (κ / N) B.q (z j) - sf L κ (EmpiricalRapidity.cauchyTransform S.μ) (z j)‖ < ε) →
        ∀ i, (∀ w ∈ Gam (xm i) (xp i) (h i), ∀ j, d ≤ ‖w - ((B.q j : ℝ) : ℂ)‖) ∧
          ∀ w ∈ Gam (xm i) (xp i) (h i),
            ‖sNf L (κ / N) B.q w - sf L κ (EmpiricalRapidity.cauchyTransform S.μ) w‖ ≤ τ := by
  have hL := S.hL
  have hκ := S.hκ
  haveI : IsProbabilityMeasure S.μ := S.isProb
  let P : ℕ → ∀ N : ℕ, OnShellBethe L κ N → Prop := fun t N B =>
    ∀ i, (∀ w ∈ Gam (xm i) (xp i) (h i), ∀ j, 1 / ((t : ℝ) + 1) ≤ ‖w - ((B.q j : ℝ) : ℂ)‖) ∧
      ∀ w ∈ Gam (xm i) (xp i) (h i),
        ‖sNf L (κ / N) B.q w - sf L κ (EmpiricalRapidity.cauchyTransform S.μ) w‖ ≤ τ
  have hmono : ∀ t t' N (B : OnShellBethe L κ N), t ≤ t' → P t N B → P t' N B := by
    intro t t' N B htt hP i
    refine ⟨fun w hw j => ?_, (hP i).2⟩
    refine le_trans ?_ ((hP i).1 w hw j)
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ htt)
  have hseq : ∀ (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (B : ∀ k, OnShellBethe L κ (N k)),
      Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 (⟨S.μ, S.isProb⟩ : ProbabilityMeasure ℝ)) →
      Tendsto N atTop atTop → ∃ t, ∀ᶠ k in atTop, P t (N k) (B k) := by
    intro N hN B hconv hNtop
    have hblock : ∀ i, ∃ δ > 0, ∀ᶠ k in atTop, BlockConclusion (B k) (n i) (xm i) (xp i) δ := fun i =>
      label_block_seq S (μ := ⟨S.μ, S.isProb⟩) rfl hconv hNtop (hxm i) (hxp i) (hlt i) (h1 i) (h2 i) (h3 i) (h4 i)
    have hd0 : ∀ i, ∃ d0 > 0, ∀ z ∈ Gam (xm i) (xp i) (h i), ∀ t ∈ S.μ.support, d0 ≤ ‖z - t‖ := fun i =>
      gam_supp_dist S (hxm i) (hxp i) (hh i)
    choose δ hδ hbl using hblock
    choose d0 hd0pos hd0s using hd0
    obtain ⟨d, hd, hdD⟩ := exists_pos_le_all (fun i => min (min (δ i) (h i)) (d0 i))
      (fun i => lt_min (lt_min (hδ i) (hh i)) (hd0pos i))
    refine ⟨⌈1 / d⌉₊, ?_⟩
    have hdt : 1 / (((⌈1 / d⌉₊ : ℕ) : ℝ) + 1) ≤ d := by
      rw [div_le_iff₀ (by positivity)]
      have h5 : 1 / d ≤ (⌈1 / d⌉₊ : ℝ) := Nat.le_ceil _
      rw [div_le_iff₀ hd] at h5
      nlinarith
    have hroot : ∀ i, ∀ᶠ k in atTop, ∀ w ∈ Gam (xm i) (xp i) (h i), ∀ j, d ≤ ‖w - (((B k).q j : ℝ) : ℂ)‖ :=
      fun i => (hbl i).mono fun k hk w hw j =>
        (hdD i).trans ((min_le_left _ _).trans (Gam_dist (hh i) (hk j).2.1 (hk j).2.2 hw))
    have hdev : ∀ i, ∀ᶠ k in atTop, ∀ w ∈ Gam (xm i) (xp i) (h i),
        ‖sNf L (κ / N k) (B k).q w - sf L κ (EmpiricalRapidity.cauchyTransform S.μ) w‖ < τ := fun i =>
      unif_sdev (μ := ⟨S.μ, S.isProb⟩) hL hκ hconv hNtop (isCompact_Gam (xm i) (xp i) (h i)) hd
        (fun z hz => Gam_im_le (hh i).le hz)
        (fun z hz t ht => ((hdD i).trans (min_le_right _ _)).trans (hd0s i z hz t ht))
        (hroot i) hτ
    filter_upwards [eventually_all.2 hroot, eventually_all.2 hdev] with k hk1 hk2 i
    exact ⟨fun w hw j => hdt.trans (hk1 i w hw j), fun w hw => (hk2 i w hw).le⟩
  obtain ⟨m, z, hz, ε, hε, N₀, t, ht⟩ := probes_generic S P hmono hseq
  refine ⟨m, z, hz, ε, hε, N₀, 1 / ((t : ℝ) + 1), by positivity, fun N hN hN0 B hB i => ?_⟩
  exact ⟨(ht N hN hN0 B hB i).1, (ht N hN hN0 B hB i).2⟩

end QuantumNLS.Prop009ProbeDev

#print axioms QuantumNLS.Prop009ProbeDev.onShell_of_arr
#print axioms QuantumNLS.Prop009ProbeDev.probes_generic
#print axioms QuantumNLS.Prop009ProbeDev.unif_sdev
#print axioms QuantumNLS.Prop009ProbeDev.finite_probes_dev
