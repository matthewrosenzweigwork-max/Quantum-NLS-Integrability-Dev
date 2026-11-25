import Mathlib
import QuantumNLS.UniformProjR01Compact
import QuantumNLS.UniformProjR01Bridge
import QuantumNLS.InverseR01

/-!
# UniformProjR01: R-98833BEE `thm:uniform-projective` — PRE-START INTERMEDIATE (named input: R-D2F4CE8F)

Source: `source-text/chapters/core/projective_reconstruction.tex` (sha256
`bc1188a07b52d3a19c337ef5ba61fb006d940f5d079d0defe2730801e679a60d`), statement lines 369-376, proof 377-388;
`eq:uniform-projective-main` is `source-text/chapters/principal_correspondence.tex:25-30`.

"For every fixed `R`, equation `eq:uniform-projective-main` holds [`sup_{u∈𝒰_R} ‖Γ_N[u^{⊗N}] - |w(u)⟩⟨w(u)|‖₁ → 0`].
The conclusion persists if normalized preparations `ψ_N(u)` satisfy `sup_{u∈𝒰_R}‖ψ_N(u)-u^{⊗N}‖ → 0`.
For every fixed coordinate `b` and `r>0`, the normalized columns converge uniformly on `{u∈𝒰_R : |w_b(u)| ≥ r}` to
`w(u)\overline{w_b(u)}/|w_b(u)|`. Their images under the quantum-derived inverse converge uniformly in physical `L²`
to `u\overline{w_b(u)}/|w_b(u)|`. No energy preparation, positive-order Sobolev convergence or rate is asserted."

## Objects
* `𝒰_R = UniformStaticR31m.unitBall R` (unit `L²` mass, DEF-002 `H¹` norm `≤ R`), the class of the R-D2F4CE8F input.
* `w = (Def021ChartR41b.chart L κ hκ).Φ`, `w⁻¹ = (…).Ψ`: the accepted R-F5355ABD chart (DEF-021), the chart of the
  R-D2F4CE8F input.
* `N = 1+n`; `Γ_N[ψ] = PreparationStability.density (ColumnR01.basis hκ n) (fullToGauge q) ψ`, the accepted
  R-BB03032A / R-93D28FE1 density for the accepted UBB1 basis at coupling `κ/N` and the gauge `\bar q` of the
  R-D2F4CE8F full gauge `q` (`UniformProjR01Bridge`: the R31m operators `E^q_{N,ab}` are exactly the DEF-029
  pullbacks for this gauge, so `⟨ψ, E^q_{N,ab}ψ⟩ = Γ_N[ψ]_{ab}`).
* `u^{⊗N} = HighMomentsOps.wvec N u`; `normalizedColumn` (DEF-029) `Γe_b/‖Γe_b‖`; `ColumnR01Core.target w b =
  w\overline{w_b}/|w_b|`.

## Parameters carried exactly as printed
The printed corollary refers to the gauge of `thm:main`/`thm:uniform-static` ("the same gauge"); it does not mention
the schedule.  Both are explicit parameters: the full gauge `q` (appearing in the conclusion through `Γ_N`) and the
schedule `j` (appearing only in the input).  No schedule or gauge is constructed here.  Instantiating `j, q` by the
rebuilt Q06 witnesses is the job of the (future) accepted R-D2F4CE8F theorem.

## Named input (the only one)
`UniformStaticD2F4CE8FInput hκ j q := UniformStaticR31m.UniformStatic hκ j q` — the printed statement of
`thm:uniform-static` (`uniform_static.tex:2-32`) for the given schedule `j` and full gauge `q`: `j` monotone with
`j → ∞`; exterior occupations preserved; for every `R > 0` the supremum over `𝒰_R` of the maximum over
`a,b ∈ [-j(N), j(N)]` of `‖(E^q_{N,ab}-c_{ab}(u))u^{⊗N}‖ + ‖((E^q_{N,ab})^*-\bar c_{ab}(u))u^{⊗N}‖` tends to `0`; for every
`R, α > 0` the phase residuals, both missing support probabilities, the affinity error and the complex defect over
distinct eligible pairs tend to `0`; empty suprema/maxima are `0`.  This Prop was checked clause by clause against the
printed theorem (see the review record); it is used as a hypothesis on the PARAMETERS `j, q`, so the witness-provenance gap
found by Terra r248 for `∃ j q, UniformStatic hκ j q` does not enter: nothing here asserts where `j, q` come from.
Only its Cartesian clause and `j → ∞` are used ("The active set eventually contains the pair").

## Accepted predecessors used directly (Lean theorems of accepted nodes)
* R-BB03032A: `ExactDensity.gamma_isPositive`, `ExactDensity.posTrace_Gamma`, `PreparationStability.density_entry`;
* R-849FDB99: `Fidelity.uniform_upgrade`;
* R-93D28FE1: `PreparationStability.stability`;
* DEF-021/R-F5355ABD chart fields; R-CA92819A `U(1)` covariance through `InverseR01.chartInv_target`.

## Predecessors used through their ARGUMENT, not their statement (no input added)
* R-AA5864B7 `cor:column`: the printed proof uses "the normalization inequality in Corollary cor:column"; that is the
  hypothesis-free lemma `ColumnR01Core.column_estimates` (incl. `norm_normalize_sub_le`), applied pointwise in `u`.
  The printed statement of `cor:column` (`ColumnR01.ColumnAA5864B7Statement`) concerns one smooth profile and a
  compact time set; it does not apply to the profile class `𝒰_R` and is not used.
* R-154AFD4C `cor:inverse`: "the compact-target continuity argument in Corollary cor:inverse" is the hypothesis-free
  `InverseR01.tendstoUniformlyOn_comp_of_compact` plus equivariance (`InverseR01.chartInv_target`); its printed
  statement (`InverseR01.InverseStatement154AFD4C`, dynamical, one profile) is not used.
* `eq:frequencies` (not in `source-text`) is NOT used by this static proof.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate ENNReal
open Filter Topology

noncomputable section

namespace QuantumNLS.UniformProjR01

open QuantumNLS.OccupationUnitary (OneParticle oneBasis)
open QuantumNLS.AuxiliaryDensity (rankOneOperator column normalizedColumn)
open QuantumNLS.TraceClass (traceNorm)
open QuantumNLS.BetheCoefficientTransform (HN)
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.UniformProjR01Compact (UR isCompact_UR UR_mono continuous_eval tight_of_compact)
open QuantumNLS.UniformProjR01Bridge (fullToGauge norm_wvec entry_le_cartesianError cartesianError_le_four
  le_supMax supMax_nonneg)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- `w = Φ^q_{L,κ}`, the accepted DEF-021 chart (the chart of the R-D2F4CE8F input). -/
abbrev w (hκ : 0 < κ) (u : L2T L) : OneParticle := (Def021ChartR41b.chart L κ hκ).Φ u

/-- `Γ_N[ψ]`, `N = 1+n`, for the gauge `\bar q` of the full gauge `q`. -/
abbrev Γ (hκ : 0 < κ) (q : UniformStaticR31m.FullGauge) (n : ℕ) (ψ : HN L (1 + n)) :
    OneParticle →L[ℂ] OneParticle :=
  PreparationStability.density (ColumnR01.basis (L := L) hκ n) (fullToGauge q) ψ

/-- `{u ∈ 𝒰_R : |w_b(u)| ≥ r}`. -/
def cls (hκ : 0 < κ) (R : ℝ) (b : ℤ) (r : ℝ) : Set (L2T L) := {u | u ∈ UR L R ∧ r ≤ ‖w (L := L) hκ u b‖}

/-- **NAMED INPUT (R-D2F4CE8F `thm:uniform-static`, uniform_static.tex:2-32), the printed statement for the schedule
`j` and full gauge `q`.** -/
def UniformStaticD2F4CE8FInput (hκ : 0 < κ) (j : ℕ → ℕ) (q : UniformStaticR31m.FullGauge) : Prop :=
  UniformStaticR31m.UniformStatic (L := L) hκ j q

/-- **R-98833BEE `thm:uniform-projective`, printed statement** (projective_reconstruction.tex:369-376), for the
full gauge `q`: for every `R`,
(1) `eq:uniform-projective-main`: `sup_{u∈𝒰_R} ‖Γ_N[u^{⊗N}] - |w(u)⟩⟨w(u)|‖₁ → 0`;
for every family of preparations `ψ_N(u)`, normalized on `𝒰_R`, with `sup_{u∈𝒰_R} ‖ψ_N(u) - u^{⊗N}‖ → 0`:
(2) the same trace-norm convergence holds for `Γ_N[ψ_N(u)]`;
(3) for every `b` and `r > 0` the normalized columns converge uniformly on `{u∈𝒰_R : |w_b(u)| ≥ r}` to
`w(u)\overline{w_b(u)}/|w_b(u)|`;
(4) their images under `w⁻¹` converge uniformly in `L²` to `\overline{w_b(u)}u/|w_b(u)|`.
(The product preparation `ψ_N(u) = u^{⊗N}` is an instance of (2)-(4).) -/
def UniformProjectiveStatement98833BEE (hκ : 0 < κ) (q : UniformStaticR31m.FullGauge) : Prop :=
  ∀ R : ℝ,
    Tendsto (fun n => ⨆ u : UR L R,
      traceNorm (Γ hκ q n (HighMomentsOps.wvec (1 + n) (u : L2T L)) - rankOneOperator (w (L := L) hκ u)))
      atTop (𝓝 0) ∧
    ∀ ψ : ∀ n : ℕ, L2T L → HN L (1 + n), (∀ n, ∀ u ∈ UR L R, ‖ψ n u‖ = 1) →
      Tendsto (fun n => ⨆ u : UR L R,
        ENNReal.ofReal ‖ψ n u - (HighMomentsOps.wvec (1 + n) (u : L2T L) : HN L (1 + n))‖) atTop (𝓝 0) →
      Tendsto (fun n => ⨆ u : UR L R, traceNorm (Γ hκ q n (ψ n u) - rankOneOperator (w (L := L) hκ u)))
        atTop (𝓝 0) ∧
      ∀ b : ℤ, ∀ r : ℝ, 0 < r →
        Tendsto (fun n => ⨆ u : cls (L := L) hκ R b r, ENNReal.ofReal
            ‖normalizedColumn (Γ hκ q n (ψ n u)) b - ColumnR01Core.target (w (L := L) hκ u) b‖) atTop (𝓝 0) ∧
        Tendsto (fun n => ⨆ u : cls (L := L) hκ R b r, ENNReal.ofReal
            ‖(Def021ChartR41b.chart L κ hκ).Ψ (normalizedColumn (Γ hκ q n (ψ n u)) b) -
              (conj (w (L := L) hκ u b) / ((‖w (L := L) hκ u b‖ : ℝ) : ℂ)) • (u : L2T L)‖) atTop (𝓝 0)

/-! ### Elementary facts -/

theorem continuous_w (hκ : 0 < κ) : Continuous (w (L := L) hκ) :=
  continuous_iff_continuousAt.2 fun u => ((Def021ChartR41b.chart L κ hκ).analytic u).continuousAt

theorem norm_w (hκ : 0 < κ) {u : L2T L} (hu : ‖u‖ = 1) : ‖w (L := L) hκ u‖ = 1 := by
  have h := (Def021ChartR41b.chart L κ hκ).norm u
  rw [hu, one_pow] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h

theorem posTrace_Γ (hκ : 0 < κ) (q : UniformStaticR31m.FullGauge) (n : ℕ) (ψ : HN L (1 + n))
    (hψ : ‖ψ‖ = 1) : QuantumNLS.TraceClass.posTrace (Γ hκ q n ψ) = 1 := by
  show QuantumNLS.TraceClass.posTrace (ExactDensity.Gamma _) = 1
  rw [ExactDensity.posTrace_Gamma, LinearIsometryEquiv.norm_map, hψ]
  simp

theorem isPositive_Γ (hκ : 0 < κ) (q : UniformStaticR31m.FullGauge) (n : ℕ) (ψ : HN L (1 + n)) :
    (Γ hκ q n ψ).IsPositive :=
  ExactDensity.gamma_isPositive _

/-! ### Step 1: uniform entries from `thm:uniform-static` ("the active set eventually contains the pair") -/

theorem eventually_mem_pairs {j : ℕ → ℕ} (hj : Tendsto j atTop atTop) (a c : ℤ) :
    ∀ᶠ n in atTop, (a, c) ∈ UniformStaticR31m.pairs (j n) := by
  filter_upwards [tendsto_atTop.1 hj (max a.natAbs c.natAbs)] with n hn
  have h1 : (a.natAbs : ℤ) ≤ (j n : ℤ) := by exact_mod_cast le_trans (le_max_left _ _) hn
  have h2 : (c.natAbs : ℤ) ≤ (j n : ℤ) := by exact_mod_cast le_trans (le_max_right _ _) hn
  have ha := abs_le.1 ((Int.abs_eq_natAbs a).trans_le h1)
  have hc := abs_le.1 ((Int.abs_eq_natAbs c).trans_le h2)
  exact Finset.mem_product.2 ⟨Finset.mem_Icc.2 ha, Finset.mem_Icc.2 hc⟩

/-- For each fixed pair, the entry error tends to zero uniformly on `𝒰_R` (bounded by the Cartesian residual). -/
theorem uniform_entry (hκ : 0 < κ) (j : ℕ → ℕ) (q : UniformStaticR31m.FullGauge)
    (hU : UniformStaticD2F4CE8FInput (L := L) hκ j q) (R : ℝ) (a c : ℤ) :
    Tendsto (fun n => ⨆ t : UR L R,
      ‖Fidelity.entry (Γ hκ q n (HighMomentsOps.wvec (1 + n) (t : L2T L))) a c -
        w (L := L) hκ t a * conj (w (L := L) hκ t c)‖) atTop (𝓝 0) := by
  obtain ⟨-, hj, -, hcart, -⟩ := hU
  have hR' : (0 : ℝ) < max R 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hc := hcart (max R 1) hR'
  have hle : ∀ᶠ n in atTop, (⨆ t : UR L R,
      ‖Fidelity.entry (Γ hκ q n (HighMomentsOps.wvec (1 + n) (t : L2T L))) a c -
        w (L := L) hκ t a * conj (w (L := L) hκ t c)‖) ≤
      UniformStaticR31m.supMax (UniformStaticR31m.unitBall (L := L) (max R 1))
        (fun _ => UniformStaticR31m.pairs (j n)) (UniformStaticR31m.cartesianError hκ q n) := by
    filter_upwards [eventually_mem_pairs hj a c] with n hn
    refine Real.iSup_le (fun t => ?_) (supMax_nonneg _ _ _)
    have h1 : ‖Fidelity.entry (Γ hκ q n (HighMomentsOps.wvec (1 + n) (t : L2T L))) a c -
        w (L := L) hκ t a * conj (w (L := L) hκ t c)‖ ≤
        UniformStaticR31m.cartesianError hκ q n (t : L2T L) (a, c) :=
      entry_le_cartesianError hκ q n (t : L2T L) t.2.1 a c
    have h2 : UniformStaticR31m.cartesianError hκ q n (t : L2T L) (a, c) ≤
        UniformStaticR31m.supMax (UniformStaticR31m.unitBall (L := L) (max R 1))
          (fun _ => UniformStaticR31m.pairs (j n)) (UniformStaticR31m.cartesianError hκ q n) :=
      le_supMax (UniformStaticR31m.unitBall (L := L) (max R 1))
        (fun _ => UniformStaticR31m.pairs (j n))
        (UniformStaticR31m.cartesianError hκ q n) (B := 4) (by norm_num)
        (fun u hu p _ => cartesianError_le_four hκ q n u hu.1 p) (UR_mono (le_max_left R 1) t.2) hn
    exact h1.trans h2
  exact squeeze_zero' (Eventually.of_forall fun n => Real.iSup_nonneg fun _ => norm_nonneg _) hle hc

/-! ### Step 2: `eq:uniform-projective-main` (positivity, trace one, tightness, `lem:uniform-upgrade`) -/

theorem product_trace (hκ : 0 < κ) (j : ℕ → ℕ) (q : UniformStaticR31m.FullGauge)
    (hU : UniformStaticD2F4CE8FInput (L := L) hκ j q) (R : ℝ) :
    Tendsto (fun n => ⨆ u : UR L R,
      traceNorm (Γ hκ q n (HighMomentsOps.wvec (1 + n) (u : L2T L)) - rankOneOperator (w (L := L) hκ u)))
      atTop (𝓝 0) := by
  have hS : IsCompact (w (L := L) hκ '' UR L R) := (isCompact_UR R).image (continuous_w hκ)
  exact Fidelity.uniform_upgrade (fun n (t : UR L R) => Γ hκ q n (HighMomentsOps.wvec (1 + n) (t : L2T L)))
    (fun t => w (L := L) hκ t) (fun n t => isPositive_Γ hκ q n _)
    (fun n t => posTrace_Γ hκ q n _ (norm_wvec _ t.2.1)) (fun t => norm_w (L := L) hκ t.2.1)
    (tight_of_compact _ hS fun t => ⟨t, t.2, rfl⟩) (uniform_entry hκ j q hU R)

/-! ### Step 3: norm-close preparations (`prop:stability`) -/

theorem prep_trace (hκ : 0 < κ) (j : ℕ → ℕ) (q : UniformStaticR31m.FullGauge)
    (hU : UniformStaticD2F4CE8FInput (L := L) hκ j q) (R : ℝ) (ψ : ∀ n : ℕ, L2T L → HN L (1 + n))
    (hψ : ∀ n, ∀ u ∈ UR L R, ‖ψ n u‖ = 1)
    (hη : Tendsto (fun n => ⨆ u : UR L R,
      ENNReal.ofReal ‖ψ n u - (HighMomentsOps.wvec (1 + n) (u : L2T L) : HN L (1 + n))‖) atTop (𝓝 0)) :
    Tendsto (fun n => ⨆ u : UR L R, traceNorm (Γ hκ q n (ψ n u) - rankOneOperator (w (L := L) hκ u)))
      atTop (𝓝 0) := by
  have h1 := product_trace hκ j q hU R
  have h2 : Tendsto (fun n => 2 * ⨆ u : UR L R,
      ENNReal.ofReal ‖ψ n u - (HighMomentsOps.wvec (1 + n) (u : L2T L) : HN L (1 + n))‖) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul hη (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
    simpa using this
  have h3 := h2.add h1
  rw [add_zero] at h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun _ => bot_le) fun n => ?_
  refine iSup_le fun u => ?_
  have e : Γ hκ q n (ψ n u) - rankOneOperator (w (L := L) hκ u) =
      (Γ hκ q n (ψ n u) - Γ hκ q n (HighMomentsOps.wvec (1 + n) (u : L2T L))) +
        (Γ hκ q n (HighMomentsOps.wvec (1 + n) (u : L2T L)) - rankOneOperator (w (L := L) hκ u)) := by abel
  rw [e]
  refine (QuantumNLS.TraceClass.traceNorm_add_le _ _).trans (add_le_add ?_ ?_)
  · have hs := PreparationStability.stability (ColumnR01.basis (L := L) hκ n) (fullToGauge q) (ψ n u)
      (HighMomentsOps.wvec (1 + n) (u : L2T L)) (hψ n u u.2) (norm_wvec _ u.2.1)
    refine (hs.1.trans hs.2).trans ?_
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    exact mul_le_mul' le_rfl (le_iSup (fun v : UR L R =>
      ENNReal.ofReal ‖ψ n v - (HighMomentsOps.wvec (1 + n) (v : L2T L) : HN L (1 + n))‖) u)
  · exact le_iSup (fun v : UR L R =>
      traceNorm (Γ hκ q n (HighMomentsOps.wvec (1 + n) (v : L2T L)) - rankOneOperator (w (L := L) hκ v))) u

/-! ### Step 4: columns on `|w_b| ≥ r` (the normalization inequality of `cor:column`) -/

/-- Eventually every column is nonzero and the normalized column is within `2ε_N/r`, `ε_N` the uniform trace error. -/
theorem column_bound (hκ : 0 < κ) (q : UniformStaticR31m.FullGauge) (R : ℝ)
    (ψ : ∀ n : ℕ, L2T L → HN L (1 + n))
    (hε : Tendsto (fun n => ⨆ u : UR L R, traceNorm (Γ hκ q n (ψ n u) - rankOneOperator (w (L := L) hκ u)))
      atTop (𝓝 0)) (b : ℤ) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n in atTop, ∀ u ∈ cls (L := L) hκ R b r, column (Γ hκ q n (ψ n u)) b ≠ 0 ∧
      ‖normalizedColumn (Γ hκ q n (ψ n u)) b - ColumnR01Core.target (w (L := L) hκ u) b‖ ≤
        2 * (⨆ v : UR L R, traceNorm (Γ hκ q n (ψ n v) - rankOneOperator (w (L := L) hκ v))).toReal / r := by
  filter_upwards [hε.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (by positivity : (0 : ℝ) < r ^ 2 / 2)))]
    with n hn
  intro u hu
  set ε := ⨆ v : UR L R, traceNorm (Γ hκ q n (ψ n v) - rankOneOperator (w (L := L) hκ v)) with hεdef
  have hfin : ε ≠ ⊤ := ne_top_of_lt hn
  have hop : ‖Γ hκ q n (ψ n u) - rankOneOperator (w (L := L) hκ u)‖ ≤ ε.toReal := by
    refine (ENNReal.ofReal_le_iff_le_toReal hfin).1 ?_
    exact (QuantumNLS.TraceClass.norm_le_traceNorm _).trans
      (le_iSup (fun v : UR L R => traceNorm (Γ hκ q n (ψ n v) - rankOneOperator (w (L := L) hκ v))) ⟨u, hu.1⟩)
  have hru : 0 < ‖w (L := L) hκ u b‖ := lt_of_lt_of_le hr hu.2
  have hεr : ε.toReal ≤ ‖w (L := L) hκ u b‖ ^ 2 / 2 := by
    have h1 : ε.toReal ≤ r ^ 2 / 2 := ENNReal.toReal_le_of_le_ofReal (by positivity) hn.le
    have h2 : r ^ 2 ≤ ‖w (L := L) hκ u b‖ ^ 2 := pow_le_pow_left₀ hr.le hu.2 2
    linarith
  obtain ⟨-, -, hne, hbd⟩ := ColumnR01Core.column_estimates (Γ hκ q n (ψ n u)) (isPositive_Γ hκ q n _)
    (w (L := L) hκ u) (norm_w (L := L) hκ hu.1.1) b hru rfl hop hεr
  refine ⟨hne, hbd.trans ?_⟩
  exact div_le_div_of_nonneg_left (by positivity) hr hu.2

theorem column_limit (hκ : 0 < κ) (j : ℕ → ℕ) (q : UniformStaticR31m.FullGauge)
    (hU : UniformStaticD2F4CE8FInput (L := L) hκ j q) (R : ℝ) (ψ : ∀ n : ℕ, L2T L → HN L (1 + n))
    (hψ : ∀ n, ∀ u ∈ UR L R, ‖ψ n u‖ = 1)
    (hη : Tendsto (fun n => ⨆ u : UR L R,
      ENNReal.ofReal ‖ψ n u - (HighMomentsOps.wvec (1 + n) (u : L2T L) : HN L (1 + n))‖) atTop (𝓝 0))
    (b : ℤ) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n => ⨆ u : cls (L := L) hκ R b r, ENNReal.ofReal
        ‖normalizedColumn (Γ hκ q n (ψ n u)) b - ColumnR01Core.target (w (L := L) hκ u) b‖) atTop (𝓝 0) := by
  have hε := prep_trace hκ j q hU R ψ hψ hη
  have hg : Tendsto (fun n => 2 * (⨆ v : UR L R,
      traceNorm (Γ hκ q n (ψ n v) - rankOneOperator (w (L := L) hκ v))).toReal / r) atTop (𝓝 0) := by
    have h0 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hε
    have := (h0.const_mul 2).div_const r
    simpa [Function.comp_def] using this
  exact ColumnR01Core.tendsto_iSup_ofReal _ _ hg
    ((column_bound hκ q R ψ hε b hr).mono fun n hn u => (hn u u.2).2)

/-! ### Step 5: the quantum-derived inverse (compact-target continuity argument of `cor:inverse`) -/

theorem isCompact_cls (hκ : 0 < κ) (R : ℝ) (b : ℤ) (r : ℝ) : IsCompact (cls (L := L) hκ R b r) := by
  have hcl : IsClosed (cls (L := L) hκ R b r) :=
    (isCompact_UR (L := L) R).isClosed.inter
      (isClosed_le continuous_const (continuous_norm.comp ((continuous_eval b).comp (continuous_w hκ))))
  exact (isCompact_UR (L := L) R).of_isClosed_subset hcl fun u hu => hu.1

theorem continuousOn_target (hκ : 0 < κ) (R : ℝ) (b : ℤ) {r : ℝ} (hr : 0 < r) :
    ContinuousOn (fun u => ColumnR01Core.target (w (L := L) hκ u) b) (cls (L := L) hκ R b r) := by
  intro u hu
  have hne : (((‖w (L := L) hκ u b‖ : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (lt_of_lt_of_le hr hu.2).ne'
  have hev : Continuous fun v : L2T L => w (L := L) hκ v b := (continuous_eval b).comp (continuous_w hκ)
  have hcoef : ContinuousAt (fun v : L2T L => conj (w (L := L) hκ v b) / ((‖w (L := L) hκ v b‖ : ℝ) : ℂ)) u :=
    ((Complex.continuous_conj.comp hev).continuousAt).div
      ((Complex.continuous_ofReal.comp (continuous_norm.comp hev)).continuousAt) hne
  exact (hcoef.smul (continuous_w hκ).continuousAt).continuousWithinAt

theorem inverse_limit (hκ : 0 < κ) (j : ℕ → ℕ) (q : UniformStaticR31m.FullGauge)
    (hU : UniformStaticD2F4CE8FInput (L := L) hκ j q) (R : ℝ) (ψ : ∀ n : ℕ, L2T L → HN L (1 + n))
    (hψ : ∀ n, ∀ u ∈ UR L R, ‖ψ n u‖ = 1)
    (hη : Tendsto (fun n => ⨆ u : UR L R,
      ENNReal.ofReal ‖ψ n u - (HighMomentsOps.wvec (1 + n) (u : L2T L) : HN L (1 + n))‖) atTop (𝓝 0))
    (b : ℤ) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n => ⨆ u : cls (L := L) hκ R b r, ENNReal.ofReal
        ‖(Def021ChartR41b.chart L κ hκ).Ψ (normalizedColumn (Γ hκ q n (ψ n u)) b) -
          (conj (w (L := L) hκ u b) / ((‖w (L := L) hκ u b‖ : ℝ) : ℂ)) • (u : L2T L)‖) atTop (𝓝 0) := by
  let F : ℕ → L2T L → OneParticle := fun n u => normalizedColumn (Γ hκ q n (ψ n u)) b
  let f : L2T L → OneParticle := fun u => ColumnR01Core.target (w (L := L) hκ u) b
  have hU' : TendstoUniformlyOn F f atTop (cls (L := L) hκ R b r) :=
    InverseR01.tendstoUniformlyOn_of_tendsto_iSup F f (cls (L := L) hκ R b r)
      (column_limit hκ j q hU R ψ hψ hη b hr)
  have hcomp : IsCompact (f '' cls (L := L) hκ R b r) :=
    (isCompact_cls hκ R b r).image_of_continuousOn (continuousOn_target hκ R b hr)
  have hΨ : Continuous (Def021ChartR41b.chart L κ hκ).Ψ :=
    continuous_iff_continuousAt.2 fun z => ((Def021ChartR41b.chart L κ hκ).inverse_analytic z).continuousAt
  have hV := InverseR01.tendstoUniformlyOn_comp_of_compact (Def021ChartR41b.chart L κ hκ).Ψ hΨ F f
    (cls (L := L) hκ R b r) hcomp hU'
  have hV' : TendstoUniformlyOn
      (fun n u => (Def021ChartR41b.chart L κ hκ).Ψ (F n u))
      (fun u => (conj (w (L := L) hκ u b) / ((‖w (L := L) hκ u b‖ : ℝ) : ℂ)) • u) atTop
      (cls (L := L) hκ R b r) :=
    hV.congr_right fun u _ => InverseR01.chartInv_target hκ (Def021ChartR41b.chart L κ hκ) u b
  exact InverseR01.tendsto_iSup_of_tendstoUniformlyOn
    (fun n u => (Def021ChartR41b.chart L κ hκ).Ψ (F n u))
    (fun u => (conj (w (L := L) hκ u b) / ((‖w (L := L) hκ u b‖ : ℝ) : ℂ)) • u)
    (cls (L := L) hκ R b r) hV'

/-! ### The intermediate theorem -/

/-- **R-98833BEE `thm:uniform-projective`, INTERMEDIATE**: from the single named input
`UniformStaticD2F4CE8FInput` (the printed `thm:uniform-static`, R-D2F4CE8F, for the schedule `j` and full gauge `q`)
and accepted predecessors, the printed statement holds for the same gauge. -/
theorem uniform_projective_intermediate (hκ : 0 < κ) (j : ℕ → ℕ) (q : UniformStaticR31m.FullGauge)
    (UniformStaticD2F4CE8FInput : UniformStaticD2F4CE8FInput (L := L) hκ j q) :
    UniformProjectiveStatement98833BEE (L := L) hκ q := fun R =>
  ⟨product_trace hκ j q UniformStaticD2F4CE8FInput R, fun ψ hψ hη =>
    ⟨prep_trace hκ j q UniformStaticD2F4CE8FInput R ψ hψ hη, fun b _ hr =>
      ⟨column_limit hκ j q UniformStaticD2F4CE8FInput R ψ hψ hη b hr,
        inverse_limit hκ j q UniformStaticD2F4CE8FInput R ψ hψ hη b hr⟩⟩⟩

end QuantumNLS.UniformProjR01

#print axioms QuantumNLS.UniformProjR01.uniform_entry
#print axioms QuantumNLS.UniformProjR01.product_trace
#print axioms QuantumNLS.UniformProjR01.prep_trace
#print axioms QuantumNLS.UniformProjR01.column_limit
#print axioms QuantumNLS.UniformProjR01.inverse_limit
#print axioms QuantumNLS.UniformProjR01.uniform_projective_intermediate

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.UniformProjR01." ||
        n.toString.startsWith "_private.QuantumNLS.UniformProjR01." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          n.components.any (fun c => c.toString == "RegularCut") then
        throwError "Held dependency: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"UniformProjR01 aggregate audit PASS: {own} own constants; {seen.size} transitive constants; standard axioms only; no held identifiers."
