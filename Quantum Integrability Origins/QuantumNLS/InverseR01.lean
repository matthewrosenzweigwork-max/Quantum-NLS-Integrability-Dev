import Mathlib
import QuantumNLS.ColumnR01
import QuantumNLS.GlobalCompatCovarianceR47a

/-!
# InverseR01: R-154AFD4C `cor:inverse` — PRE-START INTERMEDIATE (named input: R-AA5864B7)

Source: `source-text/chapters/core/projective_reconstruction.tex` (sha256
`bc1188a07b52d3a19c337ef5ba61fb006d940f5d079d0defe2730801e679a60d`), statement lines 338-346, proof 347-360.

"Applying the quantum-derived inverse `w^{-1}` to the unit columns `ĉ_N^{(b)}(t)`, gives physical profiles
converging in `L²`, uniformly on `K`, to `\overline{w_b(t)}Φ_tu/|w_b(t)|`.  This assertion uses the previously proved
continuous inverse and its `U(1)` equivariance."

## Objects
Exactly those of `ColumnR01` (same chart record `C : Def021ChartR41b.Chart L κ hκ` with `w = C.Φ`,
`w^{-1} = C.Ψ`; gauge `g`; DEF-024 flows `Fl`).  `Φ_tu` is `physical (jointSmooth (flows Fl hFl R) t u)`.

## Named input
`ColumnAA5864B7Input : ColumnR01.ColumnAA5864B7Statement hκ C g Fl hFl` — the exact printed statement of
`cor:column` (R-AA5864B7, not accepted), for the same `C, g, Fl` (NOT the Lean proof `column_intermediate`).

## Accepted inputs used
* the continuous inverse: `C.Ψ`, analytic (hence continuous), `C.left_inverse`, `C.right_inverse`
  (DEF-021 record of the accepted R-F5355ABD chart);
* `U(1)` equivariance: `GlobalCompatR47a.Extension.covariance` (accepted R-CA92819A modules) at
  `SymKind.phase γ`, for the extension built from `C` (`extension`, a verbatim copy of the field-by-field
  construction of the frozen `Def044ChartR28m.extension`, which is private there); `Ψ(0) = 0` from
  `Extension.inverse_zero`;
* the accepted R-93D28FE1 stability bound `PreparationStability.stability` (`‖Γ[φ]-Γ[φ']‖ ≤ 2‖φ-φ'‖`).

## Argument (source lines 348-357) and the one route note
The printed proof: the target columns form a compact set; if uniform convergence of the inverse images failed,
choose `N_j → ∞`, `t_j ∈ K` with errors bounded below, pass to a convergent subsequence of target columns, use
`cor:column`, and contradict continuity of the inverse; equivariance identifies the target.  Here the compactness/
continuity step is the equivalent "uniform continuity of a continuous map at a compact set"
(`IsCompact.uniformContinuousAt_of_continuousAt`, `tendstoUniformlyOn_comp_of_compact`).
ROUTE NOTE: the printed proof obtains compactness of the target columns from continuity of `t ↦ w(t)`
via `eq:frequencies` (a model convention, `coordinate_conventions.tex:66`, not part of `cor:column`'s statement).
With only the named input, continuity of `t ↦ w(t)\overline{w_b(t)}/|w_b(t)|` on `K` is DERIVED instead as a
uniform limit (`cor:column` (iv)) of the continuous maps `t ↦ ĉ_N^{(b)}(t)` (continuity: `U_N(t)` is strongly
continuous in `t` by dominated convergence, `continuous_quantumFlow`, and `Γ_N[·]` is 2-Lipschitz on unit vectors by
R-93D28FE1; the columns are nonzero on `K` for large `N` by `cor:column` (iii)).  No hypothesis is added.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped InnerProductSpace ComplexConjugate ComplexOrder ENNReal
open Filter Topology

noncomputable section

namespace QuantumNLS.InverseR01

open QuantumNLS.OccupationUnitary (OneParticle oneBasis)
open QuantumNLS.AuxiliaryDensity
open QuantumNLS.TraceClass (traceNorm)
open QuantumNLS.BetheOccupationGauge (Gauge)
open QuantumNLS.BetheCoefficientTransform (BetheBasis HN)
open QuantumNLS.BetheSpectralCharges (eigenvalue)
open QuantumNLS.HierarchyFlow (HamFlows IsHamFlow hamiltonian quantumFlow)
open QuantumNLS.Def033HierarchyR24m (Smooth physical jointSmooth)
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.ColumnR01 (basis flows evolved gammaT wt)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-! ### The continuous inverse and its `U(1)` equivariance (accepted R-F5355ABD / R-CA92819A) -/

section Equivariance

attribute [local instance] InnerProductSpace.complexToReal

/-- The R-CA92819A extension record of the DEF-021 chart `C` (field-by-field as the frozen
`Def044ChartR28m.extension`). -/
theorem extension (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) :
    GlobalCompatR47a.Extension κ hκ (Def021ChartR41b.localChart L).d
      ((Def021ChartR41b.localChart L).Φ κ) ((Def021ChartR41b.localChart L).Ψ κ) C.Φ C.Ψ := by
  refine ⟨C.analytic, C.inverse_analytic, C.left_inverse, C.right_inverse, ?_,
    C.actions, C.local_agreement⟩
  refine ⟨⟨C.Ψ, C.left_inverse, C.right_inverse, fun z => (C.inverse_analytic z).differentiableAt⟩,
    fun u => (C.analytic u).differentiableAt, ?_, C.symplectic⟩
  intro u
  obtain ⟨e, h, _⟩ := C.differential u
  exact ⟨e, congrArg (fun A : L2T L →L[ℝ] D01LocalPrimitive.K => (A : L2T L → D01LocalPrimitive.K))
    h.fderiv.symm⟩

/-- `w(e^{iγ}v) = e^{iγ}w(v)` (R-CA92819A covariance at `SymKind.phase γ`). -/
theorem chart_phase (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) (γ : ℝ) (v : L2T L) :
    C.Φ (Complex.exp ((γ : ℂ) * Complex.I) • v) = Complex.exp ((γ : ℂ) * Complex.I) • C.Φ v := by
  have h := (extension hκ C).covariance (Def021ChartR41b.localChart L).positive
    (Def021ChartR41b.localChart L).spec (QuantumNLS.Local021.SymKind.phase γ) v
  have hp : (QuantumNLS.Local021.SymKind.phase γ).phys L v = Complex.exp ((γ : ℂ) * Complex.I) • v :=
    rfl
  rw [hp] at h
  rw [h]
  apply lp.ext
  funext n
  simp [QuantumNLS.Local021.SymKind.mono, QuantumNLS.Local021.Mono.cj]

theorem chartInv_zero (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) : C.Ψ 0 = 0 :=
  (extension hκ C).inverse_zero

end Equivariance

/-- `w^{-1}(e^{iγ}z) = e^{iγ}w^{-1}(z)`. -/
theorem chartInv_phase (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) (γ : ℝ)
    (z : D01LocalPrimitive.K) :
    C.Ψ (Complex.exp ((γ : ℂ) * Complex.I) • z) = Complex.exp ((γ : ℂ) * Complex.I) • C.Ψ z := by
  have h := chart_phase hκ C γ (C.Ψ z)
  rw [C.right_inverse] at h
  rw [← h, C.left_inverse]

/-- Equivariance identifies the target: `w^{-1}(w(v)\overline{w_b(v)}/|w_b(v)|) = \overline{w_b(v)}v/|w_b(v)|`. -/
theorem chartInv_target (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) (v : L2T L) (b : ℤ) :
    C.Ψ (ColumnR01Core.target (C.Φ v) b) =
      (conj (C.Φ v b) / ((‖C.Φ v b‖ : ℝ) : ℂ)) • v := by
  unfold ColumnR01Core.target
  by_cases h0 : C.Φ v b = 0
  · rw [h0]
    simp [chartInv_zero hκ C]
  · have hc : ‖conj (C.Φ v b) / ((‖C.Φ v b‖ : ℝ) : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_norm]
      exact div_self (norm_ne_zero_iff.2 h0)
    have he := Complex.norm_mul_exp_arg_mul_I (conj (C.Φ v b) / ((‖C.Φ v b‖ : ℝ) : ℂ))
    rw [hc, Complex.ofReal_one, one_mul] at he
    rw [← he, ← chart_phase hκ C, C.left_inverse]

/-! ### Strong continuity of `t ↦ U_N(t)ψ` and continuity of the columns -/

/-- `t ↦ U_N(t)φ = exp(-iΣ_{r∈𝓡} t_r Q_{N,r})φ` is continuous (dominated convergence on Bethe coefficients). -/
theorem continuous_quantumFlow {N : ℕ} (b : BetheBasis L N) (R : Finset ℕ) (φ : HN L N) :
    Continuous (fun t : ℕ → ℝ => quantumFlow b κ R t φ) := by
  rw [continuous_iff_continuousAt]
  intro t0
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  let e : (ℕ → ℝ) → QuantumNLS.BetheLabels.MArr N → ℂ := fun t m =>
    Complex.exp (-((∑ r ∈ R, t r * eigenvalue L N (κ / N) r m : ℝ) : ℂ) * Complex.I)
  have hcoord : ∀ t m, b.repr (quantumFlow b κ R t φ) m = e t m * b.repr φ m := by
    intro t m
    rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply,
      QuantumNLS.HierarchyFlow.quantumFlow_coord]
  have hsq : ∀ t, ‖quantumFlow b κ R t φ - quantumFlow b κ R t0 φ‖ ^ 2 =
      ∑' m, ‖(e t m - e t0 m) * b.repr φ m‖ ^ 2 := by
    intro t
    have h1 := b.repr.norm_map (quantumFlow b κ R t φ - quantumFlow b κ R t0 φ)
    rw [← h1, map_sub, ← (QuantumNLS.ExactDensity.lp_sq_hasSum _).tsum_eq]
    refine tsum_congr fun m => ?_
    rw [lp.coeFn_sub, Pi.sub_apply, hcoord, hcoord, ← sub_mul]
  have he1 : ∀ s m, ‖e s m‖ = 1 := fun s m => by simp [e, Complex.norm_exp]
  have hlim : Tendsto (fun t => ∑' m, ‖(e t m - e t0 m) * b.repr φ m‖ ^ 2) (𝓝 t0) (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝 t0)
      (f := fun t m => ‖(e t m - e t0 m) * b.repr φ m‖ ^ 2) (g := fun _ => (0 : ℝ))
      (bound := fun m => 4 * ‖b.repr φ m‖ ^ 2)
      ((QuantumNLS.ExactDensity.lp_sq_hasSum (b.repr φ)).summable.mul_left 4) ?_ ?_
    · simpa using h
    · intro m
      have hc : Continuous (fun t : ℕ → ℝ => e t m) := by
        refine Complex.continuous_exp.comp (Continuous.mul ?_ continuous_const)
        refine Continuous.neg (Complex.continuous_ofReal.comp ?_)
        exact continuous_finsetSum _ fun r _ => (continuous_apply r).mul continuous_const
      have h2 : Tendsto (fun t => ‖(e t m - e t0 m) * b.repr φ m‖ ^ 2) (𝓝 t0)
          (𝓝 (‖(e t0 m - e t0 m) * b.repr φ m‖ ^ 2)) :=
        ((((hc.tendsto t0).sub_const _).mul_const _).norm).pow 2
      simpa using h2
    · refine Filter.Eventually.of_forall fun t m => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul, mul_pow]
      have h3 : ‖e t m - e t0 m‖ ≤ 2 :=
        (norm_sub_le _ _).trans (by rw [he1, he1]; norm_num)
      have h4 : ‖e t m - e t0 m‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (e t m - e t0 m)]
      nlinarith [sq_nonneg ‖b.repr φ m‖]
  have h5 : Tendsto (fun t => ‖quantumFlow b κ R t φ - quantumFlow b κ R t0 φ‖ ^ 2) (𝓝 t0)
      (𝓝 0) := by
    simp only [hsq]
    exact hlim
  have h6 := h5.sqrt
  simpa [Real.sqrt_sq_eq_abs] using h6

/-- `‖Γ_N[φ] - Γ_N[φ']‖ ≤ 2‖φ - φ'‖` for unit `φ, φ'` (accepted R-93D28FE1). -/
theorem norm_density_sub_le {q : ℕ} (b : BetheBasis L (1 + q)) (g : Gauge) (φ φ' : HN L (1 + q))
    (hφ : ‖φ‖ = 1) (hφ' : ‖φ'‖ = 1) :
    ‖QuantumNLS.PreparationStability.density b g φ - QuantumNLS.PreparationStability.density b g φ'‖ ≤
      2 * ‖φ - φ'‖ := by
  have h := QuantumNLS.PreparationStability.stability b g φ φ' hφ hφ'
  have h1 : ENNReal.ofReal ‖QuantumNLS.PreparationStability.density b g φ -
      QuantumNLS.PreparationStability.density b g φ'‖ ≤ ENNReal.ofReal (2 * ‖φ - φ'‖) :=
    (QuantumNLS.TraceClass.norm_le_traceNorm _).trans (h.1.trans h.2)
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1

/-- `t ↦ Γ_N(t)` is continuous in operator norm. -/
theorem continuous_gammaT (hκ : 0 < κ) (g : Gauge) (R : Finset ℕ) (ψ : ∀ q : ℕ, HN L (1 + q))
    (hψ : ∀ q, ‖ψ q‖ = 1) (q : ℕ) : Continuous (fun t => gammaT hκ g R ψ q t) := by
  have hU := continuous_quantumFlow (κ := κ) (basis hκ q) R (ψ q)
  rw [continuous_iff_continuousAt] at hU ⊢
  intro t0
  have h := hU t0
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero] at h ⊢
  refine squeeze_zero (fun _ => norm_nonneg _) (fun t => ?_) (by simpa using h.const_mul 2)
  exact norm_density_sub_le _ _ _ _
    (by simp only [evolved, LinearIsometryEquiv.norm_map, hψ])
    (by simp only [evolved, LinearIsometryEquiv.norm_map, hψ])

/-- Normalized columns of a continuous operator family are continuous where the column is nonzero. -/
theorem continuousOn_normalizedColumn {α : Type*} [TopologicalSpace α]
    (F : α → OneParticle →L[ℂ] OneParticle) (hF : Continuous F) (b : ℤ) (s : Set α)
    (hs : ∀ t ∈ s, column (F t) b ≠ 0) : ContinuousOn (fun t => normalizedColumn (F t) b) s := by
  intro t ht
  have hcol : Continuous (fun t => column (F t) b) := by
    show Continuous (fun t => F t (oneBasis b))
    exact hF.clm_apply continuous_const
  have hne : (((‖column (F t) b‖ : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.2 (hs t ht)
  have hn : ContinuousAt (fun x : OneParticle => (((‖x‖ : ℝ) : ℂ))⁻¹ • x) (column (F t) b) :=
    ((Complex.continuous_ofReal.comp continuous_norm).continuousAt.inv₀ hne).smul continuousAt_id
  exact (ContinuousAt.comp (f := fun t => column (F t) b) (x := t) hn
    hcol.continuousAt).continuousWithinAt

/-! ### Uniform convergence tools -/

theorem tendstoUniformlyOn_of_tendsto_iSup {α E : Type*} [NormedAddCommGroup E] (F : ℕ → α → E)
    (f : α → E) (K : Set α)
    (h : Tendsto (fun q => ⨆ t : K, ENNReal.ofReal ‖F q t - f t‖) atTop (𝓝 0)) :
    TendstoUniformlyOn F f atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [h.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε))] with q hq
  intro t ht
  have h1 : ENNReal.ofReal ‖F q t - f t‖ < ENNReal.ofReal ε :=
    lt_of_le_of_lt (le_iSup (fun s : K => ENNReal.ofReal ‖F q s - f s‖) ⟨t, ht⟩) hq
  rw [dist_eq_norm, norm_sub_rev]
  exact (ENNReal.ofReal_lt_ofReal_iff hε).1 h1

theorem tendsto_iSup_of_tendstoUniformlyOn {α E : Type*} [NormedAddCommGroup E] (F : ℕ → α → E)
    (f : α → E) (K : Set α) (h : TendstoUniformlyOn F f atTop K) :
    Tendsto (fun q => ⨆ t : K, ENNReal.ofReal ‖F q t - f t‖) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨r, -, hr, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hrpos : 0 < r := ENNReal.ofReal_pos.1 hr
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 h r hrpos] with q hq
  refine iSup_le fun t => le_trans ?_ hrε.le
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := hq t t.2
  rw [dist_eq_norm, norm_sub_rev] at h1
  exact h1.le

/-- A continuous map is uniformly continuous at a compact set, so it preserves uniform convergence to a family
with compact range (the compactness step of the printed proof). -/
theorem tendstoUniformlyOn_comp_of_compact {α E G : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup G] (Ψ : E → G) (hΨ : Continuous Ψ) (F : ℕ → α → E) (f : α → E)
    (K : Set α) (hc : IsCompact (f '' K)) (h : TendstoUniformlyOn F f atTop K) :
    TendstoUniformlyOn (fun q t => Ψ (F q t)) (fun t => Ψ (f t)) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  have hU := hc.uniformContinuousAt_of_continuousAt Ψ (fun a _ => hΨ.continuousAt)
    (Metric.dist_mem_uniformity hε)
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_uniformity_dist.1 hU
  filter_upwards [h δ hδ] with q hq
  intro t ht
  exact hδU (hq t ht) (Set.mem_image_of_mem f ht)

/-! ### The printed statement and the intermediate theorem -/

/-- **R-154AFD4C `cor:inverse`, printed statement** (projective_reconstruction.tex:338-346), in the setting of
`cor:column`: for every `b` with `|w_b(u)| > 0`, the images `w^{-1}(ĉ_N^{(b)}(t))` of the unit columns converge in
`L²`, uniformly on `K`, to `\overline{w_b(t)}Φ_tu/|w_b(t)|`. -/
def InverseStatement154AFD4C (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) (g : Gauge)
    (Fl : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ)) (hFl : ∀ r, IsHamFlow L (hamiltonian L κ r) (Fl r)) :
    Prop :=
  ∀ (u : Smooth L), ‖physical u‖ = 1 →
  ∀ (R : Finset ℕ) (K : Set (ℕ → ℝ)), IsCompact K →
  ∀ (ψ : ∀ q : ℕ, HN L (1 + q)), (∀ q, ‖ψ q‖ = 1) →
    Tendsto (fun q => ‖ψ q - QuantumNLS.HighMomentsOps.wvec (1 + q) (physical u)‖) atTop (𝓝 0) →
  ∀ b : ℤ, 0 < ‖C.Φ (physical u) b‖ →
    Tendsto (fun q => ⨆ t : K, ENNReal.ofReal
        ‖C.Ψ (normalizedColumn (gammaT hκ g R ψ q t) b) -
          (conj (wt hκ C Fl hFl R u t b) / ((‖wt hκ C Fl hFl R u t b‖ : ℝ) : ℂ)) •
            physical (jointSmooth (flows Fl hFl R) t u)‖) atTop (𝓝 0)

/-- **R-154AFD4C `cor:inverse`, INTERMEDIATE**: from the single named input `ColumnAA5864B7Input` (the printed
`cor:column`, R-AA5864B7) and the accepted continuous inverse with its `U(1)` equivariance, the printed inverse
statement holds, for the same chart `C`, gauge `g` and flows `Fl`. -/
theorem inverse_intermediate (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) (g : Gauge)
    (Fl : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ)) (hFl : ∀ r, IsHamFlow L (hamiltonian L κ r) (Fl r))
    (ColumnAA5864B7Input : ColumnR01.ColumnAA5864B7Statement hκ C g Fl hFl) :
    InverseStatement154AFD4C hκ C g Fl hFl := by
  intro u hu R K hK ψ hψ hη b hb
  obtain ⟨-, -, h3, h4⟩ := ColumnAA5864B7Input u hu R K hK ψ hψ hη b hb
  have hU : TendstoUniformlyOn (fun q t => normalizedColumn (gammaT hκ g R ψ q t) b)
      (fun t => ColumnR01Core.target (wt hκ C Fl hFl R u t) b) atTop K :=
    tendstoUniformlyOn_of_tendsto_iSup (fun q t => normalizedColumn (gammaT hκ g R ψ q t) b)
      (fun t => ColumnR01Core.target (wt hκ C Fl hFl R u t) b) K h4
  have hcont : ∃ᶠ q in atTop,
      ContinuousOn (fun t => normalizedColumn (gammaT hκ g R ψ q t) b) K := by
    refine (h3.mono fun q hq => ?_).frequently
    exact continuousOn_normalizedColumn (fun t => gammaT hκ g R ψ q t)
      (continuous_gammaT hκ g R ψ hψ q) b K (fun t ht => (hq t ht).1)
  have hy_cont : ContinuousOn (fun t => ColumnR01Core.target (wt hκ C Fl hFl R u t) b) K :=
    TendstoUniformlyOn.continuousOn hU hcont
  have hcomp : IsCompact ((fun t => ColumnR01Core.target (wt hκ C Fl hFl R u t) b) '' K) :=
    hK.image_of_continuousOn hy_cont
  have hΨ : Continuous C.Ψ :=
    continuous_iff_continuousAt.2 fun z => (C.inverse_analytic z).continuousAt
  have hV := tendstoUniformlyOn_comp_of_compact C.Ψ hΨ
    (fun q t => normalizedColumn (gammaT hκ g R ψ q t) b)
    (fun t => ColumnR01Core.target (wt hκ C Fl hFl R u t) b) K hcomp hU
  have hV' : TendstoUniformlyOn (fun q t => C.Ψ (normalizedColumn (gammaT hκ g R ψ q t) b))
      (fun t => (conj (wt hκ C Fl hFl R u t b) / ((‖wt hκ C Fl hFl R u t b‖ : ℝ) : ℂ)) •
        physical (jointSmooth (flows Fl hFl R) t u)) atTop K :=
    hV.congr_right fun t _ => chartInv_target hκ C (physical (jointSmooth (flows Fl hFl R) t u)) b
  exact tendsto_iSup_of_tendstoUniformlyOn
    (fun q t => C.Ψ (normalizedColumn (gammaT hκ g R ψ q t) b))
    (fun t => (conj (wt hκ C Fl hFl R u t b) / ((‖wt hκ C Fl hFl R u t b‖ : ℝ) : ℂ)) •
      physical (jointSmooth (flows Fl hFl R) t u)) K hV'

end QuantumNLS.InverseR01

#print axioms QuantumNLS.InverseR01.chart_phase
#print axioms QuantumNLS.InverseR01.chartInv_phase
#print axioms QuantumNLS.InverseR01.chartInv_target
#print axioms QuantumNLS.InverseR01.continuous_quantumFlow
#print axioms QuantumNLS.InverseR01.continuous_gammaT
#print axioms QuantumNLS.InverseR01.inverse_intermediate

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.InverseR01." ||
        n.toString.startsWith "_private.QuantumNLS.InverseR01." then
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
  Lean.logInfo m!"InverseR01 aggregate audit PASS: {own} own constants; {seen.size} transitive constants; standard axioms only; no held identifiers."
