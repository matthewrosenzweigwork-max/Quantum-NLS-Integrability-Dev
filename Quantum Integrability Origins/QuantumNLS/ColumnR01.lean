import Mathlib
import QuantumNLS.ColumnR01Core
import QuantumNLS.PreparationStability
import QuantumNLS.HierarchyFlow
import QuantumNLS.Def033HierarchyR24m
import QuantumNLS.HighMomentsOps
import QuantumNLS.Def021ChartR41b

/-!
# ColumnR01: R-AA5864B7 `cor:column` — PRE-START INTERMEDIATE (named input: R-FAF88C8A)

Source: `source-text/chapters/core/projective_reconstruction.tex` (sha256
`bc1188a07b52d3a19c337ef5ba61fb006d940f5d079d0defe2730801e679a60d`), statement lines 281-303, proof 304-324;
the cited Corollary `thm:reconstruction` (R-FAF88C8A) is lines 225-240.

## Objects (all accepted / realized definitions; nothing redefined)
* `N = 1+q`; `𝓗_N = HN L (1+q)`; the complete normalized Bethe basis `Ψ_{N,m}` at coupling `κ/N`
  (`basis`, accepted UBB1 `meanField_physicalBasis`, as in DEF-029 `PhysicalAuxiliaryDensity`);
* `U_N(t) = exp(-i Σ_{r∈𝓡} t_r Q_{N,r})`: DEF-024 `HierarchyFlow.quantumFlow` in that basis (`evolved`);
* `Γ_N[φ]`: the accepted R-93D28FE1 `PreparationStability.density` (= R-BB03032A `ExactDensity.Gamma` of the gauged
  occupation coordinates) for the gauge `g` (the single gauge of `prop:audit-dynamic-gauge`, a parameter);
  `Γ_N(t) = Γ_N[U_N(t)ψ_N]` (`gammaT`);
* `Φ_t`: the DEF-024 joint hierarchy flow of a family `Fl` of Hamiltonian flows of `I_{r+1}^{(κ)}`
  (`HierarchyFlow.IsHamFlow`, every order), on smooth profiles (`Def033HierarchyR24m.jointSmooth`), with
  physical class `Def033HierarchyR24m.physical`;
* `w`: the quantum-derived chart of a realized DEF-021 chart record `C : Def021ChartR41b.Chart L κ hκ`
  (`C.Φ`, inverse `C.Ψ`); `w(t) = w(Φ_t u)` (`wt`); `P(t) = |w(t)⟩⟨w(t)|` (DEF-029 `rankOneOperator`);
* `u^{⊗N} = HighMomentsOps.wvec (1+q) (physical u)`; columns: DEF-029 `column`, `normalizedColumn`,
  `sourceColumn` (`c_N^{(b)} = Γe_b/√Γ_{bb}`).

## The named input
`ReconstructionFAF88C8AInput hκ C g Fl hFl` is the printed statement of `thm:reconstruction` (R-FAF88C8A, NOT
accepted, no author yet), stated once, for the same `C, g, Fl` as the conclusion:
"Fix the smooth unit profile `u`, the finite hierarchy set `𝓡`, and the compact time set `K`. Let `ψ_N ∈ 𝓗_N` be
normalized and satisfy `η_N := ‖ψ_N - u^{⊗N}‖ → 0`. Put `Γ_N(t) = Γ_N[U_N(t)ψ_N]`, `P(t) = |w(t)⟩⟨w(t)|`. Then
`sup_{t∈K} ‖Γ_N(t) - P(t)‖₁ → 0`."
The compact time set is a compact `K ⊆ ℕ → ℝ`; only the coordinates `t_r`, `r ∈ 𝓡`, enter both `U_N(t)` and `Φ_t`.

## Intermediate theorem
`column_intermediate` : `ReconstructionFAF88C8AInput … → ColumnAA5864B7Statement …`, the printed `cor:column`:
for every `b` with `r = |w_b(u)| > 0`: `p_N(t) = Γ_N(t)_{bb} ≥ r²/2 > 0` uniformly on `K` for large `N`;
`sup_K ‖c_N^{(b)}(t) - w(t)\overline{w_b(t)}/|w_b(t)|‖ → 0`; for large `N` the columns are nonzero and
`‖ĉ_N^{(b)}(t) - w(t)\overline{w_b(t)}/|w_b(t)|‖ ≤ 2ε_N/r`, `ε_N = sup_K ‖Γ_N(t)-P(t)‖₁`; and the `ĉ` limit.

## Argument (source lines 305-323) and the one route note
The core estimate is `ColumnR01Core.column_uniform` (literal printed inequalities).  The printed proof also uses
`|w_b(t)| = r` on `K` and `‖w(t)‖ = 1` ("`y = P(t)e_b` has norm `r`"), which the source takes from the model
conventions (`eq:frequencies`, `coordinate_conventions.tex:66`, outside the materialized `source-text`).  Here both are
DERIVED, with no extra hypothesis, from the named input itself: the input applied to the compact set `K ∪ {0}`, the
exact identity `Γ_N(t)_{nn} = Γ_N[ψ_N]_{nn}` (`U_N(t)` is diagonal in the Bethe basis, so it only rephases the gauged
coordinates; `diag_gammaT_eq`), `Φ_0 = id` (`jointSmooth_zero`) and the chart mass identity `‖w(v)‖ = ‖v‖` (`C.norm`)
give `|w_n(t)| = |w_n(u)|` for every `n` and `t ∈ K` (`moduli_conserved`), hence `‖w(t)‖ = 1` (`norm_wt`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped InnerProductSpace ComplexConjugate ComplexOrder ENNReal
open Filter Topology

noncomputable section

namespace QuantumNLS.ColumnR01

open QuantumNLS.OccupationUnitary (OneParticle oneBasis)
open QuantumNLS.AuxiliaryDensity
open QuantumNLS.PhysicalAuxiliaryDensity (sourceColumn)
open QuantumNLS.TraceClass (traceNorm)
open QuantumNLS.BetheOccupationGauge (Gauge)
open QuantumNLS.BetheCoefficientTransform (BetheBasis HN)
open QuantumNLS.HierarchyFlow (HamFlows IsHamFlow hamiltonian quantumFlow)
open QuantumNLS.Def033HierarchyR24m (Smooth physical jointSmooth smoothStep)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- The complete normalized Bethe basis `Ψ_{N,m}` at coupling `κ/N`, `N = 1+q` (accepted UBB1). -/
def basis (hκ : 0 < κ) (q : ℕ) : BetheBasis L (1 + q) :=
  QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L (1 + q) (by omega) hκ

/-- The DEF-024 family of Hamiltonian flows `Φ^{(r)}` of `I_{r+1}^{(κ)}`, restricted to `𝓡`. -/
def flows (Fl : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ)) (hFl : ∀ r, IsHamFlow L (hamiltonian L κ r) (Fl r))
    (R : Finset ℕ) : HamFlows L κ R :=
  ⟨Fl, fun r _ => hFl r⟩

/-- `U_N(t)ψ_N = exp(-i Σ_{r∈𝓡} t_r Q_{N,r}) ψ_N` (DEF-024 `quantumFlow`, `N = 1+q`). -/
def evolved (hκ : 0 < κ) (R : Finset ℕ) (t : ℕ → ℝ) (ψ : ∀ q : ℕ, HN L (1 + q)) (q : ℕ) :
    HN L (1 + q) :=
  quantumFlow (basis hκ q) κ R t (ψ q)

/-- `Γ_N(t) = Γ_N[U_N(t)ψ_N]` (accepted R-93D28FE1 `density`, i.e. R-BB03032A `Gamma` of the gauged
coordinates). -/
def gammaT (hκ : 0 < κ) (g : Gauge) (R : Finset ℕ) (ψ : ∀ q : ℕ, HN L (1 + q)) (q : ℕ)
    (t : ℕ → ℝ) : OneParticle →L[ℂ] OneParticle :=
  QuantumNLS.PreparationStability.density (basis hκ q) g (evolved hκ R t ψ q)

/-- `w(t) = w(Φ_t u)`, the quantum-derived chart at the joint hierarchy flow. -/
def wt (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) (Fl : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ))
    (hFl : ∀ r, IsHamFlow L (hamiltonian L κ r) (Fl r)) (R : Finset ℕ) (u : Smooth L)
    (t : ℕ → ℝ) : OneParticle :=
  C.Φ (physical (jointSmooth (flows Fl hFl R) t u))

/-- **NAMED INPUT (R-FAF88C8A `thm:reconstruction`, projective_reconstruction.tex:225-240), exact printed
statement**: for the smooth unit profile `u`, the finite hierarchy set `𝓡`, the compact time set `K`, and normalized
`ψ_N` with `η_N = ‖ψ_N - u^{⊗N}‖ → 0`: `sup_{t∈K} ‖Γ_N[U_N(t)ψ_N] - |w(t)⟩⟨w(t)|‖₁ → 0`. -/
def ReconstructionFAF88C8AInput (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) (g : Gauge)
    (Fl : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ)) (hFl : ∀ r, IsHamFlow L (hamiltonian L κ r) (Fl r)) :
    Prop :=
  ∀ (u : Smooth L), ‖physical u‖ = 1 →
  ∀ (R : Finset ℕ) (K : Set (ℕ → ℝ)), IsCompact K →
  ∀ (ψ : ∀ q : ℕ, HN L (1 + q)), (∀ q, ‖ψ q‖ = 1) →
    Tendsto (fun q => ‖ψ q - QuantumNLS.HighMomentsOps.wvec (1 + q) (physical u)‖) atTop (𝓝 0) →
    Tendsto (fun q => ⨆ t : K,
      traceNorm (gammaT hκ g R ψ q t - rankOneOperator (wt hκ C Fl hFl R u t))) atTop (𝓝 0)

/-- **R-AA5864B7 `cor:column`, printed statement** (projective_reconstruction.tex:281-303), in the setting of
`thm:reconstruction`: for every `b ∈ ℤ` with `r := |w_b(u)| > 0`, with
`ε_N = sup_{t∈K} ‖Γ_N(t) - P(t)‖₁`:
(i) for all sufficiently large `N`, `p_N(t) := Γ_N(t)_{bb} > 0` uniformly on `K` (a real lower bound `c > 0`);
(ii) `sup_{t∈K} ‖c_N^{(b)}(t) - w(t)\overline{w_b(t)}/|w_b(t)|‖ → 0` (`eq:column-limit`);
(iii) the exactly normalized columns `ĉ_N^{(b)}(t) = Γ_N(t)e_b/‖Γ_N(t)e_b‖` are defined for large `N`
(`Γ_N(t)e_b ≠ 0`) with error at most `2ε_N/r`;
(iv) they have the same limit. -/
def ColumnAA5864B7Statement (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) (g : Gauge)
    (Fl : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ)) (hFl : ∀ r, IsHamFlow L (hamiltonian L κ r) (Fl r)) :
    Prop :=
  ∀ (u : Smooth L), ‖physical u‖ = 1 →
  ∀ (R : Finset ℕ) (K : Set (ℕ → ℝ)), IsCompact K →
  ∀ (ψ : ∀ q : ℕ, HN L (1 + q)), (∀ q, ‖ψ q‖ = 1) →
    Tendsto (fun q => ‖ψ q - QuantumNLS.HighMomentsOps.wvec (1 + q) (physical u)‖) atTop (𝓝 0) →
  ∀ b : ℤ, 0 < ‖C.Φ (physical u) b‖ →
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ q in atTop, ∀ t ∈ K,
        (c : ℂ) ≤ ⟪oneBasis b, gammaT hκ g R ψ q t (oneBasis b)⟫_ℂ) ∧
    Tendsto (fun q => ⨆ t : K, ENNReal.ofReal
        ‖sourceColumn (gammaT hκ g R ψ q t) b - ColumnR01Core.target (wt hκ C Fl hFl R u t) b‖)
      atTop (𝓝 0) ∧
    (∀ᶠ q in atTop, ∀ t ∈ K, column (gammaT hκ g R ψ q t) b ≠ 0 ∧
        ‖normalizedColumn (gammaT hκ g R ψ q t) b - ColumnR01Core.target (wt hκ C Fl hFl R u t) b‖ ≤
          2 * (⨆ s : K, traceNorm (gammaT hκ g R ψ q s -
            rankOneOperator (wt hκ C Fl hFl R u s))).toReal / ‖C.Φ (physical u) b‖) ∧
    Tendsto (fun q => ⨆ t : K, ENNReal.ofReal
        ‖normalizedColumn (gammaT hκ g R ψ q t) b - ColumnR01Core.target (wt hκ C Fl hFl R u t) b‖)
      atTop (𝓝 0)

/-! ### `U_N(t)` only rephases the gauged occupation coordinates -/

theorem norm_coordinates_quantumFlow {q' : ℕ} (b : BetheBasis L (1 + q')) (g : Gauge) (R : Finset ℕ)
    (t : ℕ → ℝ) (φ : HN L (1 + q')) (m : QuantumNLS.Occupation.Arr (1 + q')) :
    ‖QuantumNLS.CartesianOccupationTransfer.coordinates b g (quantumFlow b κ R t φ) m‖ =
      ‖QuantumNLS.CartesianOccupationTransfer.coordinates b g φ m‖ := by
  obtain ⟨m', rfl⟩ := (QuantumNLS.BetheCoefficientTransform.marrArr (1 + q')).surjective m
  simp only [QuantumNLS.CartesianOccupationTransfer.coordinates,
    QuantumNLS.BetheCoefficientTransform.occupationCoefficient_apply,
    QuantumNLS.BetheOccupationGauge.gaugedBasis_apply, inner_smul_left, norm_mul,
    QuantumNLS.HierarchyFlow.quantumFlow_coord]
  simp [Complex.norm_exp]

/-- Diagonal entries of `Γ_N[·]` depend only on the moduli of the gauged occupation coordinates. -/
theorem diag_density_eq {q' : ℕ} (b : BetheBasis L (1 + q')) (g : Gauge) (φ φ' : HN L (1 + q'))
    (h : ∀ m, ‖QuantumNLS.CartesianOccupationTransfer.coordinates b g φ' m‖ =
      ‖QuantumNLS.CartesianOccupationTransfer.coordinates b g φ m‖) (a : ℤ) :
    ⟪oneBasis a, QuantumNLS.PreparationStability.density b g φ' (oneBasis a)⟫_ℂ =
      ⟪oneBasis a, QuantumNLS.PreparationStability.density b g φ (oneBasis a)⟫_ℂ := by
  unfold QuantumNLS.PreparationStability.density
  rw [QuantumNLS.ExactDensity.inner_Gamma, QuantumNLS.ExactDensity.inner_Gamma]
  refine tsum_congr fun ν => ?_
  rw [Complex.mul_conj', Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_pow,
    QuantumNLS.ExactDensity.norm_vEntry_sq, QuantumNLS.ExactDensity.norm_vEntry_sq, h]

/-- `Γ_N(t)_{nn} = Γ_N[ψ_N]_{nn}` for every time. -/
theorem diag_gammaT_eq (hκ : 0 < κ) (g : Gauge) (R : Finset ℕ) (ψ : ∀ q : ℕ, HN L (1 + q))
    (q : ℕ) (t : ℕ → ℝ) (n : ℤ) :
    ⟪oneBasis n, gammaT hκ g R ψ q t (oneBasis n)⟫_ℂ =
      ⟪oneBasis n, QuantumNLS.PreparationStability.density (basis hκ q) g (ψ q) (oneBasis n)⟫_ℂ :=
  diag_density_eq (basis hκ q) g (ψ q) (evolved hκ R t ψ q)
    (fun m => norm_coordinates_quantumFlow (basis hκ q) g R t (ψ q) m) n

/-! ### `Φ_0 = id` -/

omit [Fact (0 < L)] in
theorem jointSmooth_zero {R : Finset ℕ} (F : HamFlows L κ R) (u : Smooth L) :
    jointSmooth F 0 u = u := by
  unfold jointSmooth
  generalize R.sort (· ≤ ·) = l
  induction l with
  | nil => rfl
  | cons r l ih =>
    simp only [List.foldr_cons, ih]
    unfold smoothStep
    split_ifs with hr
    · exact Subtype.ext ((F.ham r hr u.val u.property).1)
    · rfl

theorem wt_zero (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) (Fl : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ))
    (hFl : ∀ r, IsHamFlow L (hamiltonian L κ r) (Fl r)) (R : Finset ℕ) (u : Smooth L) :
    wt hκ C Fl hFl R u 0 = C.Φ (physical u) := by
  unfold wt
  rw [jointSmooth_zero]

/-! ### Moduli and unit norm of `w(t)`, derived from the named input -/

/-- `|w_n(t)| = |w_n(u)|` for every `n` and `t ∈ K`, from the named input on `K ∪ {0}`. -/
theorem moduli_conserved (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) (g : Gauge)
    (Fl : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ)) (hFl : ∀ r, IsHamFlow L (hamiltonian L κ r) (Fl r))
    (H : ReconstructionFAF88C8AInput hκ C g Fl hFl)
    (u : Smooth L) (hu : ‖physical u‖ = 1) (R : Finset ℕ) (K : Set (ℕ → ℝ)) (hK : IsCompact K)
    (ψ : ∀ q : ℕ, HN L (1 + q)) (hψ : ∀ q, ‖ψ q‖ = 1)
    (hη : Tendsto (fun q => ‖ψ q - QuantumNLS.HighMomentsOps.wvec (1 + q) (physical u)‖) atTop
      (𝓝 0))
    (t : ℕ → ℝ) (ht : t ∈ K) (n : ℤ) :
    ‖wt hκ C Fl hFl R u t n‖ = ‖C.Φ (physical u) n‖ := by
  have hlim := H u hu R (insert 0 K) (hK.insert 0) ψ hψ hη
  have hd : ∀ s : (insert 0 K : Set (ℕ → ℝ)),
      Tendsto (fun q => ⟪oneBasis n, gammaT hκ g R ψ q s.val (oneBasis n)⟫_ℂ) atTop
        (𝓝 (((‖wt hκ C Fl hFl R u s.val n‖ ^ 2 : ℝ)) : ℂ)) := fun s =>
    ColumnR01Core.tendsto_diag_of_opNorm (fun q => gammaT hκ g R ψ q s.val)
      (wt hκ C Fl hFl R u s.val) n
      (ColumnR01Core.tendsto_opNorm_of_supError (T := (insert 0 K : Set (ℕ → ℝ)))
        (fun q s => gammaT hκ g R ψ q s.val) (fun s => wt hκ C Fl hFl R u s.val) hlim s)
  have h1 := hd ⟨t, Set.mem_insert_of_mem 0 ht⟩
  have h0 := hd ⟨0, Set.mem_insert 0 K⟩
  have heq : (fun q => ⟪oneBasis n, gammaT hκ g R ψ q t (oneBasis n)⟫_ℂ) =
      (fun q => ⟪oneBasis n, gammaT hκ g R ψ q 0 (oneBasis n)⟫_ℂ) := by
    funext q
    rw [diag_gammaT_eq, diag_gammaT_eq]
  simp only at h1 h0
  rw [heq] at h1
  have h2 := tendsto_nhds_unique h1 h0
  rw [wt_zero] at h2
  have h3 : ‖wt hκ C Fl hFl R u t n‖ ^ 2 = ‖C.Φ (physical u) n‖ ^ 2 := by exact_mod_cast h2
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h3

/-- `‖w(t)‖ = 1` on `K`, from the moduli and the chart mass identity `‖w(v)‖ = ‖v‖`. -/
theorem norm_wt (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) (g : Gauge)
    (Fl : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ)) (hFl : ∀ r, IsHamFlow L (hamiltonian L κ r) (Fl r))
    (H : ReconstructionFAF88C8AInput hκ C g Fl hFl)
    (u : Smooth L) (hu : ‖physical u‖ = 1) (R : Finset ℕ) (K : Set (ℕ → ℝ)) (hK : IsCompact K)
    (ψ : ∀ q : ℕ, HN L (1 + q)) (hψ : ∀ q, ‖ψ q‖ = 1)
    (hη : Tendsto (fun q => ‖ψ q - QuantumNLS.HighMomentsOps.wvec (1 + q) (physical u)‖) atTop
      (𝓝 0))
    (t : ℕ → ℝ) (ht : t ∈ K) :
    ‖wt hκ C Fl hFl R u t‖ = 1 := by
  have h := (QuantumNLS.ExactDensity.lp_sq_hasSum (wt hκ C Fl hFl R u t)).tsum_eq
  have h' := (QuantumNLS.ExactDensity.lp_sq_hasSum (C.Φ (physical u))).tsum_eq
  have hsum : (∑' n, ‖wt hκ C Fl hFl R u t n‖ ^ 2) = ∑' n, ‖C.Φ (physical u) n‖ ^ 2 :=
    tsum_congr fun n => by
      rw [moduli_conserved hκ C g Fl hFl H u hu R K hK ψ hψ hη t ht n]
  have hsq : ‖wt hκ C Fl hFl R u t‖ ^ 2 = 1 ^ 2 := by
    rw [← h, hsum, h', C.norm, hu]
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 hsq

/-! ### The intermediate theorem -/

/-- **R-AA5864B7 `cor:column`, INTERMEDIATE**: from the single named input `ReconstructionFAF88C8AInput` (the
printed `thm:reconstruction`, R-FAF88C8A), the printed column statement holds, for the same chart `C`, gauge
`g` and hierarchy flows `Fl`. -/
theorem column_intermediate (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) (g : Gauge)
    (Fl : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ)) (hFl : ∀ r, IsHamFlow L (hamiltonian L κ r) (Fl r))
    (ReconstructionFAF88C8AInput : ReconstructionFAF88C8AInput hκ C g Fl hFl) :
    ColumnAA5864B7Statement hκ C g Fl hFl := by
  intro u hu R K hK ψ hψ hη b hb
  have hlim := ReconstructionFAF88C8AInput u hu R K hK ψ hψ hη
  obtain ⟨h1, h2, h3, h4⟩ := ColumnR01Core.column_uniform (T := K)
    (fun q t => gammaT hκ g R ψ q t.val) (fun t => wt hκ C Fl hFl R u t.val) b
    (fun q t => QuantumNLS.ExactDensity.gamma_isPositive _)
    (fun t => norm_wt hκ C g Fl hFl ReconstructionFAF88C8AInput u hu R K hK ψ hψ hη t.val t.2)
    hb
    (fun t => moduli_conserved hκ C g Fl hFl ReconstructionFAF88C8AInput u hu R K hK ψ hψ hη
      t.val t.2 b)
    hlim
  refine ⟨⟨‖C.Φ (physical u) b‖ ^ 2 / 2, by positivity,
    h1.mono fun q hq t ht => (hq ⟨t, ht⟩).1⟩, h2, h3.mono fun q hq t ht => hq ⟨t, ht⟩, h4⟩

end QuantumNLS.ColumnR01

#print axioms QuantumNLS.ColumnR01.norm_coordinates_quantumFlow
#print axioms QuantumNLS.ColumnR01.diag_density_eq
#print axioms QuantumNLS.ColumnR01.jointSmooth_zero
#print axioms QuantumNLS.ColumnR01.moduli_conserved
#print axioms QuantumNLS.ColumnR01.norm_wt
#print axioms QuantumNLS.ColumnR01.column_intermediate

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.ColumnR01." ||
        n.toString.startsWith "_private.QuantumNLS.ColumnR01." then
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
  Lean.logInfo m!"ColumnR01 aggregate audit PASS: {own} own constants; {seen.size} transitive constants; standard axioms only; no held identifiers."
