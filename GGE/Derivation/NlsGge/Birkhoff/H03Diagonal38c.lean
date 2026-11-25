import NlsGge.Birkhoff.H03Diagonal38
import NlsGge.Birkhoff.H03Diagonal38b

/-! # H03 (v2 `C:cor:diagonal`): the one-parameter bare Fourier approximation

Statement (v2 l.915-923).  For the coefficients `β_j = c_j/(j!)^4` there is a deterministic
integer-valued function `m(N) → ∞` such that the bare Fourier-plane measures
`𝒵_{m(N),N}⁻¹ exp[-Σ_{j≤m(N)} β_j Q_{2j}(u)] ∏_{|n|≤N} d²û(n)` (`nuBareS38 (m N) β N`, F08) converge
weakly to `μ_W` in every fixed `H^r` (`r ∈ ℕ`).

Proof (v2 l.924-926), conditional on `B : BirkhoffInput38` and `O : OneSmoothingInput38 B`
(through F08 and H02): Theorem `C:thm:bare` (F08, on `H^r` for `r ≤ k-1` via
`F08_weak_sobolev38`) gives `ν_{k,N} ⇀ μ_k` as `N → ∞`; H02 (`H02_hierarchy_limit_38`, through the
identification `integral_muM38_reSob_eq_hierMu38`) gives `μ_k ⇀ μ_W` as `k → ∞`; the diagonal
argument `diagonal_tendsto38` (a metric for weak convergence, which exists on separable metric
spaces by Lévy–Prokhorov, is used only inside the proof) produces `m`.

Coordinates.  `ν_{m,N}` is a measure on `SobolevHilbert r`, the Fourier coefficient sequence
`(û(n))` with weight `⟨n⟩^{2r}`.  The limit is `μ_W` read in the same coordinates, `physFS38 r`
(`coeffSeq_physFS38`: the `n`-th coefficient of `physFS38 r u` is `û(n)` for `u ∈ H^r`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory ProbabilityTheory Filter Topology NlsGge.Measure NlsGge.Pilot
  NlsGge.HierarchyRiccati.Core NlsGge.Sobolev38 NlsGge.SpectralFoundations NlsGge.Weights
open scoped ENNReal BoundedContinuousFunction

namespace BirkhoffInput38

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B) (lower upper : ℝ) (c : ℕ → ℝ)
  (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper)

section Objects

include hlower hbound in
theorem coefficient_hβ38 (k : ℕ) : ∀ j ≤ k, 0 < coefficient c j :=
  fun j _ => coefficient_pos lower c hlower hbound j

/-- A probability measure from a measure with the instance. -/
def mkPM38 {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    ProbabilityMeasure α := ⟨μ, inferInstance⟩

@[simp] theorem coe_mkPM38 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] : ((mkPM38 μ : ProbabilityMeasure α) : Measure α) = μ := rfl

/-- `ν_{k,N}` on `H^r` as a probability measure (the constant `δ₀` for `k < 2`, never used). -/
def nuP38 (r k N : ℕ) : ProbabilityMeasure (SobolevHilbert (r : ℝ)) :=
  if hk : 2 ≤ k then
    haveI := isProbabilityMeasure_nuBareS38 hk (coefficient_hβ38 lower c hlower hbound k) N (r : ℝ)
    mkPM38 (nuBareS38 k (coefficient c) N (r : ℝ))
  else mkPM38 (Measure.dirac (0 : SobolevHilbert (r : ℝ)))

/-- The image of `μ_k` in `H^r` (the constant `δ₀` for `k < 2`, never used). -/
def muP38 (r k : ℕ) : ProbabilityMeasure (SobolevHilbert (r : ℝ)) :=
  if hk : 2 ≤ k then
    haveI := B.isProbabilityMeasure_muM38 hk (coefficient_hβ38 lower c hlower hbound k)
    mkPM38 ((muM38 B k (coefficient c)).map (reSob38 ((k - 1 : ℕ) : ℝ) (r : ℝ)))
  else mkPM38 (Measure.dirac (0 : SobolevHilbert (r : ℝ)))

/-- `μ_W` in `H^r` in `û`-coordinates. -/
def limP38 (r : ℕ) : ProbabilityMeasure (SobolevHilbert (r : ℝ)) :=
  haveI := B.isProbabilityMeasure_muW38 lower upper c hlower hbound hupper
  mkPM38 ((B.muW38 c).map (physFS38 r))

theorem coe_nuP38 (r k N : ℕ) (hk : 2 ≤ k) :
    ((nuP38 lower c hlower hbound r k N : ProbabilityMeasure (SobolevHilbert (r : ℝ))) :
      Measure (SobolevHilbert (r : ℝ))) = nuBareS38 k (coefficient c) N (r : ℝ) := by
  unfold nuP38
  simp only [hk, ↓reduceDIte, coe_mkPM38]

theorem coe_muP38 (r k : ℕ) (hk : 2 ≤ k) :
    ((muP38 B lower c hlower hbound r k : ProbabilityMeasure (SobolevHilbert (r : ℝ))) :
      Measure (SobolevHilbert (r : ℝ))) =
      (muM38 B k (coefficient c)).map (reSob38 ((k - 1 : ℕ) : ℝ) (r : ℝ)) := by
  unfold muP38
  simp only [hk, ↓reduceDIte, coe_mkPM38]

theorem nuP38_eq_muP38_of_lt (r k N : ℕ) (hk : ¬ 2 ≤ k) :
    nuP38 lower c hlower hbound r k N = muP38 B lower c hlower hbound r k := by
  unfold nuP38 muP38
  simp only [hk, ↓reduceDIte]

theorem coe_limP38 (r : ℕ) :
    ((B.limP38 lower upper c hlower hbound hupper r : ProbabilityMeasure (SobolevHilbert (r : ℝ))) :
      Measure (SobolevHilbert (r : ℝ))) = (B.muW38 c).map (physFS38 r) := rfl

include O hlower hbound in
theorem tendsto_nuP38 (r k : ℕ) (hrk : r < k) :
    Tendsto (fun N : ℕ => nuP38 lower c hlower hbound r k N) atTop
      (𝓝 (muP38 B lower c hlower hbound r k)) := by
  by_cases hk : 2 ≤ k
  · rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro G
    have hr : r ≤ k - 1 := by omega
    have h := B.F08_weak_sobolev38 O hk (coefficient_hβ38 lower c hlower hbound k) r hr G
    have hG : Measurable (fun u : SobolevHilbert (r : ℝ) => G u) := G.continuous.measurable
    simp only [coe_nuP38 lower c hlower hbound r k _ hk]
    rw [B.coe_muP38 lower c hlower hbound r k hk,
      integral_map (measurable_reSob38 _ _).aemeasurable hG.aestronglyMeasurable]
    exact h
  · simp only [B.nuP38_eq_muP38_of_lt lower c hlower hbound r k _ hk]
    exact tendsto_const_nhds

include hlower hbound hupper in
theorem tendsto_muP38 (r : ℕ) :
    Tendsto (fun k : ℕ => muP38 B lower c hlower hbound r k) atTop
      (𝓝 (B.limP38 lower upper c hlower hbound hupper r)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro G
  let Fc : SobolevCarrier38 (r : ℝ) →ᵇ ℝ := G.compContinuous
    ⟨fun x => ofCarrier38 (r : ℝ) (reflC38 (r : ℝ) x), continuous_physFS_comp38 r⟩
  have hH := ((B.H02_hierarchy_limit_38 lower upper c hlower hbound hupper).2.2 r).2 Fc
  have hG : Measurable (fun u : SobolevHilbert (r : ℝ) => G u) := G.continuous.measurable
  have hlim : ∫ u, G u ∂((B.limP38 lower upper c hlower hbound hupper r : ProbabilityMeasure _) :
      Measure _) = ∫ u, Fc (physH38 r u) ∂(B.muW38 c) := by
    rw [B.coe_limP38 lower upper c hlower hbound hupper r,
      integral_map (measurable_physFS38 r).aemeasurable hG.aestronglyMeasurable]
    rfl
  rw [hlim]
  refine hH.congr' ?_
  filter_upwards [eventually_ge_atTop (max 2 (r + 1))] with k hk
  have hk2 : 2 ≤ k := (le_max_left _ _).trans hk
  have hrk : r ≤ k - 1 := by have := (le_max_right _ _).trans hk; omega
  have := B.integral_muM38_reSob_eq_hierMu38 lower c hlower hbound hk2 r hrk G
  rw [B.coe_muP38 lower c hlower hbound r k hk2,
    integral_map (measurable_reSob38 _ _).aemeasurable hG.aestronglyMeasurable, this]
  rfl

end Objects

include O hlower hbound hupper in
/-- **H03 (v2 `C:cor:diagonal`), conditional on `B : BirkhoffInput38`,
`O : OneSmoothingInput38 B`; explicit form.**  There are thresholds `N_k ≥ k` such that, with the
deterministic hierarchy order `m(N) = diagOrder38 N_• N = max{k ≥ 2 : N_k ≤ N}` (value `2` before
`N_2`), for every integer `r ≥ 0`:

* each `ν_{m(N),N}` (`nuBareS38 (m N) β N r`, the law `𝒵⁻¹ exp(-Σ_{j≤m(N)} β_j Q_{2j}) ∏ d²û(n)`
  on the Fourier plane `F_N`, regarded in `H^r`) is a probability measure with `𝒵_{m(N),N} > 0`;
* for every bounded continuous `G : H^r → ℝ`,
  `∫ G dν_{m(N),N} → ∫ G(û) dμ_W` as `N → ∞`.

Here `β_j = c_j/(j!)^4` (`coefficient c j`), `0 < lower ≤ c_j ≤ upper` (v2 `eq:weight` is the case
`[1, 2]`), and `physFS38 r u` is the field `u` read as its coefficient sequence `(û(n))` in `H^r`. -/
theorem H03_diagonal_explicit_38 :
    ∃ Nk : ℕ → ℕ, (∀ k, k ≤ Nk k) ∧
      ∀ r : ℕ,
        (∀ N : ℕ, 0 < ZcalBare38 (diagOrder38 Nk N) (coefficient c) N ∧
          IsProbabilityMeasure
            (nuBareS38 (diagOrder38 Nk N) (coefficient c) N (r : ℝ))) ∧
        ∀ G : SobolevHilbert (r : ℝ) →ᵇ ℝ,
          Tendsto (fun N : ℕ =>
              ∫ u, G u ∂(nuBareS38 (diagOrder38 Nk N) (coefficient c) N (r : ℝ))) atTop
            (𝓝 (∫ u, G (physFS38 r u) ∂(B.muW38 c))) := by
  obtain ⟨Nk, hNk, hlim⟩ := diagonal_tendsto_explicit38
    (X := fun r : ℕ => ProbabilityMeasure (SobolevHilbert (r : ℝ)))
    (fun r k N => nuP38 lower c hlower hbound r k N)
    (fun r k => muP38 B lower c hlower hbound r k)
    (fun r => B.limP38 lower upper c hlower hbound hupper r)
    (fun r k hrk => B.tendsto_nuP38 O lower c hlower hbound r k hrk)
    (fun r => B.tendsto_muP38 lower upper c hlower hbound hupper r)
  refine ⟨Nk, hNk, fun r => ⟨fun N => ⟨ZcalBare_pos38 (two_le_diagOrder38 Nk N)
    (coefficient_hβ38 lower c hlower hbound _) N,
    isProbabilityMeasure_nuBareS38 (two_le_diagOrder38 Nk N)
      (coefficient_hβ38 lower c hlower hbound _) N (r : ℝ)⟩, fun G => ?_⟩⟩
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 (hlim r)) G
  have hG : Measurable (fun u : SobolevHilbert (r : ℝ) => G u) := G.continuous.measurable
  have hlim' : ∫ u, G u ∂((B.limP38 lower upper c hlower hbound hupper r : ProbabilityMeasure _) :
      Measure _) = ∫ u, G (physFS38 r u) ∂(B.muW38 c) := by
    rw [B.coe_limP38 lower upper c hlower hbound hupper r,
      integral_map (measurable_physFS38 r).aemeasurable hG.aestronglyMeasurable]
  rw [hlim'] at h
  refine h.congr fun N => ?_
  rw [coe_nuP38 lower c hlower hbound r (diagOrder38 Nk N) N (two_le_diagOrder38 Nk N)]

include O hlower hbound hupper in
/-- **H03 (v2 `C:cor:diagonal`), existential form** (as v2 states it: "there is a deterministic
integer-valued function `m(N) → ∞`").  Same conclusion as `H03_diagonal_explicit_38`, with
`m : ℕ → ℕ`, `m N → ∞`, `m N ≥ 2`. -/
theorem H03_diagonal_38 :
    ∃ m : ℕ → ℕ, Tendsto m atTop atTop ∧ (∀ N, 2 ≤ m N) ∧
      ∀ r : ℕ,
        (∀ N : ℕ, 0 < ZcalBare38 (m N) (coefficient c) N ∧
          IsProbabilityMeasure (nuBareS38 (m N) (coefficient c) N (r : ℝ))) ∧
        ∀ G : SobolevHilbert (r : ℝ) →ᵇ ℝ,
          Tendsto (fun N : ℕ => ∫ u, G u ∂(nuBareS38 (m N) (coefficient c) N (r : ℝ))) atTop
            (𝓝 (∫ u, G (physFS38 r u) ∂(B.muW38 c))) := by
  obtain ⟨Nk, hNk, h⟩ := B.H03_diagonal_explicit_38 O lower upper c hlower hbound hupper
  exact ⟨diagOrder38 Nk, tendsto_diagOrder38 Nk hNk, two_le_diagOrder38 Nk, h⟩

end BirkhoffInput38

end NlsGge.Birkhoff

end
