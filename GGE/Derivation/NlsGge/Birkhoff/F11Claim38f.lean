import NlsGge.Birkhoff.F11Claim38e
import NlsGge.Birkhoff.F09Limit38g

/-! # NEW-F11 (`F:cor:charge`, v2 l.1801-1819): the headline (conditional on `B`, `O`)

Source: `paper/v2.tex` l.1801-1807 (statement), l.1808-1819 (proof). Conditional on `B : BirkhoffInput38` (E01) and
`O : OneSmoothingInput38 B` (E04), exactly through the landed NEW-F09 results (`F09_38`: `Z_N → Z_W > 0`,
`inf_N Z_N > 0`, weak convergence `ν_{W,N} ⇀ μ_W` on every fixed `H^r`). The remaining ingredients are the concrete
NEW-F07 (`uniformRelativePartition_bound38`) and the `B`-free files `F11Claim38`-`38e`.

Reading of the statement. `c : BoundedCoefficients lower upper` is an admitted coefficient sequence
`0 < c₋ ≤ c_j ≤ c₊` (`eq:weight`), `β_j = NlsGge.coefficient c.val j = c_j/(j!)^4`, `ν_{W,N} = nuWN38 c N`
(`eq:fullbare`, a probability measure on `L²`), `μ_W = B.muW38 c.val`. The local charge `Q_{2j}` is
`chargeFn38 m j : L² → ℝ`, the continuous extension of the local charge to `H^{m-1}` (`2 ≤ m`, `j ≤ m-1`; equal to the
local charge `∫ (-1)^{j+1} u p_{2j+1}` on every plane field `chargeFn38_planeL2`, and `μ_W`-a.e. by `S04.06`), cleaned to
`0` off `H^{m-1}`.

`F11_chargeexp38` (`F:eq:chargeexp`): for every finite collection `t_j`, `0 ≤ t_j < β_j` (`j ≤ J`):
`∃ C, ∀ N, exp(Σ_{j≤J} t_j Q_{2j})` is `ν_{W,N}`-integrable with integral `≤ C`.

`F11_moments38` (convergence of fixed moments and finite products): for every finite family of charges
`Q_{2 j_i}` (`i : Fin n`) and powers `p_i`, `∏_i Q_{2 j_i}^{p_i}` is integrable under every `ν_{W,N}` and under `μ_W`, and
`∫ ∏_i Q_{2 j_i}^{p_i} dν_{W,N} → ∫ ∏_i Q_{2 j_i}^{p_i} dμ_W`.
(`n = 1` is "all finite moments of each fixed even charge"; `F11_moment_single38`.)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.HierarchyRiccati.Core NlsGge.HierarchyRiccati Filter Topology
open scoped ENNReal Real ContDiff

namespace BirkhoffInput38

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {lower upper : ℝ}
  (c : BoundedCoefficients lower upper)

include B O in
/-- **NEW-F11.04 + `F:eq:chargeexp`** (v2 l.1802-1805, 1813-1818):
`sup_N ∫ exp(Σ_{j≤J} t_j Q_{2j}) dν_{W,N} < ∞` for `0 ≤ t_j < β_j`. The numerator `Z_N(W-p)` is bounded uniformly by
NEW-F07 applied to the lowered class, the denominator `Z_N(W)` is bounded below by NEW-F09, `D_{p,N}` by
`tiltDet_lower38`. -/
theorem F11_chargeexp38 (m : ℕ) (hm : 2 ≤ m) (J : ℕ) (hJ : J ≤ m - 1) (t : ℕ → ℝ)
    (ht : ∀ j ≤ J, 0 ≤ t j ∧ t j < NlsGge.coefficient c.val j) :
    ∃ C : ℝ, ∀ N : ℕ,
      Integrable (fun u => Real.exp (∑ j ∈ Finset.range (J + 1), t j * chargeFn38 m j u))
          (nuWN38 c N) ∧
        ∫ u, Real.exp (∑ j ∈ Finset.range (J + 1), t j * chargeFn38 m j u) ∂(nuWN38 c N) ≤ C := by
  have ht' : TiltAdmissible38 c J t := ht
  obtain ⟨C7, hC7, hC7b⟩ := uniformRelativePartition_bound38 (tiltLower38 c J t) upper
    (tiltLower38_pos c ht') ((min_le_left _ _).trans c.property.2.1)
  obtain ⟨δZ, hδZ, hZ⟩ := B.inf_Z_pos38 O c (s := (5 / 8 : ℝ)) (by norm_num) (by norm_num)
  obtain ⟨δD, hδD, hD⟩ := tiltDet_lower38 ht'
  refine ⟨(δD)⁻¹ * (C7 / δZ), fun N => ?_⟩
  obtain ⟨hI, hE⟩ := exact_identity38 c ht' m hm (by omega) N
  refine ⟨hI, hE ▸ ?_⟩
  have hDpos := tiltDet_pos38 ht' N
  have hZpos := relativePartition38_pos c N
  have h1 : relativePartition38 (tiltedCoefficients38 c ht') N / relativePartition38 c N ≤ C7 / δZ :=
    div_le_div₀ hC7.le (hC7b _ N) hδZ (hZ N)
  have h2 : (tiltDet38 c J t N)⁻¹ ≤ δD⁻¹ := inv_anti₀ hδD (hD N)
  have h3 : 0 ≤ relativePartition38 (tiltedCoefficients38 c ht') N / relativePartition38 c N :=
    div_nonneg (relativePartition38_pos _ N).le hZpos.le
  exact mul_le_mul h2 h1 h3 (inv_nonneg.2 hδD.le)

include B O in
/-- **NEW-F11.06** (convergence of fixed moments and finite products of fixed even charges). -/
theorem F11_moments38 (m : ℕ) (hm : 2 ≤ m) (n : ℕ) (jj : Fin n → ℕ) (hjj : ∀ i, jj i ≤ m - 1)
    (p : Fin n → ℕ) :
    (∀ N : ℕ, Integrable (fun u => ∏ i, chargeFn38 m (jj i) u ^ p i) (nuWN38 c N)) ∧
      Integrable (fun u => ∏ i, chargeFn38 m (jj i) u ^ p i) (B.muW38 c.val) ∧
      Tendsto (fun N : ℕ => ∫ u, ∏ i, chargeFn38 m (jj i) u ^ p i ∂(nuWN38 c N)) atTop
        (𝓝 (∫ u, ∏ i, chargeFn38 m (jj i) u ^ p i ∂(B.muW38 c.val))) := by
  have hs : (1 : ℝ) / 2 < 5 / 8 := by norm_num
  have hs' : (5 / 8 : ℝ) < 3 / 4 := by norm_num
  have hlower := c.property.1
  have : IsProbabilityMeasure (B.muW38 c.val) :=
    B.isProbabilityMeasure_muW38 lower upper c.val hlower (fun j => (c.property.2.2 j).1)
      (fun j => (c.property.2.2 j).2)
  have : ∀ N, IsProbabilityMeasure (nuWN38 c N) := fun N => isProbabilityMeasure_nuWN38 c N
  set Q : ℕ → PhysicalL2 → ℝ := fun j u => chargeFn38 m j u with hQdef
  set F : PhysicalL2 → ℝ := fun u => ∏ i, chargeFn38 m (jj i) u ^ p i with hFdef
  have hQ0 : ∀ j ≤ m - 1, ∀ u, 0 ≤ Q j u := fun j hj u => chargeFn38_nonneg m j hm hj u
  have hF0 : ∀ u, 0 ≤ F u := fun u => Finset.prod_nonneg fun i _ =>
    pow_nonneg (chargeFn38_nonneg m _ hm (hjj i) u) _
  have hFmeas : Measurable F :=
    Finset.measurable_prod _ fun i _ => (measurable_chargeFn38 m (jj i) (hjj i)).pow_const _
  -- the exponential moment with `t_j = β_j / 2`
  set t : ℕ → ℝ := fun j => NlsGge.coefficient c.val j / 2 with htdef
  have hcoef : ∀ j, 0 < NlsGge.coefficient c.val j := fun j => by
    have := hlower.trans_le (c.property.2.2 j).1
    unfold NlsGge.coefficient; positivity
  have htpos : ∀ j ≤ m - 1, 0 < t j := fun j _ => by
    have := hcoef j; simp only [htdef]; positivity
  have htad : ∀ j ≤ m - 1, 0 ≤ t j ∧ t j < NlsGge.coefficient c.val j := fun j hj =>
    ⟨(htpos j hj).le, by have := hcoef j; simp only [htdef]; linarith⟩
  obtain ⟨Cexp, hCexp⟩ := B.F11_chargeexp38 O c m hm (m - 1) le_rfl t htad
  obtain ⟨K, hK, hKb⟩ := prod_sq_le_exp38 Q (m - 1) hQ0 t htpos n jj hjj p
  -- uniform second moments
  set M : ℝ := K * Cexp with hM
  have hsq : ∀ N, Integrable (fun u => F u ^ 2) (nuWN38 c N) ∧
      ∫ u, F u ^ 2 ∂(nuWN38 c N) ≤ M := by
    intro N
    obtain ⟨hI, hC⟩ := hCexp N
    have hdom : Integrable (fun u => K * Real.exp (∑ j ∈ Finset.range (m - 1 + 1), t j * chargeFn38 m j u))
        (nuWN38 c N) := hI.const_mul K
    refine ⟨hdom.mono' (hFmeas.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => ?_), ?_⟩
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hKb u
    · calc ∫ u, F u ^ 2 ∂(nuWN38 c N)
          ≤ ∫ u, K * Real.exp (∑ j ∈ Finset.range (m - 1 + 1), t j * chargeFn38 m j u) ∂(nuWN38 c N) :=
            integral_mono ((hdom.mono' (hFmeas.pow_const 2).aestronglyMeasurable
              (Filter.Eventually.of_forall fun u => by
                rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hKb u))) hdom
              fun u => hKb u
        _ = K * ∫ u, Real.exp (∑ j ∈ Finset.range (m - 1 + 1), t j * chargeFn38 m j u) ∂(nuWN38 c N) :=
            integral_const_mul _ _
        _ ≤ M := mul_le_mul_of_nonneg_left hC hK.le
  -- weak convergence of the truncations
  have hr : (0 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hcont : Continuous (fun y : SobolevCarrier38 ((m - 1 : ℕ) : ℝ) =>
      F (physOfCarrier38 ((m - 1 : ℕ) : ℝ) hr y)) := by
    simp only [hFdef]
    exact continuous_finset_prod _ fun i _ =>
      (continuous_chargeFn_physOfCarrier38 m (jj i) (hjj i)).pow _
  have hweak : ∀ G : PhysicalL2 → ℝ,
      Continuous (fun y : SobolevCarrier38 ((m - 1 : ℕ) : ℝ) =>
        G (physOfCarrier38 ((m - 1 : ℕ) : ℝ) hr y)) →
      (∃ M, ∀ y : SobolevCarrier38 ((m - 1 : ℕ) : ℝ),
        |G (physOfCarrier38 ((m - 1 : ℕ) : ℝ) hr y)| ≤ M) →
      Tendsto (fun N : ℕ => ∫ u, G u ∂(nuWN38 c N)) atTop (𝓝 (∫ u, G u ∂(B.muW38 c.val))) :=
    fun G hG hGb => B.weak_Sobolev38 O c hs hs' _ hr G hG hGb
  obtain ⟨⟨hF2μ, -⟩, hFμ, hFν, hlim⟩ := tendsto_integral_of_sq_bounded38 (nuWN38 c) (B.muW38 c.val)
    (fun N => inferInstance) F hF0 (fun N => hFmeas.aestronglyMeasurable)
    hFmeas.aestronglyMeasurable M hsq
    (fun R hR => hweak (fun u => min (F u) R)
      (hcont.min continuous_const)
      ⟨R, fun y => by
        rw [abs_of_nonneg (le_min (hF0 _) hR.le)]; exact min_le_right _ _⟩)
    (fun R hR => hweak (fun u => min (F u ^ 2) R)
      ((hcont.pow 2).min continuous_const)
      ⟨R, fun y => by
        rw [abs_of_nonneg (le_min (sq_nonneg _) hR.le)]; exact min_le_right _ _⟩)
  exact ⟨hFν, hFμ, hlim⟩

include B O in
/-- "All finite moments of each fixed positive even local charge" (`n = 1` of `F11_moments38`). -/
theorem F11_moment_single38 (m : ℕ) (hm : 2 ≤ m) (j : ℕ) (hj : j ≤ m - 1) (p : ℕ) :
    (∀ N : ℕ, Integrable (fun u => chargeFn38 m j u ^ p) (nuWN38 c N)) ∧
      Integrable (fun u => chargeFn38 m j u ^ p) (B.muW38 c.val) ∧
      Tendsto (fun N : ℕ => ∫ u, chargeFn38 m j u ^ p ∂(nuWN38 c N)) atTop
        (𝓝 (∫ u, chargeFn38 m j u ^ p ∂(B.muW38 c.val))) := by
  have h := B.F11_moments38 O c m hm 1 (fun _ => j) (fun _ => hj) (fun _ => p)
  simpa using h

include B O in
/-- **`F:cor:charge` (v2 l.1801-1807), conditional on `B : BirkhoffInput38`, `O : OneSmoothingInput38 B`.**
See the file docstring for the reading of every symbol. -/
theorem F11_38 (m : ℕ) (hm : 2 ≤ m) :
    (∀ (J : ℕ), J ≤ m - 1 → ∀ t : ℕ → ℝ, (∀ j ≤ J, 0 ≤ t j ∧ t j < NlsGge.coefficient c.val j) →
      ∃ C : ℝ, ∀ N : ℕ,
        Integrable (fun u => Real.exp (∑ j ∈ Finset.range (J + 1), t j * chargeFn38 m j u))
            (nuWN38 c N) ∧
          ∫ u, Real.exp (∑ j ∈ Finset.range (J + 1), t j * chargeFn38 m j u) ∂(nuWN38 c N) ≤ C) ∧
    (∀ (n : ℕ) (jj : Fin n → ℕ), (∀ i, jj i ≤ m - 1) → ∀ p : Fin n → ℕ,
      (∀ N : ℕ, Integrable (fun u => ∏ i, chargeFn38 m (jj i) u ^ p i) (nuWN38 c N)) ∧
        Integrable (fun u => ∏ i, chargeFn38 m (jj i) u ^ p i) (B.muW38 c.val) ∧
        Tendsto (fun N : ℕ => ∫ u, ∏ i, chargeFn38 m (jj i) u ^ p i ∂(nuWN38 c N)) atTop
          (𝓝 (∫ u, ∏ i, chargeFn38 m (jj i) u ^ p i ∂(B.muW38 c.val)))) :=
  ⟨fun J hJ t ht => B.F11_chargeexp38 O c m hm J hJ t ht,
    fun n jj hjj p => B.F11_moments38 O c m hm n jj hjj p⟩

end BirkhoffInput38

end NlsGge.Birkhoff
end
