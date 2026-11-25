import Mathlib
import QuantumNLS.FunctionalLinearizationParam

/-!
# PROP-014, integral-over-parameter clause: measurability replaces integrability, `F_θ` smooth near the cube

Source: `source/chapters/propagation/spectral_calculus.tex`, lines 497-598, `lem:A4-functional-linearization`
(`\ReportID{PROP-014}`), last sentence of the statement and last paragraph of the proof.  This
module imports the frozen `QuantumNLS.FunctionalLinearizationParam` (`functional_linearization_param`,
hash 582ac073) and `QuantumNLS.FunctionalLinearization` read-only and removes the two assumptions that
Terra r94 flagged:

1. the explicit Bochner integrability hypotheses `hA`, `hL` of the operator-valued integrands;
2. global smoothness (and compact support) of `F_θ`: now `F_θ` is `C^∞` on a fixed open
   neighbourhood `U` of the compact `Q ⊇ K ∪ {b_θ}` only.

## Measurability that is assumed, and why the source needs it
`H_N = N ∫ F_θ(B_θ) dν` and `H^lin = N ∫ ∑_j ∂_jF_θ(b_θ) B_{θ,j} dν` are Bochner integrals in the
Banach algebra `B(H)` (operator norm).  A Bochner integral exists only for strongly (a.e.) measurable
integrands, so the source's "the integrals are legitimate" can only mean measurable parameter
dependence.  Exactly three measurability hypotheses are assumed, nothing else:
* `hB : ∀ j, AEStronglyMeasurable (fun θ => Φ θ (coordC j)) ν` (`θ ↦ B_{θ,j}` strongly measurable in
  `B(H)`; automatically true e.g. if `θ ↦ B_{θ,j}` is norm continuous on a topological `Θ` with separable
  range, or `Θ` is countable).  By Stone–Weierstrass (`adjoin_coord_top`) and `‖Φ θ g‖ ≤ ‖g‖` this
  implies strong measurability of `θ ↦ Φ θ g` for *every* `g ∈ C(K,ℂ)`
  (`aestronglyMeasurable_apply_of_coord`), so only the coordinates need be assumed.
* `hFm : AEStronglyMeasurable (fun θ => resKd K (F θ)) ν`: `θ ↦ F_θ|_K ∈ C(K,ℂ)` strongly measurable.
  Then `θ ↦ Φ θ (F_θ|_K)` is strongly measurable (`aestronglyMeasurable_apply_comp`: approximate
  `θ ↦ F_θ|_K` by simple functions; the error is controlled by `‖Φ θ g‖ ≤ ‖g‖`).
* `hdF : ∀ j, AEStronglyMeasurable (fun θ => fderiv ℝ (F θ) (b θ) (single j 1)) ν`: `θ ↦ ∂_jF_θ(b_θ)`
  measurable.
These are strong-measurability (not weak/SOT) hypotheses because the integrals are defined in the
operator-norm Banach algebra `B(H)`; integrals in the strong operator topology would need a separate
definition that the source does not use.  Integrability then follows from `‖Φ θ g‖ ≤ ‖g‖`
(`Phi_norm_le`), the uniform bound `‖D^i F_θ‖ ≤ M` on `U` for `i = 0, 1` (so `|F_θ| ≤ M` on `K` and
`|∂_jF_θ(b_θ)| ≤ M`), and `ν` finite (`integrable_apply_comp`, `integrable_sum_smul_coord`).

## Main theorem `functional_linearization_param_meas`
For every `d` there are `m ≥ 1`, `C₀ ≥ 0` (depending only on `d`) such that for every compact `Q` in
an open `U` there is `C₁(Q,U,d) ≥ 0` with: for every finite measure space `(Θ,ν)`, compact `K`,
commuting family `Φ θ` with `hB`, `F_θ` `C^∞` on `U` with `‖D^i F_θ‖ ≤ M` on `U` (`i ≤ m`), `hFm`, `hdF`,
and the margin `hQK` (`Q` contains the closed `√d δ`-neighbourhood of `K`; this makes `K ⊆ Q`,
`b_θ ∈ Q` automatic via `infDist_le_deviation`), the Heisenberg expectations of
`H_N = HnlPK` and `H^lin = HlinP` differ by at most `ν(Θ) · (C₀C₁M) · T · C_J · δ`.
`F_θ` is replaced by the canonical extension `cutoffExt χ U F_θ = χ F_θ` (`χ = 1` near `Q`, `tsupport χ ⊆ U`,
depending only on `(Q,U)`, `exists_cutoff`) inside the proof only; it agrees with `F_θ` near `Q`, so the
Hamiltonians coincide, and `sup_seminorm_cutoffExt_le` bounds the Schwartz seminorms uniformly.

## Remaining stated limitations (nothing hidden)
* Common compact `K` and margin `hQK` stay as hypotheses: at fixed `N` with `δ > 0` the point `b_θ`
  need not lie in `K` (`infDist_le_deviation` gives only `dist(b_θ, K) ≤ √d δ`), so some margin of this form
  is genuinely necessary; for `δ_N → 0` it is automatic (`mem_of_deviation_tendsto`).
* The three measurability hypotheses are assumptions about the parameter family.  The module does not
  prove that jointly measurable (Carathéodory) `(θ,x) ↦ F_θ(x)` implies `hFm`.
* `C₁` is existential (not closed form).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NormedSpace ComplexConjugate MeasureTheory Filter Topology
open scoped InnerProductSpace ContDiff FourierTransform

noncomputable section

namespace QuantumNLS.FunctionalLinearization

variable {d : ℕ}

section Meas

variable {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ)
variable {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (Φ : Θ → C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))

/-- **Strong measurability of `θ ↦ Φ θ g` for every `g ∈ C(K,ℂ)` follows from that of the
coordinates `θ ↦ B_{θ,j} = Φ θ (x_j)`** (norm-strong measurability in `B(H)`).  The coordinates
generate `C(K,ℂ)` as a closed `*`-algebra (Stone–Weierstrass, `adjoin_coord_top`) and
`‖Φ θ g‖ ≤ ‖g‖`, so measurability passes to uniform limits. -/
theorem aestronglyMeasurable_apply_of_coord
    (hB : ∀ j, AEStronglyMeasurable (fun θ => Φ θ (coordC j)) ν) (g : C(K, ℂ)) :
    AEStronglyMeasurable (fun θ => Φ θ g) ν := by
  have hpoly : ∀ a ∈ (StarAlgebra.adjoin ℂ (Set.range (coordC (K := K)))),
      AEStronglyMeasurable (fun θ => Φ θ a) ν := by
    intro a ha
    induction ha using StarAlgebra.adjoin_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hB j
    | algebraMap r =>
      have : (fun θ => Φ θ (algebraMap ℂ C(K, ℂ) r)) = fun _ => algebraMap ℂ (H →L[ℂ] H) r :=
        funext fun θ => AlgHomClass.commutes (Φ θ) r
      rw [this]; exact aestronglyMeasurable_const
    | add x y hx hy ihx ihy =>
      have : (fun θ => Φ θ (x + y)) = fun θ => Φ θ x + Φ θ y := funext fun θ => map_add _ _ _
      rw [this]; exact ihx.add ihy
    | mul x y hx hy ihx ihy =>
      have : (fun θ => Φ θ (x * y)) = fun θ => Φ θ x * Φ θ y := funext fun θ => map_mul _ _ _
      rw [this]; exact ihx.mul ihy
    | star x hx ihx =>
      have : (fun θ => Φ θ (star x)) = fun θ => star (Φ θ x) := funext fun θ => map_star _ _
      rw [this]; exact continuous_star.comp_aestronglyMeasurable ihx
  have hg : g ∈ closure ((StarAlgebra.adjoin ℂ (Set.range (coordC (K := K))) : StarSubalgebra ℂ C(K, ℂ)) :
      Set C(K, ℂ)) := by
    have : g ∈ (StarAlgebra.adjoin ℂ (Set.range (coordC (K := K)))).topologicalClosure := by
      rw [adjoin_coord_top]; trivial
    rw [← SetLike.mem_coe, StarSubalgebra.topologicalClosure_coe] at this
    exact this
  obtain ⟨x, hxmem, hxlim⟩ := mem_closure_iff_seq_limit.mp hg
  refine aestronglyMeasurable_of_tendsto_ae atTop (fun n => hpoly (x n) (hxmem n))
    (ae_of_all _ fun θ => ?_)
  exact ((Phi_continuous (Φ θ)).tendsto g).comp hxlim

theorem aestronglyMeasurable_apply_simple
    (hall : ∀ g : C(K, ℂ), AEStronglyMeasurable (fun θ => Φ θ g) ν)
    (s : SimpleFunc Θ C(K, ℂ)) : AEStronglyMeasurable (fun θ => Φ θ (s θ)) ν := by
  refine SimpleFunc.induction (motive := fun s => AEStronglyMeasurable (fun θ => Φ θ (s θ)) ν)
    (fun c {t} ht => ?_) (fun f g _ hf hg => ?_) s
  · have : (fun θ => Φ θ ((SimpleFunc.piecewise t ht (SimpleFunc.const Θ c)
        (SimpleFunc.const Θ 0)) θ)) = t.indicator (fun θ => Φ θ c) := by
      funext θ
      by_cases h : θ ∈ t
      · simp [SimpleFunc.piecewise_apply, h]
      · simp [SimpleFunc.piecewise_apply, h]
    rw [this]; exact (hall c).indicator ht
  · have : (fun θ => Φ θ ((f + g) θ)) = fun θ => Φ θ (f θ) + Φ θ (g θ) :=
      funext fun θ => by simp [map_add]
    rw [this]; exact hf.add hg

/-- **`θ ↦ Φ θ (g θ)` is strongly measurable when `θ ↦ g θ ∈ C(K,ℂ)` is** (and the coordinates
are). -/
theorem aestronglyMeasurable_apply_comp
    (hB : ∀ j, AEStronglyMeasurable (fun θ => Φ θ (coordC j)) ν)
    (g : Θ → C(K, ℂ)) (hg : AEStronglyMeasurable g ν) :
    AEStronglyMeasurable (fun θ => Φ θ (g θ)) ν := by
  have hall := aestronglyMeasurable_apply_of_coord ν Φ hB
  obtain ⟨g', hg', hae⟩ := hg
  have h1 : AEStronglyMeasurable (fun θ => Φ θ (g' θ)) ν := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => aestronglyMeasurable_apply_simple ν Φ hall (hg'.approx n))
      (ae_of_all _ fun θ => ?_)
    exact ((Phi_continuous (Φ θ)).tendsto (g' θ)).comp (hg'.tendsto_approx θ)
  exact h1.congr (hae.mono fun θ h => by show Φ θ (g' θ) = Φ θ (g θ); rw [h])

/-- **Bochner integrability of `θ ↦ Φ θ (g θ)`** from measurability of the coordinates and of
`θ ↦ g θ`, a uniform sup-norm bound and `ν` finite. -/
theorem integrable_apply_comp [IsFiniteMeasure ν]
    (hB : ∀ j, AEStronglyMeasurable (fun θ => Φ θ (coordC j)) ν)
    (g : Θ → C(K, ℂ)) (hg : AEStronglyMeasurable g ν) {C : ℝ} (hC : ∀ θ, ‖g θ‖ ≤ C) :
    Integrable (fun θ => Φ θ (g θ)) ν :=
  (integrable_const C).mono' (aestronglyMeasurable_apply_comp ν Φ hB g hg)
    (ae_of_all _ fun θ => (Phi_norm_le (Φ θ) _).trans (hC θ))

/-- **Bochner integrability of `θ ↦ ∑_j a_j(θ) B_{θ,j}`** (real coefficient functions measurable and
uniformly bounded). -/
theorem integrable_sum_smul_coord [IsFiniteMeasure ν]
    (hB : ∀ j, AEStronglyMeasurable (fun θ => Φ θ (coordC j)) ν)
    (a : Fin d → Θ → ℝ) (ha : ∀ j, AEStronglyMeasurable (a j) ν) {M1 : ℝ}
    (hM : ∀ θ j, |a j θ| ≤ M1) :
    Integrable (fun θ => ∑ j : Fin d, ((a j θ : ℝ) : ℂ) • Φ θ (coordC j)) ν := by
  refine integrable_finsetSum _ (fun j _ => ?_)
  refine (integrable_const (M1 * ‖coordC (K := K) j‖)).mono' ?_ (ae_of_all _ fun θ => ?_)
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable (ha j)).smul (hB j)
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hM θ j) (Phi_norm_le (Φ θ) _) (norm_nonneg _)
      ((abs_nonneg _).trans (hM θ j))

end Meas


section CutoffExt

variable {U : Set (EuclideanSpace ℝ (Fin d))}

open Classical in
/-- The canonical extension of a function `F` that is smooth only on `U`: `χ F` on `U`, `0` off
`U`.  Smooth on all of the space when `tsupport χ ⊆ U`, compactly supported when `χ` is. -/
def cutoffExt (χ : EuclideanSpace ℝ (Fin d) → ℝ) (U : Set (EuclideanSpace ℝ (Fin d)))
    (F : EuclideanSpace ℝ (Fin d) → ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x => if x ∈ U then χ x * F x else 0

lemma cutoffExt_eq_on {χ F : EuclideanSpace ℝ (Fin d) → ℝ} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ U) : cutoffExt χ U F x = χ x * F x := by
  simp [cutoffExt, hx]

lemma cutoffExt_eq_zero {χ F : EuclideanSpace ℝ (Fin d) → ℝ} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∉ tsupport χ) : cutoffExt χ U F x = 0 := by
  have : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
  unfold cutoffExt; split_ifs <;> simp [this]

lemma tsupport_cutoffExt_subset {χ F : EuclideanSpace ℝ (Fin d) → ℝ} :
    tsupport (cutoffExt χ U F) ⊆ tsupport χ := by
  refine closure_minimal ?_ (isClosed_tsupport χ)
  intro x hx
  by_contra h
  exact hx (cutoffExt_eq_zero h)

lemma hasCompactSupport_cutoffExt {χ F : EuclideanSpace ℝ (Fin d) → ℝ} (hχc : HasCompactSupport χ) :
    HasCompactSupport (cutoffExt χ U F) :=
  IsCompact.of_isClosed_subset hχc (isClosed_tsupport _) tsupport_cutoffExt_subset

lemma contDiff_cutoffExt (hU : IsOpen U) {χ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχU : tsupport χ ⊆ U) {F : EuclideanSpace ℝ (Fin d) → ℝ}
    (hF : ContDiffOn ℝ ∞ F U) : ContDiff ℝ ∞ (cutoffExt χ U F) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hxU : x ∈ U
  · have h1 : ContDiffAt ℝ ∞ (fun y => χ y * F y) x :=
      hχ.contDiffAt.mul (hF.contDiffAt (hU.mem_nhds hxU))
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hxU] with y hy using cutoffExt_eq_on hy
  · have hx : x ∉ tsupport χ := fun h => hxU (hχU h)
    have : cutoffExt χ U F =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
        using cutoffExt_eq_zero hy
    exact contDiffAt_const.congr_of_eventuallyEq this

/-- **Uniform Schwartz-seminorm bound for the canonical extension of `F` smooth only on `U`.**
Same statement as `sup_seminorm_cutoff_le`, for `F` that is `C^∞` on the open set `U ⊇ tsupport χ`
only; the bounds on `D^i F` are required on `U` only. -/
theorem sup_seminorm_cutoffExt_le (hU : IsOpen U) (χ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    (s : Finset (ℕ × ℕ)) :
    ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ (F : EuclideanSpace ℝ (Fin d) → ℝ) (hF : ContDiffOn ℝ ∞ F U) (M : ℝ)
      (hM0 : 0 ≤ M)
      (hFb : ∀ i ≤ s.sup Prod.snd, ∀ x ∈ U, ‖iteratedFDeriv ℝ i F x‖ ≤ M),
      (s.sup (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin d)) ℂ))
        (schwartzOfReal (cutoffExt χ U F) (contDiff_cutoffExt hU hχ hχU hF)
          (hasCompactSupport_cutoffExt hχc)) ≤ C1 * M := by
  classical
  obtain ⟨R, hR⟩ := hχc.isCompact.isBounded.exists_norm_le
  set R0 : ℝ := max R 0 with hR0
  have hR0nn : 0 ≤ R0 := le_max_right _ _
  have hBex : ∀ i : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ B := by
    intro i
    obtain ⟨C, hC⟩ := (hχc.iteratedFDeriv (𝕜 := ℝ) i).exists_bound_of_continuous
      (hχ.continuous_iteratedFDeriv (m := i) (by exact_mod_cast le_top))
    exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩
  choose B hB0 hB using hBex
  set c : ℕ × ℕ → ℝ := fun p => R0 ^ p.1 *
    ∑ i ∈ Finset.range (p.2 + 1), (p.2.choose i : ℝ) * B i with hc
  have hc0 : ∀ p, 0 ≤ c p := fun p => by
    rw [hc]; refine mul_nonneg (pow_nonneg hR0nn _) (Finset.sum_nonneg fun i _ => ?_)
    exact mul_nonneg (Nat.cast_nonneg _) (hB0 i)
  refine ⟨∑ p ∈ s, c p, Finset.sum_nonneg fun p _ => hc0 p, ?_⟩
  intro F hF M hM0 hFb
  have hCnn : 0 ≤ (∑ p ∈ s, c p) * M := mul_nonneg (Finset.sum_nonneg fun p _ => hc0 p) hM0
  refine Seminorm.finset_sup_apply_le hCnn (fun p hp => ?_)
  have hpm : p.2 ≤ s.sup Prod.snd := Finset.le_sup (f := Prod.snd) hp
  have hcle : c p ≤ ∑ p ∈ s, c p := Finset.single_le_sum (f := c) (fun p _ => hc0 p) hp
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hcle hM0)
  show SchwartzMap.seminorm ℂ p.1 p.2 _ ≤ _
  refine SchwartzMap.seminorm_le_bound ℂ p.1 p.2 _ (mul_nonneg (hc0 p) hM0) (fun x => ?_)
  have hprod : ContDiff ℝ ∞ (cutoffExt χ U F) := contDiff_cutoffExt hU hχ hχU hF
  have hcoe : ⇑(schwartzOfReal (cutoffExt χ U F) hprod (hasCompactSupport_cutoffExt hχc)) =
      Complex.ofRealLI ∘ (cutoffExt χ U F) := rfl
  rw [hcoe, LinearIsometry.norm_iteratedFDeriv_comp_left Complex.ofRealLI hprod.contDiffAt
    (by exact_mod_cast le_top)]
  by_cases hx : x ∈ tsupport χ
  · have hxR : ‖x‖ ≤ R0 := (hR x hx).trans (le_max_left _ _)
    have hxU : x ∈ U := hχU hx
    have e1 : iteratedFDeriv ℝ p.2 (cutoffExt χ U F) x =
        iteratedFDerivWithin ℝ p.2 (fun y => χ y * F y) U x := by
      rw [← iteratedFDerivWithin_of_isOpen p.2 hU hxU]
      exact iteratedFDerivWithin_congr (fun y hy => cutoffExt_eq_on hy) hxU p.2
    have hL := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (N := ∞) hχ.contDiffOn hF
      hU.uniqueDiffOn hxU (n := p.2) (by exact_mod_cast le_top)
    have hsum : ∑ i ∈ Finset.range (p.2 + 1), (p.2.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i χ U x‖ * ‖iteratedFDerivWithin ℝ (p.2 - i) F U x‖ ≤
        (∑ i ∈ Finset.range (p.2 + 1), (p.2.choose i : ℝ) * B i) * M := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      have h1 : ‖iteratedFDerivWithin ℝ i χ U x‖ ≤ B i := by
        rw [iteratedFDerivWithin_of_isOpen i hU hxU]; exact hB i x
      have h2 : ‖iteratedFDerivWithin ℝ (p.2 - i) F U x‖ ≤ M := by
        rw [iteratedFDerivWithin_of_isOpen _ hU hxU]
        exact hFb _ ((Nat.sub_le _ _).trans hpm) x hxU
      calc (p.2.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i χ U x‖ *
            ‖iteratedFDerivWithin ℝ (p.2 - i) F U x‖
          ≤ (p.2.choose i : ℝ) * B i * M := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2
              (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hB0 i))
        _ = _ := by ring
    rw [e1]
    calc ‖x‖ ^ p.1 * ‖iteratedFDerivWithin ℝ p.2 (fun y => χ y * F y) U x‖
        ≤ R0 ^ p.1 * ((∑ i ∈ Finset.range (p.2 + 1), (p.2.choose i : ℝ) * B i) * M) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hxR _) (hL.trans hsum) (norm_nonneg _)
            (pow_nonneg hR0nn _)
      _ = c p * M := by rw [hc]; ring
  · have hxs : x ∉ tsupport (cutoffExt χ U F) := fun h => hx (tsupport_cutoffExt_subset h)
    have : iteratedFDeriv ℝ p.2 (cutoffExt χ U F) x = 0 := by
      by_contra hne
      exact hxs (support_iteratedFDeriv_subset p.2 hne)
    rw [this, norm_zero, mul_zero]
    exact mul_nonneg (hc0 p) hM0

end CutoffExt


section Final

/-- The restriction `F|_K ∈ C(K,ℂ)` of a real function continuous on `K` (and `0` otherwise, a
total convention that is never used: all uses have `F` continuous on `K`). -/
def resKd (K : Set (EuclideanSpace ℝ (Fin d))) (f : EuclideanSpace ℝ (Fin d) → ℝ) : C(K, ℂ) :=
  open Classical in
  if h : ContinuousOn f K then
    ⟨fun x : K => ((f x : ℝ) : ℂ), Complex.continuous_ofReal.comp h.restrict⟩
  else 0

lemma resKd_apply {K : Set (EuclideanSpace ℝ (Fin d))} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : ContinuousOn f K) (x : K) : resKd K f x = ((f x : ℝ) : ℂ) := by
  simp [resKd, h]

variable {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ)
variable {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (Φ : Θ → C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))

/-- `H_N = N ∫ F_θ(B_θ) dν(θ)` for `F_θ` merely continuous on `K`: `F_θ(B_θ) := Φ_θ(F_θ|_K)`. -/
def HnlPK (F : Θ → EuclideanSpace ℝ (Fin d) → ℝ) (N : ℝ) : H →L[ℂ] H :=
  (N : ℂ) • ∫ θ, Φ θ (resKd K (F θ)) ∂ν

/-- **PROP-014, integral-over-parameter clause: measurability replaces the integrability
hypotheses; `F_θ` only smooth near the cube.**

There are `m ≥ 1` and `C₀ ≥ 0` depending only on `d` such that for every compact `Q` inside an open `U`
there is `C₁ ≥ 0` depending only on `(Q, U, d)` with the following property.  Let `(Θ,ν)` be a finite
measure space, `K` compact, `Φ θ` a joint functional calculus on `C(K,ℂ)` with mutually commuting
spectral coordinates, and `F_θ` `C^∞` on `U` only (no global smoothness, no compact support) with
`‖D^i F_θ‖ ≤ M` on `U` for `i ≤ m`.  Assume only the following *measurability* (without which the
Bochner integrals defining `H_N`, `H_N^lin` have no meaning):
* `hB`: `θ ↦ B_{θ,j} = Φ θ (x_j)` is strongly measurable in `B(H)` (norm topology);
* `hFm`: `θ ↦ F_θ|_K` is strongly measurable in `C(K,ℂ)`;
* `hdF`: `θ ↦ ∂_jF_θ(b_θ)` is measurable (real valued).
No integrability hypothesis is assumed: integrability of `θ ↦ F_θ(B_θ)` and
`θ ↦ ∑_j ∂_jF_θ(b_θ) B_{θ,j}` is *proved* from `‖Φ θ g‖ ≤ ‖g‖`, the uniform bound `M` and
`ν(Θ) < ∞`.  The margin hypothesis `hQK` (`Q` contains the closed `√d δ`-neighbourhood of `K`) makes
`b_θ ∈ Q`, `K ⊆ Q` automatic.  Then the two Heisenberg expectations differ by at most
`ν(Θ) · (C₀ C₁ M) · T · C_J · δ`. -/
theorem functional_linearization_param_meas (d : ℕ) :
    ∃ (m : ℕ) (C0 : ℝ), 1 ≤ m ∧ 0 ≤ C0 ∧
      ∀ {U Q : Set (EuclideanSpace ℝ (Fin d))}, IsOpen U → IsCompact Q → Q ⊆ U →
      ∃ C1 : ℝ, 0 ≤ C1 ∧
      ∀ {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [IsFiniteMeasure ν]
        {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K]
        {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (Φ : Θ → C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
        (F : Θ → EuclideanSpace ℝ (Fin d) → ℝ) (hF : ∀ θ, ContDiffOn ℝ ∞ (F θ) U)
        (b : Θ → EuclideanSpace ℝ (Fin d))
        (hcomm : ∀ θ θ' j j', Commute (Φ θ (coordC j)) (Φ θ' (coordC j')))
        (hB : ∀ j, AEStronglyMeasurable (fun θ => Φ θ (coordC j)) ν)
        (hFm : AEStronglyMeasurable (fun θ => resKd K (F θ)) ν)
        (hdF : ∀ j, AEStronglyMeasurable
          (fun θ => fderiv ℝ (F θ) (b θ) (EuclideanSpace.single j 1)) ν)
        (N : ℝ) (hN : 0 < N) (ψ : H) (hψ : ‖ψ‖ = 1) {δ : ℝ} (hδ : 0 ≤ δ)
        (hQK : ∀ x, Metric.infDist x K ≤ Real.sqrt d * δ → x ∈ Q)
        (hψδ : ∀ θ j, ‖(Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) ψ‖ ≤ δ)
        (J : H →L[ℂ] H) {CJ : ℝ} (hCJ : 0 ≤ CJ)
        (hJ : ∀ θ j, ‖Φ θ (coordC j) * J - J * Φ θ (coordC j)‖ ≤ CJ / N)
        {M : ℝ} (hM0 : 0 ≤ M)
        (hFb : ∀ θ, ∀ i ≤ m, ∀ x ∈ U, ‖iteratedFDeriv ℝ i (F θ) x‖ ≤ M)
        (t T : ℝ) (ht : |t| ≤ T),
        ‖⟪evol (HnlPK ν Φ F N) t ψ, J (evol (HnlPK ν Φ F N) t ψ)⟫_ℂ -
          ⟪evol (HlinP ν Φ F b N) t ψ, J (evol (HlinP ν Φ F b N) t ψ)⟫_ℂ‖ ≤
          (ν Set.univ).toReal * (C0 * (C1 * M)) * T * CJ * δ := by
  obtain ⟨s, C0, hC0, hCF⟩ := CF_le_seminorms d
  refine ⟨max (s.sup Prod.snd) 1, C0, le_max_right _ _, hC0, fun {U Q} hU hQ hQU => ?_⟩
  obtain ⟨χ, hχ, hχc, hχU, W, hWo, hQW, hχW⟩ := exists_cutoff hU hQ hQU
  obtain ⟨C1, hC1, hC1b⟩ := sup_seminorm_cutoffExt_le hU χ hχ hχc hχU s
  refine ⟨C1, hC1, fun {Θ} _ ν _ {K} _ {H} _ _ _ Φ F hF b hcomm hB hFm hdF N hN ψ hψ {δ} hδ hQK
    hψδ J {CJ} hCJ hJ {M} hM0 hFb t T ht => ?_⟩
  have : Nontrivial H := ⟨⟨ψ, 0, fun h => by rw [h] at hψ; simp at hψ⟩⟩
  have hbQ : ∀ θ, b θ ∈ Q := fun θ => hQK _ (by
    by_cases hKne : K.Nonempty
    · exact infDist_le_deviation (Φ θ) hKne (b θ) ψ hψ hδ (hψδ θ)
    · have : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
      subst this
      simp only [Metric.infDist_empty]
      positivity)
  have hKQ : ∀ x ∈ K, x ∈ Q := fun x hx => hQK x (by
    rw [Metric.infDist_zero_of_mem hx]; positivity)
  have hKU : K ⊆ U := fun x hx => hQU (hKQ x hx)
  have hFK : ∀ θ, ContinuousOn (F θ) K := fun θ => (hF θ).continuousOn.mono hKU
  set F' : Θ → EuclideanSpace ℝ (Fin d) → ℝ := fun θ => cutoffExt χ U (F θ) with hF'def
  have hF' : ∀ θ, ContDiff ℝ ∞ (F' θ) := fun θ => contDiff_cutoffExt hU hχ hχU (hF θ)
  have hF'c : ∀ θ, HasCompactSupport (F' θ) := fun θ => hasCompactSupport_cutoffExt hχc
  have hWU : ∀ x ∈ W, x ∈ U := fun x hx =>
    hχU (subset_tsupport _ (Function.mem_support.mpr (by rw [hχW x hx]; exact one_ne_zero)))
  have hFF' : ∀ θ, ∀ x ∈ W, F' θ x = F θ x := fun θ x hx => by
    simp only [hF'def]; rw [cutoffExt_eq_on (hWU x hx), hχW x hx, one_mul]
  have hFop : ∀ θ, Fop (Φ θ) (F' θ) (hF' θ).continuous = Φ θ (resKd K (F θ)) := by
    intro θ
    unfold Fop
    congr 1
    refine ContinuousMap.ext fun x => ?_
    simp only [liftC, ContinuousMap.coe_mk, resKd_apply (hFK θ)]
    rw [hFF' θ x.1 (hQW (hKQ x.1 x.2))]
  have hLin : ∀ θ, LinOp (Φ θ) (F' θ) (b θ) = LinOp (Φ θ) (F θ) (b θ) := by
    intro θ
    unfold LinOp
    have hev : F' θ =ᶠ[nhds (b θ)] F θ := by
      filter_upwards [hWo.mem_nhds (hQW (hbQ θ))] with y hy using hFF' θ y hy
    rw [hev.fderiv_eq]
  have hHn : HnlP ν Φ F' (fun θ => (hF' θ).continuous) N = HnlPK ν Φ F N := by
    unfold HnlP HnlPK; simp only [hFop]
  have hHl : HlinP ν Φ F' b N = HlinP ν Φ F b N := by
    unfold HlinP; simp only [hLin]
  have hnormK : ∀ θ, ‖resKd K (F θ)‖ ≤ M := fun θ =>
    (ContinuousMap.norm_le _ hM0).mpr fun x => by
      rw [resKd_apply (hFK θ), Complex.norm_real]
      have := hFb θ 0 (Nat.zero_le _) x.1 (hKU x.2)
      rwa [norm_iteratedFDeriv_zero] at this
  have hA' : Integrable (fun θ => Fop (Φ θ) (F' θ) (hF' θ).continuous) ν := by
    simp only [hFop]
    exact integrable_apply_comp ν Φ hB (fun θ => resKd K (F θ)) hFm hnormK
  have hdFb : ∀ θ j, |fderiv ℝ (F θ) (b θ) (EuclideanSpace.single j 1)| ≤ M := by
    intro θ j
    have h1 : ‖fderiv ℝ (F θ) (b θ)‖ ≤ M := by
      have := hFb θ 1 (le_max_right _ _) (b θ) (hQU (hbQ θ))
      have e : ‖iteratedFDeriv ℝ 0 (fderiv ℝ (F θ)) (b θ)‖ = ‖iteratedFDeriv ℝ (0 + 1) (F θ) (b θ)‖ :=
        norm_iteratedFDeriv_fderiv
      rw [norm_iteratedFDeriv_zero] at e
      rw [e]; simpa using this
    calc |fderiv ℝ (F θ) (b θ) (EuclideanSpace.single j 1)| =
          ‖fderiv ℝ (F θ) (b θ) (EuclideanSpace.single j 1)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (F θ) (b θ)‖ * ‖(EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin d))‖ :=
          (fderiv ℝ (F θ) (b θ)).le_opNorm _
      _ ≤ M * 1 := by
          rw [EuclideanSpace.norm_single]
          simpa using h1
      _ = M := mul_one M
  have hL' : Integrable (fun θ => LinOp (Φ θ) (F' θ) (b θ)) ν := by
    simp only [hLin]
    exact integrable_sum_smul_coord ν Φ hB
      (fun j θ => fderiv ℝ (F θ) (b θ) (EuclideanSpace.single j 1)) hdF hdFb
  have hCb : ∀ θ, CF (schwartzOfReal (F' θ) (hF' θ) (hF'c θ)) ≤ C0 * (C1 * M) := fun θ =>
    (hCF _).trans (mul_le_mul_of_nonneg_left
      (hC1b (F θ) (hF θ) M hM0 (fun i hi x hx => hFb θ i (hi.trans (le_max_left _ _)) x hx)) hC0)
  have := functional_linearization_param ν Φ F' hF' hF'c b hcomm hA' hL' N hN ψ hψ hδ hψδ J hCJ hJ
    (Cb := C0 * (C1 * M)) (mul_nonneg hC0 (mul_nonneg hC1 hM0)) hCb t T ht
  rwa [hHn, hHl] at this

end Final

end QuantumNLS.FunctionalLinearization

#print axioms QuantumNLS.FunctionalLinearization.aestronglyMeasurable_apply_of_coord
#print axioms QuantumNLS.FunctionalLinearization.aestronglyMeasurable_apply_simple
#print axioms QuantumNLS.FunctionalLinearization.aestronglyMeasurable_apply_comp
#print axioms QuantumNLS.FunctionalLinearization.integrable_apply_comp
#print axioms QuantumNLS.FunctionalLinearization.integrable_sum_smul_coord
#print axioms QuantumNLS.FunctionalLinearization.contDiff_cutoffExt
#print axioms QuantumNLS.FunctionalLinearization.hasCompactSupport_cutoffExt
#print axioms QuantumNLS.FunctionalLinearization.sup_seminorm_cutoffExt_le
#print axioms QuantumNLS.FunctionalLinearization.resKd_apply
#print axioms QuantumNLS.FunctionalLinearization.HnlPK
#print axioms QuantumNLS.FunctionalLinearization.functional_linearization_param_meas
