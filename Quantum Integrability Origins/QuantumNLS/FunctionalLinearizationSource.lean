import Mathlib
import QuantumNLS.FunctionalLinearizationParamMeas

/-!
# PROP-014, source form: fixed `b`, fixed compact cube `Q`, `δ_N → 0`, no margin hypothesis

Source: `source/chapters/propagation/spectral_calculus.tex`, lines 497-598, `lem:A4-functional-linearization`
(`\ReportID{PROP-014}`).  This module imports the frozen `FunctionalLinearizationParamMeas`
(sha256 f04b812d...) read-only, and addresses Terra r97's two remaining objections.

1. **Margin hypothesis removed.**  The printed setting has joint spectra `K_N ⊆ Q` (the fixed
   compact cube) for every `N`, a fixed `b`, and `δ_N → 0`.  `mem_of_deviation_tendsto_sub` derives
   `b ∈ Q` from `K_n ⊆ Q` and `δ_n → 0` (`dist(b,K_n) ≤ √d δ_n` by `infDist_le_deviation`, `Q` closed;
   `K_n` is nonempty because `ψ_n` is a unit vector and `Φ` is unital).  Then the *core* theorem
   `functional_linearization_param_core` (the margin-free version of
   `functional_linearization_param_meas`, with `K ⊆ Q` and `b_θ ∈ Q` as the only inclusions) applies
   to every `n` separately with ONE common cutoff `χ` depending only on `(Q,U)`: `χ F` agrees with
   `F` on `K_n ∪ {b} ⊆ Q`, so the Hamiltonians coincide, and the estimate holds for EVERY `n`.
2. **Measurable-family convention stated.**  `H_N = N ∫ F_θ(B_θ) dν`, `H^lin_N = N ∫ ∑_j ∂_jF_θ(b_θ) B_{θ,j} dν`
   are Bochner integrals in the operator-norm Banach algebra `B(H)`; a Bochner integral exists
   only for strongly measurable integrands, so the source's "legitimate integral" can only mean
   the convention made explicit here as hypotheses: `hB` (`θ ↦ B_{n,θ,j}` strongly measurable into
   `B(H)`, for every `n`; by Stone–Weierstrass it gives strong measurability of all `θ ↦ Φ θ g`),
   `hFm` (`θ ↦ F_θ|_Q` strongly measurable into `C(Q,ℂ)`; its restrictions to each `K_n ⊆ Q` are
   then strongly measurable by continuity of pull-back, `resKd_eq_comp`), `hdF` (`θ ↦ ∂_jF_θ(b_θ)`
   measurable).  Integrability is *derived* from these and the uniform bounds, not assumed.

## Results (all proved)
* `mem_of_deviation_tendsto_sub`: `b ∈ Q`.
* `functional_linearization_param_core`: fixed `N`, `K ⊆ Q`, `b_θ ∈ Q`, no margin.
* `functional_linearization_param_source`: the parameter-integral clause in the printed sequence
  setting; `b_θ ∈ Q` derived for every `θ`; bound `⨆_{|t|≤T} ≤ ν(Θ)·C₀C₁M·T·C_J·δ_n` for every `n`.
* `functional_linearization_source`: the single-function source form (`H_n = N_n F(B_n)`, `HnlK`,
  `HlinK`), with the conclusion `b ∈ Q ∧ sup_{|t|≤T} ... ≤ C_F T C_J δ_n`, `C_F = C₀ C₁ M`.

## Uniformity of the constant, as printed
`C₀ = C₀(d)`, `C₁ = C₁(Q,U,d)`; the constant `C = ν(Θ)·C₀C₁M` (single function: `C_F = C₀C₁M`)
depends only on the fixed cube `Q`, the fixed neighbourhood `U` and the bound `M` for finitely many
(`≤ m(d)`) derivatives of `F_θ` on `U`.  It is independent of `n`, `K_n`, `b`, `ψ_n`, `J_n`, `T`,
`C_J`, `δ_n`, the dimension of `H`, and (for the integral clause) of the parameter family beyond `ν(Θ)`.

## Remaining stated limitations
* The three measurability hypotheses are assumptions on the parameter family (the module does not
  prove that jointly measurable `(θ,x) ↦ F_θ(x)` implies `hFm`).
* `C₁` is existential (not closed form).
* The single-function theorem and the parameter theorem are formulated with an `ℕ`-indexed sequence
  `n ↦ N_n` of positive reals (the source's "for each `N`").
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NormedSpace ComplexConjugate MeasureTheory Filter Topology
open scoped InnerProductSpace ContDiff FourierTransform

noncomputable section

namespace QuantumNLS.FunctionalLinearization

variable {d : ℕ}

section Bridge

/-- **`b` lies in the fixed compact cube `Q` once the deviations tend to zero** (varying joint
spectra `K_n ⊆ Q`).  `mem_of_deviation_tendsto` for a fixed `K` is the special case `K_n = K`. -/
theorem mem_of_deviation_tendsto_sub {Q : Set (EuclideanSpace ℝ (Fin d))} (hQ : IsClosed Q)
    {K : ℕ → Set (EuclideanSpace ℝ (Fin d))} [∀ n, CompactSpace (K n)] (hKQ : ∀ n, K n ⊆ Q)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Φs : ∀ n, C(K n, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : ℕ → H) (hψ : ∀ n, ‖ψ n‖ = 1) (δ : ℕ → ℝ)
    (hδ0 : ∀ n, 0 ≤ δ n) (hδ : Tendsto δ atTop (𝓝 0)) (b : EuclideanSpace ℝ (Fin d))
    (hdev : ∀ n j, ‖(Φs n (coordC j) - ((b j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) (ψ n)‖ ≤ δ n) :
    b ∈ Q := by
  have hne : ∀ n, (K n).Nonempty := by
    intro n
    by_contra hcon
    have hK : IsEmpty (K n) := by
      rw [Set.not_nonempty_iff_eq_empty] at hcon
      rw [hcon]; infer_instance
    have h10 : (1 : C(K n, ℂ)) = 0 := by ext x; exact (IsEmpty.false x).elim
    have h1 : (1 : H →L[ℂ] H) = 0 := by rw [← map_one (Φs n), h10, map_zero]
    have hψ0 : ψ n = 0 := by
      have := congrArg (fun T : H →L[ℂ] H => T (ψ n)) h1
      simpa using this
    have h2 := hψ n
    rw [hψ0] at h2
    simp at h2
  have h1 : ∀ n, Metric.infDist b Q ≤ Real.sqrt d * δ n := fun n =>
    (Metric.infDist_le_infDist_of_subset (hKQ n) (hne n)).trans
      (infDist_le_deviation (Φs n) (hne n) b (ψ n) (hψ n) (hδ0 n) (hdev n))
  have h2 : Tendsto (fun n => Real.sqrt d * δ n) atTop (𝓝 (Real.sqrt d * 0)) := hδ.const_mul _
  rw [mul_zero] at h2
  have h3 : Metric.infDist b Q ≤ 0 := ge_of_tendsto' h2 h1
  have hQne : Q.Nonempty := (hne 0).mono (hKQ 0)
  exact (hQ.mem_iff_infDist_zero hQne).mpr (le_antisymm h3 Metric.infDist_nonneg)

end Bridge


section Core

/-- **Fixed-`N` estimate with `K ⊆ Q` and `b_θ ∈ Q` as hypotheses (no margin).**  This is
`functional_linearization_param_meas` with the margin hypothesis `hQK` replaced by the two
inclusions that it was used to derive.  The same one cutoff `χ` (depending only on `(Q,U)`) is used. -/
theorem functional_linearization_param_core (d : ℕ) :
    ∃ (m : ℕ) (C0 : ℝ), 1 ≤ m ∧ 0 ≤ C0 ∧
      ∀ {U Q : Set (EuclideanSpace ℝ (Fin d))}, IsOpen U → IsCompact Q → Q ⊆ U →
      ∃ C1 : ℝ, 0 ≤ C1 ∧
      ∀ {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [IsFiniteMeasure ν]
        {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K]
        {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (Φ : Θ → C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
        (F : Θ → EuclideanSpace ℝ (Fin d) → ℝ) (hF : ∀ θ, ContDiffOn ℝ ∞ (F θ) U)
        (b : Θ → EuclideanSpace ℝ (Fin d))
        (hKQ : K ⊆ Q) (hbQ : ∀ θ, b θ ∈ Q)
        (hcomm : ∀ θ θ' j j', Commute (Φ θ (coordC j)) (Φ θ' (coordC j')))
        (hB : ∀ j, AEStronglyMeasurable (fun θ => Φ θ (coordC j)) ν)
        (hFm : AEStronglyMeasurable (fun θ => resKd K (F θ)) ν)
        (hdF : ∀ j, AEStronglyMeasurable
          (fun θ => fderiv ℝ (F θ) (b θ) (EuclideanSpace.single j 1)) ν)
        (N : ℝ) (hN : 0 < N) (ψ : H) (hψ : ‖ψ‖ = 1) {δ : ℝ} (hδ : 0 ≤ δ)
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
  refine ⟨C1, hC1, fun {Θ} _ ν _ {K} _ {H} _ _ _ Φ F hF b hKQ hbQ hcomm hB hFm hdF N hN ψ hψ {δ} hδ
    hψδ J {CJ} hCJ hJ {M} hM0 hFb t T ht => ?_⟩
  have hKU : K ⊆ U := fun x hx => hQU (hKQ hx)
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
    rw [hFF' θ x.1 (hQW (hKQ x.2))]
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

end Core


section Source

/-- Restriction of `f|_Q` to `K ⊆ Q` is the pull-back along the inclusion. -/
theorem resKd_eq_comp {K Q : Set (EuclideanSpace ℝ (Fin d))} (hKQ : K ⊆ Q)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContinuousOn f Q) :
    resKd K f = (resKd Q f).comp ⟨Set.inclusion hKQ, continuous_inclusion hKQ⟩ := by
  have hfK : ContinuousOn f K := hf.mono hKQ
  refine ContinuousMap.ext fun x => ?_
  have h2 := resKd_apply hf (Set.inclusion hKQ x)
  rw [resKd_apply hfK]
  exact h2.symm

/-- **PROP-014 `lem:A4-functional-linearization`, parameter-integral clause, in the printed
sequence setting.**

Setting: a finite measure space `(Θ, ν)`; for every `N`-index `n` and every parameter `θ`, a joint
functional calculus `Φ n θ` on `C(K n, ℂ)`, where the joint spectrum `K n` of the commuting
self-adjoint tuple `B_{n,θ,·} = Φ n θ (coordC ·)` lies in the *fixed* compact cube `Q`
(`hKQ`); the points `b_θ` and the functions `F_θ` do not depend on `n`; the unit vectors
`ψ_n` satisfy `‖(B_{n,θ,j} − b_{θ,j}) ψ_n‖ ≤ δ_n` with `δ_n → 0` (`hδ`).  **There is no margin
hypothesis**: `b_θ ∈ Q` is *derived* for every `θ` from `δ_n → 0` and `K n ⊆ Q`
(`mem_of_deviation_tendsto_sub`), and `K n ⊆ Q` is the hypothesis of the printed setting.  The
functions `F_θ` are `C^∞` on a fixed open `U ⊇ Q` with `‖D^iF_θ‖ ≤ M` on `U` (`i ≤ m`); one common
cutoff `χ` (`= 1` near `Q`, `tsupport χ ⊆ U`, depending only on `(Q,U)`) gives `χ F_θ`, which agrees
with `F_θ` on `K n ∪ {b_θ} ⊆ Q`, so the Hamiltonians coincide.

Measurable-family convention (Bochner integrals in the operator-norm Banach algebra `B(H)` exist only
for strongly measurable integrands; the source's "legitimate integral" is this convention, stated
explicitly): `hB` the maps `θ ↦ B_{n,θ,j}` are strongly measurable `Θ → B(H)`; `hFm` `θ ↦ F_θ|_Q`
is strongly measurable `Θ → C(Q,ℂ)` (its restrictions to each `K n` are then strongly measurable by
continuity of the restriction); `hdF` `θ ↦ ∂_jF_θ(b_θ)` is measurable.  Integrability of the two
operator-valued integrands is *derived* (`functional_linearization_param_core`), not assumed.

Conclusion, for **every** `n` (no `n`-dependence of the constant), the printed estimate
`sup_{|t|≤T} |⟨e^{-itH_n}ψ_n, J_n e^{-itH_n}ψ_n⟩ − ⟨e^{-itH_n^lin}ψ_n, J_n e^{-itH_n^lin}ψ_n⟩| ≤ C T C_J δ_n`
with `C = ν(Θ)·C₀·C₁·M`: `C₀` depends only on `d`, `C₁` only on `(Q,U,d)`, and `M` is the derivative
bound; `C` is independent of `n`, `K n`, `b`, `ψ_n`, `J_n`, `T`, `C_J`, `δ_n`.  Here
`H_n = N_n ∫ F_θ(B_{n,θ}) dν` and `H_n^lin = N_n ∫ ∑_j ∂_jF_θ(b_θ) B_{n,θ,j} dν`
(`HnlPK`, `HlinP`). -/
theorem functional_linearization_param_source (d : ℕ) :
    ∃ (m : ℕ) (C0 : ℝ), 1 ≤ m ∧ 0 ≤ C0 ∧
      ∀ {U Q : Set (EuclideanSpace ℝ (Fin d))}, IsOpen U → IsCompact Q → Q ⊆ U →
      ∃ C1 : ℝ, 0 ≤ C1 ∧
      ∀ {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [IsFiniteMeasure ν]
        {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (K : ℕ → Set (EuclideanSpace ℝ (Fin d))) [∀ n, CompactSpace (K n)]
        (hKQ : ∀ n, K n ⊆ Q)
        (Φ : ∀ n, Θ → C(K n, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
        (F : Θ → EuclideanSpace ℝ (Fin d) → ℝ) (hF : ∀ θ, ContDiffOn ℝ ∞ (F θ) U)
        (b : Θ → EuclideanSpace ℝ (Fin d))
        (hcomm : ∀ n θ θ' j j', Commute (Φ n θ (coordC j)) (Φ n θ' (coordC j')))
        (hB : ∀ n j, AEStronglyMeasurable (fun θ => Φ n θ (coordC j)) ν)
        (hFm : AEStronglyMeasurable (fun θ => resKd Q (F θ)) ν)
        (hdF : ∀ j, AEStronglyMeasurable
          (fun θ => fderiv ℝ (F θ) (b θ) (EuclideanSpace.single j 1)) ν)
        (N : ℕ → ℝ) (hN : ∀ n, 0 < N n) (ψ : ℕ → H) (hψ : ∀ n, ‖ψ n‖ = 1)
        (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n) (hδ : Tendsto δ atTop (𝓝 0))
        (hψδ : ∀ n θ j, ‖(Φ n θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) (ψ n)‖ ≤ δ n)
        (J : ℕ → H →L[ℂ] H) {CJ : ℝ} (hCJ : 0 ≤ CJ)
        (hJ : ∀ n θ j, ‖Φ n θ (coordC j) * J n - J n * Φ n θ (coordC j)‖ ≤ CJ / N n)
        {M : ℝ} (hM0 : 0 ≤ M)
        (hFb : ∀ θ, ∀ i ≤ m, ∀ x ∈ U, ‖iteratedFDeriv ℝ i (F θ) x‖ ≤ M)
        {T : ℝ} (hT : 0 ≤ T) (n : ℕ),
        (⨆ t : Set.Icc (-T) T,
          ‖⟪evol (HnlPK ν (Φ n) F (N n)) t (ψ n),
              J n (evol (HnlPK ν (Φ n) F (N n)) t (ψ n))⟫_ℂ -
            ⟪evol (HlinP ν (Φ n) F b (N n)) t (ψ n),
              J n (evol (HlinP ν (Φ n) F b (N n)) t (ψ n))⟫_ℂ‖) ≤
          (ν Set.univ).toReal * (C0 * (C1 * M)) * T * CJ * δ n := by
  obtain ⟨m, C0, hm, hC0, hcore⟩ := functional_linearization_param_core d
  refine ⟨m, C0, hm, hC0, fun {U Q} hU hQ hQU => ?_⟩
  obtain ⟨C1, hC1, hC1b⟩ := hcore hU hQ hQU
  refine ⟨C1, hC1, fun {Θ} _ ν _ {H} _ _ _ K _ hKQ Φ F hF b hcomm hB hFm hdF N hN ψ hψ δ hδ0 hδ hψδ J
    {CJ} hCJ hJ {M} hM0 hFb {T} hT n => ?_⟩
  have hbQ : ∀ θ, b θ ∈ Q := fun θ =>
    mem_of_deviation_tendsto_sub hQ.isClosed hKQ (fun n => Φ n θ) ψ hψ δ hδ0 hδ (b θ)
      (fun n j => hψδ n θ j)
  have hFQ : ∀ θ, ContinuousOn (F θ) Q := fun θ => (hF θ).continuousOn.mono hQU
  have hFmn : AEStronglyMeasurable (fun θ => resKd (K n) (F θ)) ν := by
    have : (fun θ => resKd (K n) (F θ)) =
        fun θ => (resKd Q (F θ)).comp ⟨Set.inclusion (hKQ n), continuous_inclusion (hKQ n)⟩ :=
      funext fun θ => resKd_eq_comp (hKQ n) (hFQ θ)
    rw [this]
    exact (ContinuousMap.continuous_precomp
      (⟨Set.inclusion (hKQ n), continuous_inclusion (hKQ n)⟩ : C(K n, Q))).comp_aestronglyMeasurable hFm
  refine Real.iSup_le (fun t => ?_) ?_
  · refine hC1b ν (Φ n) F hF b (hKQ n) hbQ (hcomm n) (hB n) hFmn hdF (N n) (hN n) (ψ n) (hψ n)
      (hδ0 n) (hψδ n) (J n) hCJ (hJ n) hM0 hFb t.1 T ?_
    rw [abs_le]; exact ⟨by linarith [t.2.1], t.2.2⟩
  · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ENNReal.toReal_nonneg
      (mul_nonneg hC0 (mul_nonneg hC1 hM0))) hT) hCJ) (hδ0 n)

end Source


section Single

variable {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `H_N = N F(B_N)` for `F` smooth only near `K`: `F(B_N) = Φ(F|_K)`. -/
def HnlK (Φ : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (F : EuclideanSpace ℝ (Fin d) → ℝ) (N : ℝ) :
    H →L[ℂ] H := (N : ℂ) • Φ (resKd K F)

/-- `H_N^lin = N ∑_j ∂_jF(b) B_{N,j}`. -/
def HlinK (Φ : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (F : EuclideanSpace ℝ (Fin d) → ℝ)
    (b : EuclideanSpace ℝ (Fin d)) (N : ℝ) : H →L[ℂ] H := (N : ℂ) • LinOp Φ F b

theorem HnlPK_dirac (Φ : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (F : EuclideanSpace ℝ (Fin d) → ℝ) (N : ℝ) :
    HnlPK (Measure.dirac ()) (fun _ : Unit => Φ) (fun _ : Unit => F) N = HnlK Φ F N := by
  unfold HnlPK HnlK
  rw [integral_const]
  simp

theorem HlinP_dirac (Φ : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (F : EuclideanSpace ℝ (Fin d) → ℝ)
    (b : EuclideanSpace ℝ (Fin d)) (N : ℝ) :
    HlinP (Measure.dirac ()) (fun _ : Unit => Φ) (fun _ : Unit => F) (fun _ : Unit => b) N =
      HlinK Φ F b N := by
  unfold HlinP HlinK
  rw [integral_const]
  simp

/-- **PROP-014 `lem:A4-functional-linearization`, single function, printed sequence setting.**

For every `n`: commuting bounded self-adjoint `B_{n,j} = Φ n (coordC j)` with joint spectrum
`K n ⊆ Q` (a fixed compact cube, `hKQ`), fixed `b`, unit `ψ_n` with
`‖(B_{n,j} − b_j)ψ_n‖ ≤ δ_n`, `δ_n → 0`, `‖[B_{n,j}, J_n]‖ ≤ C_J/N_n`, and `F` `C^∞` on an open
`U ⊇ Q` with `‖D^iF‖ ≤ M` on `U` (`i ≤ m`): then `b ∈ Q` (derived, not assumed), and for every
`n` and `T ≥ 0`
`sup_{|t|≤T} |⟨e^{-itH_n}ψ_n, J_n e^{-itH_n}ψ_n⟩ − ⟨e^{-itH_n^lin}ψ_n, J_n e^{-itH_n^lin}ψ_n⟩|
  ≤ C_F T C_J δ_n`, `C_F = C₀ C₁ M`, `H_n = N_n F(B_n)`, `H_n^lin = N_n ∑_j ∂_jF(b) B_{n,j}`.
No margin hypothesis.  Uniformity as printed: `C₀ = C₀(d)`, `C₁ = C₁(Q,U,d)`; `C_F` depends on
nothing else than the bound `M` of finitely many derivatives of `F` on the fixed neighbourhood
`U` of the cube; it is independent of `n`, `K n`, `b`, `ψ_n`, `J_n`, `T`, `C_J`, `δ_n`.  One common
cutoff `χ` (depending only on `(Q,U)`) is used inside the proof; `χ F = F` on `K n ∪ {b} ⊆ Q`. -/
theorem functional_linearization_source (d : ℕ) :
    ∃ (m : ℕ) (C0 : ℝ), 1 ≤ m ∧ 0 ≤ C0 ∧
      ∀ {U Q : Set (EuclideanSpace ℝ (Fin d))}, IsOpen U → IsCompact Q → Q ⊆ U →
      ∃ C1 : ℝ, 0 ≤ C1 ∧
      ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (K : ℕ → Set (EuclideanSpace ℝ (Fin d))) [∀ n, CompactSpace (K n)]
        (hKQ : ∀ n, K n ⊆ Q)
        (Φ : ∀ n, C(K n, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
        (F : EuclideanSpace ℝ (Fin d) → ℝ) (hF : ContDiffOn ℝ ∞ F U)
        (b : EuclideanSpace ℝ (Fin d))
        (N : ℕ → ℝ) (hN : ∀ n, 0 < N n) (ψ : ℕ → H) (hψ : ∀ n, ‖ψ n‖ = 1)
        (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n) (hδ : Tendsto δ atTop (𝓝 0))
        (hψδ : ∀ n j, ‖(Φ n (coordC j) - ((b j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) (ψ n)‖ ≤ δ n)
        (J : ℕ → H →L[ℂ] H) {CJ : ℝ} (hCJ : 0 ≤ CJ)
        (hJ : ∀ n j, ‖Φ n (coordC j) * J n - J n * Φ n (coordC j)‖ ≤ CJ / N n)
        {M : ℝ} (hM0 : 0 ≤ M)
        (hFb : ∀ i ≤ m, ∀ x ∈ U, ‖iteratedFDeriv ℝ i F x‖ ≤ M)
        {T : ℝ} (hT : 0 ≤ T) (n : ℕ),
        b ∈ Q ∧
        (⨆ t : Set.Icc (-T) T,
          ‖⟪evol (HnlK (Φ n) F (N n)) t (ψ n), J n (evol (HnlK (Φ n) F (N n)) t (ψ n))⟫_ℂ -
            ⟪evol (HlinK (Φ n) F b (N n)) t (ψ n),
              J n (evol (HlinK (Φ n) F b (N n)) t (ψ n))⟫_ℂ‖) ≤
          C0 * (C1 * M) * T * CJ * δ n := by
  obtain ⟨m, C0, hm, hC0, hsrc⟩ := functional_linearization_param_source d
  refine ⟨m, C0, hm, hC0, fun {U Q} hU hQ hQU => ?_⟩
  obtain ⟨C1, hC1, hC1b⟩ := hsrc hU hQ hQU
  refine ⟨C1, hC1, fun {H} _ _ _ K _ hKQ Φ F hF b N hN ψ hψ δ hδ0 hδ hψδ J {CJ} hCJ hJ {M} hM0 hFb
    {T} hT n => ?_⟩
  refine ⟨mem_of_deviation_tendsto_sub hQ.isClosed hKQ Φ ψ hψ δ hδ0 hδ b hψδ, ?_⟩
  have := hC1b (Measure.dirac ()) K hKQ (fun n (_ : Unit) => Φ n) (fun _ : Unit => F) (fun _ => hF)
    (fun _ : Unit => b)
    (fun n _ _ j j' => (Commute.all (coordC j) (coordC j')).map (Φ n))
    (fun n j => aestronglyMeasurable_const) aestronglyMeasurable_const
    (fun j => aestronglyMeasurable_const) N hN ψ hψ δ hδ0 hδ (fun n _ j => hψδ n j) J hCJ
    (fun n _ j => hJ n j) hM0 (fun _ => hFb) hT n
  simpa only [HnlPK_dirac, HlinP_dirac, measure_univ, ENNReal.toReal_one, one_mul] using this

end Single

end QuantumNLS.FunctionalLinearization

#print axioms QuantumNLS.FunctionalLinearization.mem_of_deviation_tendsto_sub
#print axioms QuantumNLS.FunctionalLinearization.functional_linearization_param_core
#print axioms QuantumNLS.FunctionalLinearization.resKd_eq_comp
#print axioms QuantumNLS.FunctionalLinearization.functional_linearization_param_source
#print axioms QuantumNLS.FunctionalLinearization.HnlPK_dirac
#print axioms QuantumNLS.FunctionalLinearization.HlinP_dirac
#print axioms QuantumNLS.FunctionalLinearization.functional_linearization_source
