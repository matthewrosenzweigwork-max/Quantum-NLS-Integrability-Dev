import Mathlib
import QuantumNLS.FunctionalLinearizationSource

/-!
# PROP-014, source form with a Hilbert space varying with `N`

Source: `source/chapters/propagation/spectral_calculus.tex`, lines 497-598, `lem:A4-functional-linearization`
(`\ReportID{PROP-014}`).  Imports the frozen `FunctionalLinearizationSource` (sha256 db48afcd...)
read-only and addresses Terra r98.

## (i) Varying Hilbert spaces
The printed physical sequence has `H_N = Sym^N`-type spaces depending on `N`.  The theorems here take a
dependent family `H : ℕ → Type` with per-`n` instances (`NormedAddCommGroup`, `InnerProductSpace ℂ`,
`CompleteSpace`), operators `B_{n,θ,j}` on `H n`, unit vectors `ψ_n ∈ H n`, observables `J_n` on `H n`:
* `mem_of_deviation_tendsto_varying`: `b ∈ Q` from `K_n ⊆ Q` (joint spectra of the tuples on `H n`) and `δ_n → 0`;
* `functional_linearization_param_varying`: the parameter-integral clause;
* `functional_linearization_varying`: the single-function clause.
Both are derived from the margin-free core `functional_linearization_param_core`, which is quantified over
every Hilbert space instance separately and applied at `H n` for each `n`; the constants `m, C₀` (depending only
on `d`) and `C₁` (depending only on `(Q,U,d)`) are therefore independent of `n` and of `H n`.

## (ii) The measurable-family interpretation (stated, not silent)
`H_n = N_n ∫ F_θ(B_{n,θ}) dν(θ)` and `H_n^lin = N_n ∫ ∑_j ∂_jF_θ(b_θ) B_{n,θ,j} dν(θ)` are integrals of
`B(H n)`-valued functions of `θ`.  **Adopted interpretation:** they are Bochner integrals in the operator-norm
Banach algebra `B(H n)`.  A Bochner integral exists exactly for (a.e.) strongly measurable integrands, i.e.
measurable with a.e. separable range *in the operator-norm topology*.  The hypotheses are therefore:
* `hB : ∀ n j, AEStronglyMeasurable (θ ↦ Φ n θ (coordC j)) ν` (norm-strong measurability of the coordinates;
  by Stone–Weierstrass and `‖Φ θ g‖ ≤ ‖g‖` this gives it for every `θ ↦ Φ θ g`, `aestronglyMeasurable_apply_of_coord`);
* `hFm : AEStronglyMeasurable (θ ↦ F_θ|_Q) ν` in `C(Q,ℂ)` (restrictions to each `K_n ⊆ Q` follow);
* `hdF : ∀ j, AEStronglyMeasurable (θ ↦ ∂_jF_θ(b_θ)) ν`.
These are *sufficient conventions*, not the only conceivable reading.  **Readings NOT covered by this module:**
1. *Strong-operator-topology (SOT) measurability* (`θ ↦ B_θ ψ` measurable in `H` for each `ψ`) with the integral
   `∫ F_θ(B_θ) ψ dν` defined as a Bochner or Pettis integral in `H` (or weakly via `⟨φ, ·ψ⟩`).  SOT-measurability
   does not imply norm-strong measurability (e.g. `θ ↦ M_{1_{[0,θ]}}` on `L²[0,1]` is SOT-continuous but has
   non-separable range in operator norm); such families have no operator-norm Bochner integral.  Proving
   the estimate for a vector-valued (Pettis) integral would need a separate definition of `H_n` and the commutator
   argument of `functional_linearization_param` redone with weak integrals; not formalised.
2. *Weak-operator-topology* measurability with the weak integral: same remark.
3. *Almost-everywhere versions* are covered (`AEStronglyMeasurable`); *Lebesgue-measure completions* of `ν` too.
4. Joint measurability `(θ,x) ↦ F_θ(x)` (Carathéodory) is not shown to imply `hFm`.
A common case in which `hB` holds automatically is proved: if `θ ↦ B_{θ,j}` is norm-continuous on a compact
parameter space, `aestronglyMeasurable_coord_of_continuous` / `hB_of_continuous` (continuous image of a compact
set is separable, continuous maps are measurable).

## Results (all proved)
`mem_of_deviation_tendsto_varying`, `functional_linearization_param_varying`, `functional_linearization_varying`,
`aestronglyMeasurable_coord_of_continuous`, `hB_of_continuous`.  Uniformity of the constant as printed:
`C = ν(Θ)·C₀C₁M` (single function `C_F = C₀C₁M`) depends only on `d`, the fixed cube `Q`, the fixed neighbourhood `U`,
and the bound `M` for finitely many derivatives.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NormedSpace ComplexConjugate MeasureTheory Filter Topology
open scoped InnerProductSpace ContDiff FourierTransform

noncomputable section

namespace QuantumNLS.FunctionalLinearization

variable {d : ℕ}

section Varying

/-- **`b ∈ Q` with a varying Hilbert space `H n`** (the physical `H_N = Sym^N` varies with `N`).
`K_n ⊆ Q` for the joint spectrum of the commuting tuple on `H n`, `δ_n → 0`, `Q` closed. -/
theorem mem_of_deviation_tendsto_varying {Q : Set (EuclideanSpace ℝ (Fin d))} (hQ : IsClosed Q)
    {K : ℕ → Set (EuclideanSpace ℝ (Fin d))} [∀ n, CompactSpace (K n)] (hKQ : ∀ n, K n ⊆ Q)
    {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]
    [∀ n, CompleteSpace (H n)]
    (Φs : ∀ n, C(K n, ℂ) →⋆ₐ[ℂ] (H n →L[ℂ] H n)) (ψ : ∀ n, H n) (hψ : ∀ n, ‖ψ n‖ = 1)
    (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n) (hδ : Tendsto δ atTop (𝓝 0))
    (b : EuclideanSpace ℝ (Fin d))
    (hdev : ∀ n j, ‖(Φs n (coordC j) - ((b j : ℝ) : ℂ) • (1 : H n →L[ℂ] H n)) (ψ n)‖ ≤ δ n) :
    b ∈ Q := by
  have hne : ∀ n, (K n).Nonempty := by
    intro n
    by_contra hcon
    have hK : IsEmpty (K n) := by
      rw [Set.not_nonempty_iff_eq_empty] at hcon
      rw [hcon]; infer_instance
    have h10 : (1 : C(K n, ℂ)) = 0 := by ext x; exact (IsEmpty.false x).elim
    have h1 : (1 : H n →L[ℂ] H n) = 0 := by rw [← map_one (Φs n), h10, map_zero]
    have hψ0 : ψ n = 0 := by
      have := congrArg (fun T : H n →L[ℂ] H n => T (ψ n)) h1
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

end Varying


section ParamVarying

/-- **PROP-014, parameter-integral clause, source form, Hilbert space varying with `n`.**
Same as `functional_linearization_param_source`, with `H : ℕ → Type` a dependent family
(`H n = Sym^{N_n}`-type spaces), operators `B_{n,θ,j}` on `H n`, unit vectors `ψ_n ∈ H n`, observables
`J_n` on `H n`.  The constants `m, C₀, C₁` do not depend on `n`, `H n`, `K n`, ... because the margin-free
core `functional_linearization_param_core` is quantified over every Hilbert space instance separately and
is applied at `H n` for each `n`.  Measurable-family hypotheses `hB`, `hFm`, `hdF`: see the module
docstring (interpretation adopted: operator-norm strong measurability). -/
theorem functional_linearization_param_varying (d : ℕ) :
    ∃ (m : ℕ) (C0 : ℝ), 1 ≤ m ∧ 0 ≤ C0 ∧
      ∀ {U Q : Set (EuclideanSpace ℝ (Fin d))}, IsOpen U → IsCompact Q → Q ⊆ U →
      ∃ C1 : ℝ, 0 ≤ C1 ∧
      ∀ {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [IsFiniteMeasure ν]
        {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]
        [∀ n, CompleteSpace (H n)]
        (K : ℕ → Set (EuclideanSpace ℝ (Fin d))) [∀ n, CompactSpace (K n)]
        (hKQ : ∀ n, K n ⊆ Q)
        (Φ : ∀ n, Θ → C(K n, ℂ) →⋆ₐ[ℂ] (H n →L[ℂ] H n))
        (F : Θ → EuclideanSpace ℝ (Fin d) → ℝ) (hF : ∀ θ, ContDiffOn ℝ ∞ (F θ) U)
        (b : Θ → EuclideanSpace ℝ (Fin d))
        (hcomm : ∀ n θ θ' j j', Commute (Φ n θ (coordC j)) (Φ n θ' (coordC j')))
        (hB : ∀ n j, AEStronglyMeasurable (fun θ => Φ n θ (coordC j)) ν)
        (hFm : AEStronglyMeasurable (fun θ => resKd Q (F θ)) ν)
        (hdF : ∀ j, AEStronglyMeasurable
          (fun θ => fderiv ℝ (F θ) (b θ) (EuclideanSpace.single j 1)) ν)
        (N : ℕ → ℝ) (hN : ∀ n, 0 < N n) (ψ : ∀ n, H n) (hψ : ∀ n, ‖ψ n‖ = 1)
        (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n) (hδ : Tendsto δ atTop (𝓝 0))
        (hψδ : ∀ n θ j,
          ‖(Φ n θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H n →L[ℂ] H n)) (ψ n)‖ ≤ δ n)
        (J : ∀ n, H n →L[ℂ] H n) {CJ : ℝ} (hCJ : 0 ≤ CJ)
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
    mem_of_deviation_tendsto_varying hQ.isClosed hKQ (fun n => Φ n θ) ψ hψ δ hδ0 hδ (b θ)
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

end ParamVarying

section SingleVarying

/-- **PROP-014 `lem:A4-functional-linearization`, single function, source form, Hilbert space varying
with `n`** (`H n` a dependent family, `B_{n,j}` on `H n`, `ψ_n ∈ H n`, `J_n` on `H n`).
`b ∈ Q` is derived across the varying spaces (`mem_of_deviation_tendsto_varying`); then for every
`n` and `T ≥ 0`: `sup_{|t|≤T} |⟨e^{-itH_n}ψ_n, J_n e^{-itH_n}ψ_n⟩ − ⟨e^{-itH^lin_n}ψ_n, J_n e^{-itH^lin_n}ψ_n⟩|
≤ C_F T C_J δ_n`, `C_F = C₀C₁M`, independent of `n`, `H n`, `K n`, `b`, `ψ_n`, `J_n`, `T`, `C_J`, `δ_n`. -/
theorem functional_linearization_varying (d : ℕ) :
    ∃ (m : ℕ) (C0 : ℝ), 1 ≤ m ∧ 0 ≤ C0 ∧
      ∀ {U Q : Set (EuclideanSpace ℝ (Fin d))}, IsOpen U → IsCompact Q → Q ⊆ U →
      ∃ C1 : ℝ, 0 ≤ C1 ∧
      ∀ {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]
        [∀ n, CompleteSpace (H n)]
        (K : ℕ → Set (EuclideanSpace ℝ (Fin d))) [∀ n, CompactSpace (K n)]
        (hKQ : ∀ n, K n ⊆ Q)
        (Φ : ∀ n, C(K n, ℂ) →⋆ₐ[ℂ] (H n →L[ℂ] H n))
        (F : EuclideanSpace ℝ (Fin d) → ℝ) (hF : ContDiffOn ℝ ∞ F U)
        (b : EuclideanSpace ℝ (Fin d))
        (N : ℕ → ℝ) (hN : ∀ n, 0 < N n) (ψ : ∀ n, H n) (hψ : ∀ n, ‖ψ n‖ = 1)
        (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n) (hδ : Tendsto δ atTop (𝓝 0))
        (hψδ : ∀ n j, ‖(Φ n (coordC j) - ((b j : ℝ) : ℂ) • (1 : H n →L[ℂ] H n)) (ψ n)‖ ≤ δ n)
        (J : ∀ n, H n →L[ℂ] H n) {CJ : ℝ} (hCJ : 0 ≤ CJ)
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
  obtain ⟨m, C0, hm, hC0, hsrc⟩ := functional_linearization_param_varying d
  refine ⟨m, C0, hm, hC0, fun {U Q} hU hQ hQU => ?_⟩
  obtain ⟨C1, hC1, hC1b⟩ := hsrc hU hQ hQU
  refine ⟨C1, hC1, fun {H} _ _ _ K _ hKQ Φ F hF b N hN ψ hψ δ hδ0 hδ hψδ J {CJ} hCJ hJ {M} hM0 hFb
    {T} hT n => ?_⟩
  refine ⟨mem_of_deviation_tendsto_varying hQ.isClosed hKQ Φ ψ hψ δ hδ0 hδ b hψδ, ?_⟩
  have := hC1b (Measure.dirac ()) K hKQ (fun n (_ : Unit) => Φ n) (fun _ : Unit => F) (fun _ => hF)
    (fun _ : Unit => b)
    (fun n _ _ j j' => (Commute.all (coordC j) (coordC j')).map (Φ n))
    (fun n j => aestronglyMeasurable_const) aestronglyMeasurable_const
    (fun j => aestronglyMeasurable_const) N hN ψ hψ δ hδ0 hδ (fun n _ j => hψδ n j) J hCJ
    (fun n _ j => hJ n j) hM0 (fun _ => hFb) hT n
  simpa only [HnlPK_dirac, HlinP_dirac, measure_univ, ENNReal.toReal_one, one_mul] using this

end SingleVarying

section Measurability

variable {Θ : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
variable {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **`hB` holds automatically under norm continuity on a compact parameter space.**  If
`θ ↦ B_{θ,j} = Φ θ (x_j)` is continuous into `B(H)` (operator norm) and `Θ` is compact (or just has
separable range of `θ ↦ B_{θ,j}`), then it is strongly measurable for every finite measure. -/
theorem aestronglyMeasurable_coord_of_continuous [CompactSpace Θ] (ν : Measure Θ)
    (Φ : Θ → C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (j : Fin d)
    (hcont : Continuous fun θ => Φ θ (coordC j)) :
    AEStronglyMeasurable (fun θ => Φ θ (coordC j)) ν := by
  borelize (H →L[ℂ] H)
  exact (stronglyMeasurable_iff_measurable_separable.2
    ⟨hcont.measurable, (isCompact_range hcont).isSeparable⟩).aestronglyMeasurable

/-- Norm continuity of the coordinates implies `hB` for every coordinate. -/
theorem hB_of_continuous [CompactSpace Θ] (ν : Measure Θ)
    (Φ : Θ → C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hcont : ∀ j, Continuous fun θ => Φ θ (coordC j)) :
    ∀ j, AEStronglyMeasurable (fun θ => Φ θ (coordC j)) ν :=
  fun j => aestronglyMeasurable_coord_of_continuous ν Φ j (hcont j)

end Measurability

end QuantumNLS.FunctionalLinearization

#print axioms QuantumNLS.FunctionalLinearization.mem_of_deviation_tendsto_varying
#print axioms QuantumNLS.FunctionalLinearization.functional_linearization_param_varying
#print axioms QuantumNLS.FunctionalLinearization.functional_linearization_varying
#print axioms QuantumNLS.FunctionalLinearization.aestronglyMeasurable_coord_of_continuous
#print axioms QuantumNLS.FunctionalLinearization.hB_of_continuous
