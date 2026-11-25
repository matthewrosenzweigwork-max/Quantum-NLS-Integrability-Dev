import Mathlib
import QuantumNLS.BornTranslation
import QuantumNLS.FullMassLimit

/-!
# R-043AB9AA `prop:root-full-mass`, last clause: translation invariance of `μ_{λ,v}` and `M_{κ,u}`

Source: `ROOT_measure_extensions.tex`, `prop:root-full-mass`: "These measures are common-phase and translation invariant" ("Common phase and translation leave every finite-particle
probability unchanged, hence leave the limits unchanged"); `ROOT_spectral_measure.tex`, discussion after `prop:root-free`.

* `isLimiting_trans`: if `ν_N → μ` weakly in probability under the Born law of `v^{⊗N}` then the same holds for the translate `τ_a v` (the Born laws coincide for all `N ≥ 1`,
  `BornTranslation.bornLaw_translate`);
* `coeff_norm_trans`: `|(τ_a u)^(n)| = |û(n)|` (obtained from the `N = 1` Born law, `OneParticleBorn.born_one`, so no separate Fourier computation);
* `muKappa_trans`: `μ_{λ,τ_a v} = μ_{λ,v}` (uniqueness of the limiting measure; at `λ ≤ 0` the free measure depends only on `|û(n)|`);
* `Mmeas_translate`, `Mfin_translate`: `M_{κ,τ_a u} = M_{κ,u}` for all real `κ`.
Together with `FullMass.Mmeas_phase` and `Mmeas_phase_zero` this proves the common-phase and translation invariance of `M_{κ,u}`.  No EXT-025 contract is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

noncomputable section

open Classical

namespace QuantumNLS.TranslationInvariance

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.BornTranslation (bornLaw_translate)
open QuantumNLS.FreeLimit (freeMeasure freeProb muKappa muKappa_spec)
open QuantumNLS.FullMass (Mmeas Mfin unitDir norm_unitDir Mmeas_of_ne Mmeas_zero)
open QuantumNLS.FullMassLimit (muKappa_congr)
open QuantumNLS.BulkResponseActual (IsLimitingRapidityMeasure physBasis empiricalProb)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BornConvergence (TendstoInProbabilityWeak tendstoInProbabilityWeak_iff)

variable {L : ℝ} [Fact (0 < L)]

theorem norm_trans (a : ℝ) (u : L2T L) : ‖QuantumNLS.BornTranslation.trans a u‖ = ‖u‖ := (QuantumNLS.BornTranslation.trans a).norm_map u

theorem bornMeasure_trans {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 1 ≤ N) (u : L2T L) (hu : ‖u‖ = 1) (a : ℝ) :
    bornMeasure (physBasis L hκ N) (QuantumNLS.BornTranslation.trans a u) (by rw [norm_trans, hu]) =
      bornMeasure (physBasis L hκ N) u hu := by
  rw [QuantumNLS.RootMeasureExistence.physBasis_eq hκ hN]
  unfold bornMeasure
  congr 1
  apply PMF.ext
  intro m
  rw [QuantumNLS.BetheCoefficientTransform.bornPMF_apply, QuantumNLS.BetheCoefficientTransform.bornPMF_apply,
    bornLaw_translate hκ hN u a m]

theorem isLimiting_trans {κ : ℝ} (hκ : 0 < κ) {u : L2T L} (hu : ‖u‖ = 1) (a : ℝ) {μ : ProbabilityMeasure ℝ}
    (h : IsLimitingRapidityMeasure L κ hκ u hu μ) :
    IsLimitingRapidityMeasure L κ hκ (QuantumNLS.BornTranslation.trans a u) (by rw [norm_trans, hu]) μ := by
  unfold IsLimitingRapidityMeasure at h ⊢
  rw [tendstoInProbabilityWeak_iff] at h ⊢
  intro ε hε
  refine (h ε hε).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [bornMeasure_trans hκ hN u hu a]

theorem coeff_norm_trans (u : L2T L) (a : ℝ) (n : ℤ) :
    ‖QuantumNLS.Fourier.coeff L ((QuantumNLS.BornTranslation.trans a u : L2T L) : AddCircle L → ℂ) n‖ =
      ‖QuantumNLS.Fourier.coeff L (u : AddCircle L → ℂ) n‖ := by
  have h := bornLaw_translate (L := L) (κ := 1) one_pos (N := 1) le_rfl u a (QuantumNLS.OneParticleBorn.idxEquiv.symm n)
  rw [QuantumNLS.OneParticleBorn.born_one one_pos, QuantumNLS.OneParticleBorn.born_one one_pos,
    ← QuantumNLS.OneParticleBorn.idxEquiv_apply, Equiv.apply_symm_apply] at h
  have h2 : ‖QuantumNLS.Fourier.coeff L ((QuantumNLS.BornTranslation.trans a u : L2T L) : AddCircle L → ℂ) n‖ ^ 2 =
      ‖QuantumNLS.Fourier.coeff L (u : AddCircle L → ℂ) n‖ ^ 2 := h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

theorem freeMeasure_trans (u : L2T L) (a : ℝ) : freeMeasure L (QuantumNLS.BornTranslation.trans a u) = freeMeasure L u := by
  unfold freeMeasure
  congr 1
  funext n
  rw [coeff_norm_trans]

theorem freeProb_trans (a : ℝ) (u : L2T L) (hu : ‖u‖ = 1) (hu' : ‖QuantumNLS.BornTranslation.trans a u‖ = 1) :
    freeProb (QuantumNLS.BornTranslation.trans a u) hu' = freeProb u hu :=
  Subtype.ext (freeMeasure_trans u a)

/-- **`μ_{λ,τ_a v} = μ_{λ,v}`** for every real `λ`. -/
theorem muKappa_trans (a : ℝ) (v : L2T L) (hv : ‖v‖ = 1) (hv' : ‖QuantumNLS.BornTranslation.trans a v‖ = 1) (lam : ℝ) :
    muKappa (QuantumNLS.BornTranslation.trans a v) hv' lam = muKappa v hv lam := by
  by_cases h : 0 < lam
  · have h1 := muKappa_spec (QuantumNLS.BornTranslation.trans a v) hv' h
    have h2 := isLimiting_trans h hv a (muKappa_spec v hv h)
    exact IsLimitingRapidityMeasure.unique h1 h2
  · unfold muKappa
    rw [dif_neg h, dif_neg h]
    exact freeProb_trans a v hv hv'

theorem unitDir_trans (a : ℝ) (u : L2T L) : unitDir (QuantumNLS.BornTranslation.trans a u) = QuantumNLS.BornTranslation.trans a (unitDir u) := by
  unfold unitDir
  rw [norm_trans, map_smul]

/-- **Translation invariance of `M_{κ,u}`** (all real `κ`). -/
theorem Mmeas_translate (κ : ℝ) (u : L2T L) (a : ℝ) : Mmeas κ (QuantumNLS.BornTranslation.trans a u) = Mmeas κ u := by
  by_cases h : u = 0
  · subst h
    simp [map_zero, Mmeas_zero]
  have h' : QuantumNLS.BornTranslation.trans a u ≠ 0 := by
    intro h0
    apply h
    have := norm_trans a u
    rw [h0, norm_zero] at this
    exact norm_eq_zero.1 this.symm
  have hmu : muKappa (unitDir (QuantumNLS.BornTranslation.trans a u)) (norm_unitDir h') (κ * ‖u‖ ^ 2) =
      muKappa (unitDir u) (norm_unitDir h) (κ * ‖u‖ ^ 2) := by
    rw [muKappa_congr (unitDir_trans a u) (norm_unitDir h') (by rw [norm_trans, norm_unitDir h]) (κ * ‖u‖ ^ 2)]
    exact muKappa_trans a (unitDir u) (norm_unitDir h) _ _
  rw [Mmeas_of_ne κ h', Mmeas_of_ne κ h, norm_trans, hmu]

theorem Mfin_translate (κ : ℝ) (u : L2T L) (a : ℝ) : Mfin κ (QuantumNLS.BornTranslation.trans a u) = Mfin κ u :=
  Subtype.ext (Mmeas_translate κ u a)

end QuantumNLS.TranslationInvariance

#print axioms QuantumNLS.TranslationInvariance.bornMeasure_trans
#print axioms QuantumNLS.TranslationInvariance.isLimiting_trans
#print axioms QuantumNLS.TranslationInvariance.coeff_norm_trans
#print axioms QuantumNLS.TranslationInvariance.muKappa_trans
#print axioms QuantumNLS.TranslationInvariance.Mmeas_translate
