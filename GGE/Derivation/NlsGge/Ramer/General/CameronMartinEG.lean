import Mathlib
import NlsGge.Ramer.General.SpaceTransferG
import NlsGge.Ramer.General.RamerLemma54G
import NlsGge.Ramer.General.RamerJacobianHeadG
import NlsGge.Ramer.General.RamerJacobianLimitsG
import NlsGge.Ramer.General.CameronMartinSetting

/-!
# CM-E, generalized (GD13): the Cameron–Martin theorem on `S.E`

Adapted from `NlsGge/Ramer/CameronMartinE.lean` over a `RamerSetting S`.  Dictionary:
`ramerA ↦ S.ramerA`, `ramerDiv ↦ S.ramerDiv`, `ramerJac ↦ S.ramerJac`, `TM ↦ S.TM`,
`projField ↦ S.projField`, `inclE ↦ S.incl`, `coordE ↦ S.coordE`, `headProj c k ↦ S.headProj k`,
`fullWeightedSequenceGaussian c s ↦ S.γE`, `fullWeightSequenceGaussian c.val ↦ S.γ`,
`actualSourceCMFiniteScorePartial(Lp) c e n ↦ cmScore(Lp) S.q (S.hcoord e) n`.

Sign conventions are as in the old file: `J^{const e} = exp(-δe - ‖e‖²/2)`; the `-` translation
has density `J^{const e}`, the `+` translation has density `J^{const (-e)}`.  The base case is
G2 goal 7 (`S.map_add_incl_eq_withDensity`), from which the `-` form is derived.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal RealInnerProductSpace

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer NlsGge.Measure

section CME

variable (S : NlsGge.Ramer.General.RamerSetting)

/-- The approximant of a constant field is the finite CM score, everywhere.
(Old: `ramerA_const_eq_score`.) -/
theorem ramerA_const_eq_score (n : ℕ) (e : S.H) (z : ℤ → ℂ) :
    S.ramerA n (fun _ => e) z = cmScore S.q (S.hcoord e) n z := by
  rw [S.ramerA_const n e z]
  unfold cmScore basisIndex
  rw [Finset.sum_product, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hw : 0 ≤ S.cmWeight m := (S.cmWeight_pos m).le
  have hb : ∀ (j : Fin 2) (x : S.H),
      ⟪weightedRealHilbertBasis S.cmWeight (m, j), x⟫ =
        ⟪Complex.orthonormalBasisOneI j,
          ((Real.sqrt (S.cmWeight m) : ℝ) : ℂ) * S.hcoord x m⟫ := by
    intro j x
    rw [weightedRealHilbertBasis_apply, weightedRealBasisVector_inner]
    rfl
  have hz : S.hcoord (S.headPt n z : S.H) m = z m := by
    simp [S.hcoord_headPt, hm]
  calc ∑ j : Fin 2, ⟪(S.headPt n z : S.H),
          weightedRealHilbertBasis S.cmWeight (m, j)⟫ *
        ⟪weightedRealHilbertBasis S.cmWeight (m, j), e⟫
      = ∑ j : Fin 2, ⟪Complex.orthonormalBasisOneI j,
          ((Real.sqrt (S.cmWeight m) : ℝ) : ℂ) * z m⟫ *
        ⟪Complex.orthonormalBasisOneI j,
          ((Real.sqrt (S.cmWeight m) : ℝ) : ℂ) * S.hcoord e m⟫ := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        have h1 : ⟪(S.headPt n z : S.H),
            weightedRealHilbertBasis S.cmWeight (m, j)⟫ =
            ⟪weightedRealHilbertBasis S.cmWeight (m, j),
              (S.headPt n z : S.H)⟫ := real_inner_comm _ _
        rw [h1, hb, hb, hz]
    _ = ⟪((Real.sqrt (S.cmWeight m) : ℝ) : ℂ) * z m,
          ((Real.sqrt (S.cmWeight m) : ℝ) : ℂ) * S.hcoord e m⟫ := by
        rw [← OrthonormalBasis.sum_inner_mul_inner Complex.orthonormalBasisOneI]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [real_inner_comm _ (Complex.orthonormalBasisOneI j)]
    _ = S.cmWeight m * ⟪S.hcoord e m, z m⟫ := by
        simp only [← Complex.real_smul, real_inner_smul_left, real_inner_smul_right]
        rw [← mul_assoc, Real.mul_self_sqrt hw, real_inner_comm]
    _ = 2 * (S.q m * (starRingEnd ℂ (S.hcoord e m) * z m).re) := by
        rw [Complex.inner]
        change (2 * S.q m) * _ = _
        ring_nf

/-- The finite CM score classes are a.e. equal to `ramerA n (const e)`.
(Old: `score_Lp_ae_eq_ramerA`.) -/
theorem score_Lp_ae_eq_ramerA (n : ℕ) (e : S.H) :
    (cmScoreLp S.q (S.hcoord e) n : (ℤ → ℂ) → ℝ) =ᵐ[S.γ]
      S.ramerA n (fun _ => e) := by
  refine (cmScoreLp_ae S.q (S.hcoord e) n).trans (Filter.Eventually.of_forall fun z => ?_)
  exact (S.ramerA_const_eq_score n e z).symm

/-- **Goal 1.** The Ramer divergence of the constant field `e` is the `L²` limit `Sc` of the
finite CM scores of `e`, `γ`-a.e. (Old: `ramerDiv_const_ae_eq`.) -/
theorem ramerDiv_const_ae_eq (e : S.H) (Sc : Lp ℝ 2 S.γ)
    (hS : Tendsto (fun N : ℕ => cmScoreLp S.q (S.hcoord e) N) atTop (𝓝 Sc)) :
    S.ramerDiv (fun _ => e) =ᵐ[S.γ] (Sc : (ℤ → ℂ) → ℝ) := by
  have h1 := (S.ramerDiv_spec (fun _ => e) contDiff_const).2.2
  have h2 := (tendstoInMeasure_of_tendsto_Lp hS).congr_left
    (fun n => S.score_Lp_ae_eq_ramerA n e)
  exact tendstoInMeasure_ae_unique h1 h2

theorem coordE_incl (e : S.H) : S.coordE (S.incl e) = S.hcoord e := by
  funext n; simp [coordE_apply]

/-- The density of Goal 2 as a function on sequences.
(Old: `aemeasurable_constDensity`.) -/
theorem aemeasurable_constDensity (e : S.H) :
    AEMeasurable (fun x : S.E => ENNReal.ofReal (S.ramerJac (fun _ => e) x)) S.γE := by
  have h := (S.ramerDiv_spec (fun _ => e) contDiff_const).1.aemeasurable
  have h2 : AEMeasurable (fun z => ENNReal.ofReal (Real.exp (-(S.ramerDiv (fun _ => e) z)
      - ‖e‖ ^ 2 / 2))) S.γ :=
    (Real.measurable_exp.comp_aemeasurable (h.neg.sub_const _)).ennreal_ofReal
  have h3 := h2.comp_quasiMeasurePreserving
    S.measurePreserving_coordE.quasiMeasurePreserving
  refine h3.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Function.comp, S.ramerJac_const e x]

/-- **Goal 2, `+` form.** `(x ↦ x + i e)_# γ_E = J^{const (-e)} · γ_E`.  Derived from G2 goal 7
(`S.map_add_incl_eq_withDensity`, density `exp (S_e - ‖e‖²/2)`).  (Old:
`map_add_inclE_eq_withDensity`; renamed because `S.map_add_incl_eq_withDensity` is G2's.) -/
theorem map_add_incl_eq_withDensity_ramerJac (e : S.H) :
    S.γE.map (fun x => x + S.incl e) =
      S.γE.withDensity (fun x => ENNReal.ofReal (S.ramerJac (fun _ => -e) x)) := by
  obtain ⟨Sc, hS, hmap⟩ := S.map_add_incl_eq_withDensity e
  rw [hmap]
  have hneg : S.hcoord (-e) = fun n => -S.hcoord e n := by
    funext n
    have := S.hcoord_smul (-1 : ℝ) e n
    simpa using this
  have hS' : Tendsto (fun N : ℕ => cmScoreLp S.q (S.hcoord (-e)) N) atTop (𝓝 (-Sc)) := by
    simp only [hneg, cmScoreLp_neg]
    exact hS.neg
  have hdiv := S.ramerDiv_const_ae_eq (-e) (-Sc) hS'
  have hdiv' : S.ramerDiv (fun _ => -e) =ᵐ[S.γ] fun z => -Sc z := by
    filter_upwards [hdiv, Lp.coeFn_neg Sc] with z h1 h2
    rw [h1, h2]; rfl
  refine withDensity_congr_ae ?_
  filter_upwards [S.ae_of_ae_coordE hdiv'] with x hx
  rw [S.ramerJac_const (-e) x, hx, norm_neg]
  congr 2
  ring

/-- **Goal 2.** Cameron–Martin on `S.E`, inverse-pushforward orientation:
`(x ↦ x - i e)_# γ_E = J^{const e} · γ_E`, `J^{const e} = exp(-δe - ‖e‖²/2)`.
(Old: `map_sub_inclE_eq_withDensity`.) -/
theorem map_sub_incl_eq_withDensity (e : S.H) :
    S.γE.map (fun x => x - S.incl e) =
      S.γE.withDensity (fun x => ENNReal.ofReal (S.ramerJac (fun _ => e) x)) := by
  have h := S.map_add_incl_eq_withDensity_ramerJac (-e)
  simpa only [map_neg, sub_eq_add_neg, neg_neg] using h

/-- **Goal 3 (minus).** (Old: `quasiMeasurePreserving_sub_inclE`.) -/
theorem quasiMeasurePreserving_sub_incl (e : S.H) :
    Measure.QuasiMeasurePreserving (fun x : S.E => x - S.incl e) S.γE S.γE :=
  ⟨measurable_id.sub_const _, by
    rw [S.map_sub_incl_eq_withDensity e]
    exact withDensity_absolutelyContinuous _ _⟩

/-- Null-set preservation by a translation on any `U` (R9c's `hT` shape for `T = τ_{ie}`).
Uses G2's `S.quasiMeasurePreserving_add_incl` (old `quasiMeasurePreserving_add_inclE`). -/
theorem translation_null_preserving (e : S.H) (U : Set S.E) :
    ∀ N : Set S.E, S.γE N = 0 → S.γE (U ∩ (fun y => y + S.incl e) ⁻¹' N) = 0 :=
  fun _ hN =>
    measure_mono_null Set.inter_subset_right
      ((S.quasiMeasurePreserving_add_incl e).preimage_null hN)

/-- Truncations of the constant field are translations by `i (P_k e)`. -/
theorem TM_projField_const (k : ℕ) (e : S.H) :
    S.TM (S.projField k (fun _ : S.E => e)) = fun y => y + S.incl (S.headProj k e) := rfl

theorem TM_const (e : S.H) :
    S.TM (fun _ : S.E => e) = fun y => y + S.incl e := rfl

/-- R9c's `hT` for `T = TM (const e)`, on any `U`. -/
theorem hT_TM_const (e : S.H) (U : Set S.E) :
    ∀ N : Set S.E, S.γE N = 0 → S.γE (U ∩ S.TM (fun _ => e) ⁻¹' N) = 0 :=
  S.translation_null_preserving e U

/-- R9c's `hTk` for `T = TM (projField k (const e))`, for every `k`, on any `U`. -/
theorem hTk_TM_const (e : S.H) (U : Set S.E) :
    ∀ k : ℕ, ∀ N : Set S.E, S.γE N = 0 →
      S.γE (U ∩ S.TM (S.projField k (fun _ => e)) ⁻¹' N) = 0 :=
  fun k => S.translation_null_preserving (S.headProj k e) U

/-- `hTk` in the "eventually in `k`" shape (R9c'). -/
theorem hTk_TM_const_eventually (e : S.H) (U : Set S.E) :
    ∀ᶠ k : ℕ in atTop, ∀ N : Set S.E, S.γE N = 0 →
      S.γE (U ∩ S.TM (S.projField k (fun _ => e)) ⁻¹' N) = 0 :=
  Filter.Eventually.of_forall (S.hTk_TM_const e U)

/-- **Goal 4, Ramer's (*) for the translation `τ_{ie}`** (Ramer §3 translation Jacobi formula).
(Old: `lintegral_image_add_inclE`.) -/
theorem lintegral_image_add_incl (e : S.H)
    (F : S.E → ℝ≥0∞) (hF : Measurable F) (V : Set S.E) (hV : MeasurableSet V) :
    ∫⁻ y in (fun x => x + S.incl e) '' V, F y ∂S.γE =
      ∫⁻ x in V, F (x + S.incl e) * ENNReal.ofReal (S.ramerJac (fun _ => e) x) ∂S.γE := by
  have hτ : Measurable (fun x : S.E => x - S.incl e) := measurable_id.sub_const _
  have himg : (fun x => x + S.incl e) '' V = (fun x : S.E => x - S.incl e) ⁻¹' V := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩; simpa using hx
    · intro hy; exact ⟨_, hy, sub_add_cancel _ _⟩
  have hg : Measurable (V.indicator (fun x : S.E => F (x + S.incl e))) :=
    (hF.comp (measurable_id.add_const _)).indicator hV
  rw [himg, ← lintegral_indicator (hτ hV), ← lintegral_indicator hV]
  have h1 : ∀ y : S.E,
      ((fun x : S.E => x - S.incl e) ⁻¹' V).indicator F y =
        (V.indicator (fun x : S.E => F (x + S.incl e))) (y - S.incl e) := by
    intro y
    by_cases hy : y - S.incl e ∈ V
    · rw [Set.indicator_of_mem (show y ∈ _ from hy), Set.indicator_of_mem hy, sub_add_cancel]
    · rw [Set.indicator_of_notMem (show y ∉ _ from hy), Set.indicator_of_notMem hy]
  simp_rw [h1]
  rw [← lintegral_map hg hτ, S.map_sub_incl_eq_withDensity e,
    lintegral_withDensity_eq_lintegral_mul₀ (S.aemeasurable_constDensity e) hg.aemeasurable]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ V
  · simp [Set.indicator_of_mem hx, mul_comm]
  · simp [Set.indicator_of_notMem hx]

/-- Goal 1 transported to `S.E`. (Old: `ramerDiv_const_coordE_ae_eq`.) -/
theorem ramerDiv_const_coordE_ae_eq (e : S.H) (Sc : Lp ℝ 2 S.γ)
    (hS : Tendsto (fun N : ℕ => cmScoreLp S.q (S.hcoord e) N) atTop (𝓝 Sc)) :
    ∀ᵐ x ∂S.γE, S.ramerDiv (fun _ => e) (S.coordE x) = Sc (S.coordE x) :=
  S.ae_of_ae_coordE (S.ramerDiv_const_ae_eq e Sc hS)

/-- R9c's translation corollary with `hT`, `hTk` discharged, on any open `U`.
(Old: `ramer_translation_unconditional`.) -/
theorem ramer_translation_unconditional (U : Set S.E) (hU : IsOpen U) (e : S.H)
    (G : S.E → S.H) (hG : ContDiff ℝ 2 G) :
    ∀ᵐ x ∂S.γE, x ∈ U →
      S.ramerJac ((fun _ => e) + G ∘ fun y => y + S.incl e) x =
        S.ramerJac G (x + S.incl e) *
          Real.exp (-(S.ramerDiv (fun _ => e) (S.coordE x)) - ‖e‖ ^ 2 / 2) :=
  S.ramer_translation U hU e G hG (S.translation_null_preserving e U)
    (fun k => S.translation_null_preserving (S.headProj k e) U)

end CME

end NlsGge.Ramer.General.RamerSetting
