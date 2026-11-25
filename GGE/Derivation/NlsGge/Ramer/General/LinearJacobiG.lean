import Mathlib
import NlsGge.Ramer.General.LinearSmallJacobiG
import NlsGge.Ramer.General.LinearDecompositionG
import NlsGge.Ramer.General.FibreBridgeGb
import NlsGge.Ramer.General.RamerJacobianHeadG
import NlsGge.Ramer.General.RamerLemma54EventuallyG
import NlsGge.Ramer.General.RamerStep8cG

/-!
# D3: the Jacobi formula for the linear `T = Π ∘ Q`, generalized (GE4)

Adapted from `NlsGge/Ramer/LinearJacobi.lean`.  Dictionary: `c, s, hs ↦ S`,
`FullWeightedHilbert c s ↦ S.E`, `ActualCM c ↦ S.H`, `inclE ↦ S.incl`,
`fullWeightedSequenceGaussian c s ↦ S.γE`, `TM ↦ S.TM`, `ramerJac ↦ S.ramerJac`,
`headProj / tailProj ↦ S.headProj / S.tailProj`, `SameTail ↦ S.SameTail`.

The linear equivalence called `S` in the old file is called `Q` here.  No isotropy is used.

`map T⁻¹ γ_E = γ_E.withDensity (ofReal ∘ ramerJac K)` for `T = I + iK` a continuous linear
automorphism of `E`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped Topology ENNReal

namespace NlsGge.Ramer.Gen

/-- `map f (μ.withDensity h) = (map f μ).withDensity (h ∘ g)` for mutually inverse measurable
maps `f`, `g`. (Old: `map_withDensity_inv`.) -/
theorem map_withDensity_inv {X : Type*} [MeasurableSpace X] (μ : Measure X) (f g : X → X)
    (hf : Measurable f) (hg : Measurable g) (hgf : ∀ x, g (f x) = x)
    (h : X → ℝ≥0∞) (hh : Measurable h) :
    (μ.withDensity h).map f = (μ.map f).withDensity (h ∘ g) := by
  ext B hB
  rw [Measure.map_apply hf hB, withDensity_apply _ (hf hB),
    withDensity_apply _ hB, setLIntegral_map hB (hh.comp hg) hf]
  simp [hgf]

end NlsGge.Ramer.Gen

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer NlsGge.Ramer.Gen NlsGge.Analysis.RegularizedDeterminant

variable (S : NlsGge.Ramer.General.RamerSetting)

/-- A continuous linear automorphism of `E` fixing the tail coordinates beyond `n` is
quasi-measure-preserving (FB 6 applied to the inverse). (Old: `qmp_of_sameTail`.) -/
theorem qmp_of_sameTail (n : ℕ)
    (Φ : S.E ≃L[ℝ] S.E)
    (hfix : ∀ x, S.SameTail n (Φ x) x) :
    Measure.QuasiMeasurePreserving Φ S.γE S.γE := by
  have h := S.map_symm_eq_withDensity n Φ.symm (S.hfix_symm_clm n Φ hfix)
  rw [ContinuousLinearEquiv.symm_symm] at h
  refine ⟨Φ.continuous.measurable, ?_⟩
  rw [h]
  exact withDensity_absolutelyContinuous _ _

/-- `ramerJac` of a linear field with `‖L ∘ i‖ ≤ 1/2` is positive everywhere.
(Old: `ramerJac_pos_of_linear`.) -/
theorem ramerJac_pos_of_linear
    (L : S.E →L[ℝ] S.H)
    (hL : ∀ h : S.H, ‖L (S.incl h)‖ ≤ (1 / 2) * ‖h‖)
    (x : S.E) : 0 < S.ramerJac (fun y => L y) x := by
  rw [S.ramerJac_eq]
  refine mul_pos (abs_pos.2 ?_) (Real.exp_pos _)
  apply det2_ne_zero_of_isUnit
  have h : ‖(S.hsDerivH (fun y => L y) x).toCLM‖ ≤ 1 / 2 := by
    rw [S.hsDerivH_toCLM]
    have e : fderiv ℝ (fun y => L y) x = L := L.fderiv
    rw [e]
    exact ContinuousLinearMap.opNorm_le_bound _ (by norm_num) hL
  exact isUnit_one_add_of_norm_le _ h

/-- **D3: the Jacobi formula for a linear `T = I + iK`.** (Old: `linear_map_symm`.) -/
theorem linear_map_symm
    (K : S.E →L[ℝ] S.H)
    (T : S.E ≃L[ℝ] S.E)
    (hT : ∀ x, T x = x + S.incl (K x)) :
    S.γE.map T.symm =
      S.γE.withDensity
        (fun x => ENNReal.ofReal (S.ramerJac (fun y => K y) x)) := by
  set γ := S.γE with hγ
  obtain ⟨n, Q, Pi, M, hAi, hS, hSs, hM, hPi, hPi2, hfix, J, hJm, hJae, hJ⟩ :=
    S.linearSmall_map_symm K T hT 1 one_pos
  set A : S.E → S.H := fun y => S.tailProj n (K y) with hA
  have hAd : ContDiff ℝ 2 A := ((S.tailProj n).comp K).contDiff
  have hTMS : S.TM A = ⇑Q := funext fun x => (hS x).symm
  -- positivity of `ramerJac A`
  have hpos : ∀ x, 0 < S.ramerJac A x :=
    S.ramerJac_pos_of_linear ((S.tailProj n).comp K)
      (fun h => (hAi h).trans (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _)))
  have hJpos : ∀ᵐ x ∂γ, J x ≠ 0 := by
    filter_upwards [hJae] with x hx
    rw [hx]; exact (ENNReal.ofReal_pos.2 (hpos x)).ne'
  -- `Q` is quasi-measure-preserving
  have hSnull : ∀ N : Set S.E, γ N = 0 → γ (Q ⁻¹' N) = 0 := by
    intro N hN
    set N' := toMeasurable γ N with hN'
    have hN'0 : γ N' = 0 := by rw [hN', measure_toMeasurable]; exact hN
    have hP : MeasurableSet (Q ⁻¹' N') :=
      (measurableSet_toMeasurable γ N).preimage Q.continuous.measurable
    have h1 : (γ.map Q.symm) (Q ⁻¹' N') = 0 := by
      rw [Measure.map_apply Q.symm.continuous.measurable hP]
      have : Q.symm ⁻¹' (Q ⁻¹' N') = N' := by
        ext y; simp
      rw [this]; exact hN'0
    rw [hJ, withDensity_apply _ hP] at h1
    have h2 : ∀ᵐ x ∂γ.restrict (Q ⁻¹' N'), J x = 0 :=
      (lintegral_eq_zero_iff hJm).1 h1
    have h3 : ∀ᵐ x ∂γ, x ∈ Q ⁻¹' N' → J x = 0 := (ae_restrict_iff' hP).1 h2
    have h4 : γ (Q ⁻¹' N') = 0 := by
      refine measure_eq_zero_iff_ae_notMem.2 ?_
      filter_upwards [h3, hJpos] with x a b hx
      exact b (a hx)
    exact measure_mono_null (preimage_mono (subset_toMeasurable γ N)) h4
  have hqS : Measure.QuasiMeasurePreserving Q γ γ := by
    refine ⟨Q.continuous.measurable, Measure.AbsolutelyContinuous.mk fun B hB hB0 => ?_⟩
    rw [Measure.map_apply Q.continuous.measurable hB]
    exact hSnull B hB0
  have hTS : ∀ N : Set S.E, γ N = 0 →
      γ (univ ∩ S.TM A ⁻¹' N) = 0 := by
    intro N hN
    rw [univ_inter, hTMS]; exact hSnull N hN
  -- `hTk`
  have hTk : ∀ k : ℕ, ∀ N : Set S.E, γ N = 0 →
      γ (univ ∩ S.TM (S.projField k A) ⁻¹' N) = 0 := by
    intro k N hN
    set Ak : S.E →L[ℝ] S.H :=
      (S.headProj k).comp ((S.tailProj n).comp K) with hAk
    obtain ⟨Φ, M', hΦ, -, -, -⟩ := Gen.exists_neumann_equiv (S.incl) Ak (1 / 8)
      (ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
        (fun h => (S.norm_headProj_le k _).trans (hAi h))) (by norm_num)
    have hΦfix : ∀ x, S.SameTail k (Φ x) x := by
      intro x m hm
      have e : S.coord m (Φ x - x) = 0 := by
        have : Φ x - x = S.incl (S.headProj k (S.tailProj n (K x))) := by
          rw [hΦ x, add_sub_cancel_left]; rfl
        rw [this]; exact S.coord_incl_headProj k _ m hm
      rw [S.coord_sub] at e
      exact sub_eq_zero.1 e
    have hTMk : S.TM (S.projField k A) = ⇑Φ := funext fun x => (hΦ x).symm
    rw [univ_inter, hTMk]
    exact (S.qmp_of_sameTail k Φ hΦfix).preimage_null hN
  -- the head part `B`
  set B : S.E →L[ℝ] S.H :=
    (S.headProj n).comp (K.comp (Q.symm : S.E →L[ℝ] S.E))
    with hB
  have hPiB : S.TM (fun y => B y) = ⇑Pi := by
    funext x
    exact (sub_eq_iff_eq_add'.1 (hPi2 x)).symm
  have hBae := S.ramerJac_ae_eq_fibreJ (m := n) (fun y => B y) B.contDiff
    (fun x => S.headProj_idem n _)
  rw [hPiB] at hBae
  have hFB := S.map_symm_eq_withDensity n Pi hfix
  have hJPm : Measurable (fun x : S.E => ENNReal.ofReal
      (S.fibreJ n (S.fibreMapOf n Pi) (S.coordE x))) :=
    ((S.measurable_fibreJ_of_clm n Pi).comp (S.measurable_coordE)).ennreal_ofReal
  -- the product formula
  have hprod := S.ramer_lemma_5_4_eventually univ isOpen_univ A (fun y => B y) hAd B.contDiff
    (fun N hN => by simpa using hTS N hN) (Filter.Eventually.of_forall hTk)
  have hfun : (A + (fun y => B y) ∘ S.TM A) = fun y => K y := by
    funext y
    show S.tailProj n (K y) + S.headProj n (K (Q.symm (S.TM A y))) = K y
    rw [show S.TM A y = Q y from congrFun hTMS y, Q.symm_apply_apply, S.tailProj_apply]; abel
  rw [hfun] at hprod
  -- assembling
  have hTsymm : (T.symm : S.E → S.E) = Q.symm ∘ Pi.symm := by
    funext z
    rw [Function.comp_apply, ContinuousLinearEquiv.symm_apply_eq, ← hPi,
      ContinuousLinearEquiv.apply_symm_apply]
  have hSm : Measurable (Q.symm : S.E → S.E) :=
    Q.symm.continuous.measurable
  rw [hTsymm, ← Measure.map_map hSm Pi.symm.continuous.measurable, hFB]
  have hmw : (γ.withDensity (fun x => ENNReal.ofReal
      (S.fibreJ n (S.fibreMapOf n Pi) (S.coordE x)))).map Q.symm =
      (γ.map Q.symm).withDensity (fun x => ENNReal.ofReal
        (S.fibreJ n (S.fibreMapOf n Pi) (S.coordE (Q x)))) :=
    Gen.map_withDensity_inv γ Q.symm Q hSm Q.continuous.measurable
      (fun x => Q.apply_symm_apply x) _ hJPm
  have hJPS : Measurable (fun x : S.E => ENNReal.ofReal
        (S.fibreJ n (S.fibreMapOf n Pi) (S.coordE (Q x)))) :=
    hJPm.comp Q.continuous.measurable
  rw [hmw, hJ, ← withDensity_mul _ hJm hJPS]
  refine withDensity_congr_ae ?_
  filter_upwards [hJae, hprod, hqS.ae hBae] with x h1 h2 h3
  have h2' := h2 (mem_univ x)
  have h2'' : S.ramerJac (fun y => K y) x =
      S.ramerJac (fun y => B y) (Q x) * S.ramerJac A x := by
    rw [h2', show S.TM A x = Q x from congrFun hTMS x]
  show J x * ENNReal.ofReal (S.fibreJ n (S.fibreMapOf n Pi) (S.coordE (Q x))) = _
  rw [h1, ← h3, h2'', ENNReal.ofReal_mul (S.ramerJac_nonneg _ _), mul_comm]


end NlsGge.Ramer.General.RamerSetting
