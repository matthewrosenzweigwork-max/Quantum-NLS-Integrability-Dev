import NlsGge.Ramer.LinearSmallJacobi
import NlsGge.Ramer.LinearDecomposition
import NlsGge.Ramer.FibreBridge
import NlsGge.Ramer.RamerJacobianHead
import NlsGge.Ramer.RamerLemma54Eventually

/-!
# D3: the Jacobi formula for the linear `T = Π ∘ S`

`map T⁻¹ γ_E = γ_E.withDensity (ofReal ∘ ramerJac K)` for `T = I + iK` a continuous linear
automorphism of `E`.

Null-set preservation needed (derived here):
* `hT` of Lemma 5.4 for the inner map `S`: `γ(S⁻¹' N) = 0` for `γ N = 0`.  D2 gives only
  `map S⁻¹ γ = J γ`, i.e. `γ(S N) = ∫_N J`; the needed direction follows because `J > 0` a.e.
  (`det₂ (I + A i) ≠ 0` since `‖A i‖ < 1/8`).
* `hTk` for `I + i P_k A`: a linear automorphism fixing tails beyond `k`; both it and its inverse
  have fibre-density pushforwards (FB 6 applied to `Φ` and to `Φ⁻¹`), so it is quasi-measure
  preserving with no positivity needed.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped Topology ENNReal

namespace NlsGge.Ramer

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

/-- A continuous linear automorphism of `E` fixing the tail coordinates beyond `n` is
quasi-measure-preserving (FB 6 applied to the inverse). -/
theorem qmp_of_sameTail (n : ℕ) (hs : (1 : ℝ) / 2 < s)
    (Φ : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s)
    (hfix : ∀ x, SameTail c s n (Φ x) x) :
    Measure.QuasiMeasurePreserving Φ (NlsGge.Measure.fullWeightedSequenceGaussian c s)
      (NlsGge.Measure.fullWeightedSequenceGaussian c s) := by
  have h := map_symm_eq_withDensity c s n hs Φ.symm (hfix_symm_clm c s n Φ hfix)
  rw [ContinuousLinearEquiv.symm_symm] at h
  refine ⟨Φ.continuous.measurable, ?_⟩
  rw [h]
  exact withDensity_absolutelyContinuous _ _

/-- `ramerJac` of a linear field with `‖L ∘ i‖ ≤ 1/2` is positive everywhere. -/
theorem ramerJac_pos_of_linear (hs : (1 : ℝ) / 2 < s)
    (L : FullWeightedHilbert c s →L[ℝ] ActualCM c)
    (hL : ∀ h : ActualCM c, ‖L (inclE c s hs h)‖ ≤ (1 / 2) * ‖h‖)
    (x : FullWeightedHilbert c s) : 0 < ramerJac c s hs (fun y => L y) x := by
  rw [ramerJac_eq]
  refine mul_pos (abs_pos.2 ?_) (Real.exp_pos _)
  apply det2_ne_zero_of_isUnit
  have h : ‖(hsDerivH c s hs (fun y => L y) x).toCLM‖ ≤ 1 / 2 := by
    rw [hsDerivH_toCLM]
    have e : fderiv ℝ (fun y => L y) x = L := L.fderiv
    rw [e]
    exact ContinuousLinearMap.opNorm_le_bound _ (by norm_num) hL
  exact isUnit_one_add_of_norm_le _ h

variable {c s}

/-- `map f (μ.withDensity h) = (map f μ).withDensity (h ∘ g)` for mutually inverse measurable
maps `f`, `g`. -/
theorem map_withDensity_inv {X : Type*} [MeasurableSpace X] (μ : Measure X) (f g : X → X)
    (hf : Measurable f) (hg : Measurable g) (hgf : ∀ x, g (f x) = x)
    (h : X → ℝ≥0∞) (hh : Measurable h) :
    (μ.withDensity h).map f = (μ.map f).withDensity (h ∘ g) := by
  ext B hB
  rw [Measure.map_apply hf hB, withDensity_apply _ (hf hB),
    withDensity_apply _ hB, setLIntegral_map hB (hh.comp hg) hf]
  simp [hgf]

variable (c s) in
/-- **D3: the Jacobi formula for a linear `T = I + iK`.** -/
theorem linear_map_symm (hs : (1 : ℝ) / 2 < s)
    (K : FullWeightedHilbert c s →L[ℝ] ActualCM c)
    (T : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s)
    (hT : ∀ x, T x = x + inclE c s hs (K x)) :
    (NlsGge.Measure.fullWeightedSequenceGaussian c s).map T.symm =
      (NlsGge.Measure.fullWeightedSequenceGaussian c s).withDensity
        (fun x => ENNReal.ofReal (ramerJac c s hs (fun y => K y) x)) := by
  set γ := NlsGge.Measure.fullWeightedSequenceGaussian c s with hγ
  have hs0 : 0 ≤ s := zero_le_of_half_lt hs
  obtain ⟨n, S, Pi, M, hAi, hS, hSs, hM, hPi, hPi2, hfix, J, hJm, hJae, hJ⟩ :=
    linearSmall_map_symm c s hs K T hT 1 one_pos
  set A : FullWeightedHilbert c s → ActualCM c := fun y => tailProj c n (K y) with hA
  have hAd : ContDiff ℝ 2 A := ((tailProj c n).comp K).contDiff
  have hTMS : TM c s hs A = ⇑S := funext fun x => (hS x).symm
  -- positivity of `ramerJac A`
  have hpos : ∀ x, 0 < ramerJac c s hs A x :=
    ramerJac_pos_of_linear c s hs ((tailProj c n).comp K)
      (fun h => (hAi h).trans (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _)))
  have hJpos : ∀ᵐ x ∂γ, J x ≠ 0 := by
    filter_upwards [hJae] with x hx
    rw [hx]; exact (ENNReal.ofReal_pos.2 (hpos x)).ne'
  -- `S` is quasi-measure-preserving
  have hSnull : ∀ N : Set (FullWeightedHilbert c s), γ N = 0 → γ (S ⁻¹' N) = 0 := by
    intro N hN
    set N' := toMeasurable γ N with hN'
    have hN'0 : γ N' = 0 := by rw [hN', measure_toMeasurable]; exact hN
    have hP : MeasurableSet (S ⁻¹' N') :=
      (measurableSet_toMeasurable γ N).preimage S.continuous.measurable
    have h1 : (γ.map S.symm) (S ⁻¹' N') = 0 := by
      rw [Measure.map_apply S.symm.continuous.measurable hP]
      have : S.symm ⁻¹' (S ⁻¹' N') = N' := by
        ext y; simp
      rw [this]; exact hN'0
    rw [hJ, withDensity_apply _ hP] at h1
    have h2 : ∀ᵐ x ∂γ.restrict (S ⁻¹' N'), J x = 0 :=
      (lintegral_eq_zero_iff hJm).1 h1
    have h3 : ∀ᵐ x ∂γ, x ∈ S ⁻¹' N' → J x = 0 := (ae_restrict_iff' hP).1 h2
    have h4 : γ (S ⁻¹' N') = 0 := by
      refine measure_eq_zero_iff_ae_notMem.2 ?_
      filter_upwards [h3, hJpos] with x a b hx
      exact b (a hx)
    exact measure_mono_null (preimage_mono (subset_toMeasurable γ N)) h4
  have hqS : Measure.QuasiMeasurePreserving S γ γ := by
    refine ⟨S.continuous.measurable, Measure.AbsolutelyContinuous.mk fun B hB hB0 => ?_⟩
    rw [Measure.map_apply S.continuous.measurable hB]
    exact hSnull B hB0
  have hTS : ∀ N : Set (FullWeightedHilbert c s), γ N = 0 →
      γ (univ ∩ TM c s hs A ⁻¹' N) = 0 := by
    intro N hN
    rw [univ_inter, hTMS]; exact hSnull N hN
  -- `hTk`
  have hTk : ∀ k : ℕ, ∀ N : Set (FullWeightedHilbert c s), γ N = 0 →
      γ (univ ∩ TM c s hs (projField k A) ⁻¹' N) = 0 := by
    intro k N hN
    set Ak : FullWeightedHilbert c s →L[ℝ] ActualCM c :=
      (headProj c k).comp ((tailProj c n).comp K) with hAk
    obtain ⟨Φ, M', hΦ, -, -, -⟩ := exists_neumann_equiv (inclE c s hs) Ak (1 / 8)
      (ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
        (fun h => (norm_headProj_le c k _).trans (hAi h))) (by norm_num)
    have hΦfix : ∀ x, SameTail c s k (Φ x) x := by
      intro x m hm
      have e : coordE c s (Φ x - x) m = 0 := by
        have : Φ x - x = inclE c s hs (headProj c k (tailProj c n (K x))) := by
          rw [hΦ x, add_sub_cancel_left]; rfl
        rw [this]; exact coordE_incl_headProj c s hs0 k _ m hm
      rw [coordE_sub] at e
      exact sub_eq_zero.1 e
    have hTMk : TM c s hs (projField k A) = ⇑Φ := funext fun x => (hΦ x).symm
    rw [univ_inter, hTMk]
    exact (qmp_of_sameTail c s k hs Φ hΦfix).preimage_null hN
  -- the head part `B`
  set B : FullWeightedHilbert c s →L[ℝ] ActualCM c :=
    (headProj c n).comp (K.comp (S.symm : FullWeightedHilbert c s →L[ℝ] FullWeightedHilbert c s))
    with hB
  have hPiB : TM c s hs (fun y => B y) = ⇑Pi := by
    funext x
    exact (sub_eq_iff_eq_add'.1 (hPi2 x)).symm
  have hBae := ramerJac_ae_eq_fibreJ c s hs (m := n) (fun y => B y) B.contDiff
    (fun x => headProj_idem n _)
  rw [hPiB] at hBae
  have hFB := map_symm_eq_withDensity c s n hs Pi hfix
  have hJPm : Measurable (fun x : FullWeightedHilbert c s => ENNReal.ofReal
      (fibreJ c n (fibreMapOf c s n Pi) (coordE c s x))) :=
    ((measurable_fibreJ_of_clm c s n Pi).comp (measurable_coordE c s)).ennreal_ofReal
  -- the product formula
  have hprod := ramer_lemma_5_4_eventually c s hs univ isOpen_univ A (fun y => B y) hAd B.contDiff
    (fun N hN => by simpa using hTS N hN) (Filter.Eventually.of_forall hTk)
  have hfun : (A + (fun y => B y) ∘ TM c s hs A) = fun y => K y := by
    funext y
    show tailProj c n (K y) + headProj c n (K (S.symm (TM c s hs A y))) = K y
    rw [show TM c s hs A y = S y from congrFun hTMS y, S.symm_apply_apply, tailProj_apply]; abel
  rw [hfun] at hprod
  -- assembling
  have hTsymm : (T.symm : FullWeightedHilbert c s → FullWeightedHilbert c s) =
      S.symm ∘ Pi.symm := by
    funext z
    rw [Function.comp_apply, ContinuousLinearEquiv.symm_apply_eq, ← hPi,
      ContinuousLinearEquiv.apply_symm_apply]
  have hSm : Measurable (S.symm : FullWeightedHilbert c s → FullWeightedHilbert c s) :=
    S.symm.continuous.measurable
  rw [hTsymm, ← Measure.map_map hSm Pi.symm.continuous.measurable, hFB]
  have hmw : (γ.withDensity (fun x => ENNReal.ofReal
      (fibreJ c n (fibreMapOf c s n Pi) (coordE c s x)))).map S.symm =
      (γ.map S.symm).withDensity (fun x => ENNReal.ofReal
        (fibreJ c n (fibreMapOf c s n Pi) (coordE c s (S x)))) :=
    map_withDensity_inv γ S.symm S hSm S.continuous.measurable (fun x => S.apply_symm_apply x)
      _ hJPm
  have hJPS : Measurable (fun x : FullWeightedHilbert c s => ENNReal.ofReal
        (fibreJ c n (fibreMapOf c s n Pi) (coordE c s (S x)))) :=
    hJPm.comp S.continuous.measurable
  rw [hmw, hJ, ← withDensity_mul _ hJm hJPS]
  refine withDensity_congr_ae ?_
  filter_upwards [hJae, hprod, hqS.ae hBae] with x h1 h2 h3
  have h2' := h2 (mem_univ x)
  have h2'' : ramerJac c s hs (fun y => K y) x =
      ramerJac c s hs (fun y => B y) (S x) * ramerJac c s hs A x := by
    rw [h2', show TM c s hs A x = S x from congrFun hTMS x]
  show J x * ENNReal.ofReal (fibreJ c n (fibreMapOf c s n Pi) (coordE c s (S x))) = _
  rw [h1, ← h3, h2'', ENNReal.ofReal_mul (ramerJac_nonneg c s hs _ _), mul_comm]

#check @qmp_of_sameTail
#check @ramerJac_pos_of_linear
#check @linear_map_symm
#print axioms qmp_of_sameTail
#print axioms ramerJac_pos_of_linear
#print axioms linear_map_symm

end NlsGge.Ramer
