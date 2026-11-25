import Mathlib
import NlsGge.Ramer.General.RamerJacobianLimitsG
import NlsGge.Ramer.General.RamerStep8BridgeG
import NlsGge.Ramer.General.RamerStep8cG

/-!
# R9c, generalized (GD12): Ramer Lemma 5.4, local form (Step 9)

Adapted from `NlsGge/Ramer/RamerLemma54.lean` over a `RamerSetting S`.  Dictionary:
`ramerDiv ↦ S.ramerDiv`, `ramerJac ↦ S.ramerJac`, `TM ↦ S.TM`, `compField ↦ S.compField`,
`projField ↦ S.projField`, `rangeComp ↦ S.rangeComp`, `ramerA ↦ S.ramerA`, `ramerJE ↦ S.ramerJE`,
`headProj c m ↦ S.headProj m`, `inclE ↦ S.incl`, `hsDerivH ↦ S.hsDerivH`, `coordE ↦ S.coordE`,
`headCoord c s n ↦ S.headCoordE n`, `fullWeightedSequenceGaussian c s ↦ S.γE`,
`fullWeightSequenceGaussian c.val ↦ S.γ`.  The null-set hypotheses `hT`, `hTk` are kept verbatim.
No norm of `E` is used.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal RealInnerProductSpace

namespace NlsGge.Ramer.Gen

/-- Null-set transfer through a map that preserves null sets on `U`. -/
theorem ae_on_comp {α : Type*} [MeasurableSpace α] {μ : Measure α} {U : Set α} {T : α → α}
    (hT : ∀ N : Set α, μ N = 0 → μ (U ∩ T ⁻¹' N) = 0) {P : α → Prop}
    (h : ∀ᵐ y ∂μ, P y) : ∀ᵐ x ∂μ, x ∈ U → P (T x) := by
  have h0 : μ {y | ¬ P y} = 0 := ae_iff.1 h
  have := measure_eq_zero_iff_ae_notMem.1 (hT _ h0)
  filter_upwards [this] with x hx hxU
  by_contra hP
  exact hx ⟨hxU, hP⟩

end NlsGge.Ramer.Gen

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer NlsGge.Analysis.RegularizedDeterminant

section Prelim

variable (S : NlsGge.Ramer.General.RamerSetting)

theorem headProj_headProj_of_le {k n : ℕ} (hkn : k ≤ n) (w : S.H) :
    S.headProj n (S.headProj k w) = S.headProj k w := by
  apply S.hcoord_ext
  intro m
  rw [S.hcoord_headProj, S.hcoord_headProj]
  split_ifs with h1 h2 h2 <;>
    first | rfl | exact absurd (symmetricModes_mono hkn h2) h1

theorem headProj_projField_of_le {k n : ℕ} (hkn : k ≤ n) (M : S.E → S.H)
    (x : S.E) : S.headProj n (S.projField k M x) = S.projField k M x :=
  S.headProj_headProj_of_le hkn _

theorem hsDerivH_apply (M : S.E → S.H)
    (x : S.E) (v : S.H) :
    (S.hsDerivH M x).toCLM v = fderiv ℝ M x (S.incl v) :=
  congrArg (fun f => f v) (S.hsDerivH_toCLM M x)

theorem hsDerivH_add (M₁ M₂ : S.E → S.H)
    (h₁ : Differentiable ℝ M₁) (h₂ : Differentiable ℝ M₂) (x : S.E) :
    S.hsDerivH (M₁ + M₂) x = S.hsDerivH M₁ x + S.hsDerivH M₂ x := by
  apply HilbertSchmidt.ext
  intro v
  have hf : fderiv ℝ (M₁ + M₂) x = fderiv ℝ M₁ x + fderiv ℝ M₂ x := fderiv_add (h₁ x) (h₂ x)
  rw [HilbertSchmidt.toCLM_add, add_apply, S.hsDerivH_apply, S.hsDerivH_apply, S.hsDerivH_apply]
  exact (congrArg (fun D => D (S.incl v)) hf).trans rfl

theorem hsDerivH_const (e : S.H) (x : S.E) :
    S.hsDerivH (fun _ => e) x = 0 := by
  apply HilbertSchmidt.ext
  intro v
  rw [S.hsDerivH_apply]
  simp

/-- If `M = 0` near `x` then `hsDerivH M x = 0`. -/
theorem hsDerivH_eq_zero_of_eventuallyEq (M : S.E → S.H) (x : S.E)
    (h : M =ᶠ[𝓝 x] fun _ => 0) : S.hsDerivH M x = 0 := by
  have : fderiv ℝ M x = fderiv ℝ (fun _ : S.E => (0 : S.H)) x :=
    h.fderiv_eq
  apply HilbertSchmidt.ext
  intro v
  rw [S.hsDerivH_apply, this]
  simp

/-- `ramerDiv (P_n ∘ M) = ramerA n M` a.e. -/
theorem ramerDiv_projField_ae (n : ℕ)
    (M : S.E → S.H) (hM : ContDiff ℝ 2 M) :
    S.ramerDiv (S.projField n M) =ᵐ[S.γ]
      S.ramerA n M := by
  filter_upwards [S.ramerDiv_ae_eq_ramerA (S.projField n M)
    (S.contDiff_projField _ M hM) (fun x => S.headProj_idem _ _)] with z hz
  rw [hz, S.ramerA_projField _ M (hM.differentiable (by norm_num))]

/-- A common subsequence along which the divergences of the projections of two fields converge. -/
theorem exists_common_subseq (G F : S.E → S.H)
    (hG : ContDiff ℝ 2 G) (hF : ContDiff ℝ 2 F) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ z ∂(S.γ),
        Tendsto (fun j => S.ramerDiv (S.projField (φ j) G) z) atTop
          (𝓝 (S.ramerDiv G z)) ∧
        Tendsto (fun j => S.ramerDiv (S.projField (φ j) F) z) atTop
          (𝓝 (S.ramerDiv F z)) := by
  obtain ⟨ψ, hψ, a1⟩ := (S.ramerDiv_spec G hG).2.2.exists_seq_tendsto_ae
  obtain ⟨φ₂, hφ₂, a2⟩ := NlsGge.Ramer.Gen.exists_subseq_ae_of_tendstoInMeasure (S.ramerDiv_spec F hF).2.2 hψ
  refine ⟨fun j => ψ (φ₂ j), hψ.comp hφ₂, ?_⟩
  have eG : ∀ᵐ z ∂(S.γ), ∀ j,
      S.ramerDiv (S.projField (ψ (φ₂ j)) G) z =
        S.ramerA (ψ (φ₂ j)) G z :=
    ae_all_iff.2 fun j => S.ramerDiv_projField_ae _ G hG
  have eF : ∀ᵐ z ∂(S.γ), ∀ j,
      S.ramerDiv (S.projField (ψ (φ₂ j)) F) z =
        S.ramerA (ψ (φ₂ j)) F z :=
    ae_all_iff.2 fun j => S.ramerDiv_projField_ae _ F hF
  filter_upwards [a1, a2, eG, eF] with z z1 z2 z3 z4
  refine ⟨?_, ?_⟩
  · exact (z1.comp hφ₂.tendsto_atTop).congr (fun j => (z3 j).symm)
  · exact z2.congr (fun j => (z4 j).symm)

end Prelim

section Conv

variable (S : NlsGge.Ramer.General.RamerSetting)

theorem continuous_ramerA_coordE (n : ℕ)
    (M : S.E → S.H) (hM : ContDiff ℝ 1 M) :
    Continuous (fun y => S.ramerA n M (S.coordE y)) := by
  have hD : Continuous (fderiv ℝ M) := hM.continuous_fderiv one_ne_zero
  have hMc : Continuous M := hM.continuous
  have hh : Continuous (fun y => ((S.headCoordE n y : S.head n) : S.H)) :=
    continuous_subtype_val.comp (S.headCoordE n).continuous
  simp only [S.ramerA_eq, S.realization_coordE, ← S.headCoordE_apply]
  unfold NlsGge.Ramer.General.RamerSetting.ramerSum
  refine continuous_finsetSum _ (fun p _ => ?_)
  exact ((hh.inner continuous_const).mul (continuous_const.inner hMc)).sub
    (continuous_const.inner (hD.clm_apply continuous_const))

theorem continuous_ramerJE_ramerA (n : ℕ)
    (M : S.E → S.H) (hM : ContDiff ℝ 1 M) :
    Continuous (S.ramerJE M (S.ramerA n M)) := by
  have : S.ramerJE M (S.ramerA n M) = fun y =>
      |det2 (S.hsDerivH M y)| *
        Real.exp (-(S.ramerA n M (S.coordE y)) - ‖M y‖ ^ 2 / 2) :=
    funext (S.ramerJE_eq _ _)
  rw [this]
  exact (S.continuous_det2_hsDerivH M hM).abs.mul
    (Real.continuous_exp.comp ((S.continuous_ramerA_coordE n M hM).neg.sub
      ((hM.continuous.norm.pow 2).div_const 2)))

theorem hsDerivH_rangeComp (m : ℕ) (G : S.E → S.H)
    (hG : Differentiable ℝ G) (M : S.E → S.H)
    (hM : Differentiable ℝ M) (x : S.E) :
    S.hsDerivH (S.rangeComp m G (S.TM M)) x =
      HilbertSchmidt.postcompose (S.headProj m)
        (S.hsDerivH G (S.TM M x) +
          mulHS (S.hsDerivH G (S.TM M x)) (S.hsDerivH M x)) := by
  apply HilbertSchmidt.ext
  intro v
  rw [S.hsDerivH_apply, S.fderiv_rangeComp m G hG M hM]
  change _ = S.headProj m ((S.hsDerivH G (S.TM M x) +
    mulHS (S.hsDerivH G (S.TM M x)) (S.hsDerivH M x)).toCLM v)
  simp only [HilbertSchmidt.toCLM_add, add_apply, toCLM_mulHS, ContinuousLinearMap.comp_apply,
    S.hsDerivH_apply, map_add]

theorem tendsto_TM_projField (K : S.E → S.H)
    (y : S.E) :
    Tendsto (fun k : ℕ => S.TM (S.projField k K) y) atTop (𝓝 (S.TM K y)) := by
  unfold TM
  exact tendsto_const_nhds.add ((S.incl).continuous.continuousAt.tendsto.comp
    (S.tendsto_projField_apply K y))

theorem tendsto_hsDerivH_rangeComp (m : ℕ)
    (G K : S.E → S.H) (hG : ContDiff ℝ 1 G) (hK : ContDiff ℝ 1 K)
    (x : S.E) :
    Tendsto (fun k : ℕ => S.hsDerivH (S.rangeComp m G (S.TM (S.projField k K))) x) atTop
      (𝓝 (S.hsDerivH (S.rangeComp m G (S.TM K)) x)) := by
  have dG := hG.differentiable one_ne_zero
  have dK := hK.differentiable one_ne_zero
  have dKk : ∀ k, Differentiable ℝ (S.projField k K) := fun k =>
    (S.contDiff_projField k K hK).differentiable one_ne_zero
  have e : ∀ k : ℕ, S.hsDerivH (S.rangeComp m G (S.TM (S.projField k K))) x =
      HilbertSchmidt.postcompose (S.headProj m)
        (S.hsDerivH G (S.TM (S.projField k K) x) +
          mulHS (S.hsDerivH G (S.TM (S.projField k K) x))
            (S.hsDerivH (S.projField k K) x)) :=
    fun k => S.hsDerivH_rangeComp m G dG _ (dKk k) x
  simp only [e, S.hsDerivH_rangeComp m G dG K dK]
  have hD : Tendsto (fun k : ℕ => S.hsDerivH G (S.TM (S.projField k K) x)) atTop
      (𝓝 (S.hsDerivH G (S.TM K x))) :=
    ((S.continuous_hsDerivH G hG).tendsto _).comp (S.tendsto_TM_projField K x)
  have hA := S.tendsto_hsDerivH_projField K dK x
  have hm := (mulHS.continuous₂.tendsto (S.hsDerivH G (S.TM K x), S.hsDerivH K x)).comp
    (hD.prodMk_nhds hA)
  exact ((HilbertSchmidt.postcomposeContinuous (S.headProj m)).continuous.tendsto _).comp
    (hD.add hm)

end Conv

section Lemma

variable (S : NlsGge.Ramer.General.RamerSetting)

/-- Step 2/Step 1: `J^{I+P_{φ j}M} → J^{I+M}` a.e., given convergence of the divergences. -/
theorem tendsto_ramerJac_projField_ae (M : S.E → S.H) (hM : ContDiff ℝ 2 M) (φ : ℕ → ℕ)
    (hφ : StrictMono φ)
    (hdiv : ∀ᵐ z ∂(S.γ),
      Tendsto (fun j => S.ramerDiv (S.projField (φ j) M) z) atTop
        (𝓝 (S.ramerDiv M z))) :
    ∀ᵐ x ∂(S.γE),
      Tendsto (fun j => S.ramerJac (S.projField (φ j) M) x) atTop
        (𝓝 (S.ramerJac M x)) := by
  filter_upwards [S.ae_of_ae_coordE hdiv] with x hx
  exact S.tendsto_ramerJac (fun j => S.projField (φ j) M) M x
    ((S.tendsto_projField_apply M x).comp hφ.tendsto_atTop)
    ((S.tendsto_hsDerivH_projField M (hM.differentiable (by norm_num)) x).comp
      hφ.tendsto_atTop) hx

/-- Step 4: `J^{K + P_{φ j} F} → J^{K + F}` a.e. -/
theorem tendsto_ramerJac_add_projField (K F : S.E → S.H) (hK : ContDiff ℝ 2 K) (hF : ContDiff ℝ 2 F)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hdiv : ∀ᵐ z ∂(S.γ),
      Tendsto (fun j => S.ramerDiv (S.projField (φ j) F) z) atTop
        (𝓝 (S.ramerDiv F z))) :
    ∀ᵐ x ∂(S.γE),
      Tendsto (fun j => S.ramerJac (K + S.projField (φ j) F) x) atTop
        (𝓝 (S.ramerJac (K + F) x)) := by
  have dK : Differentiable ℝ K := hK.differentiable (by norm_num)
  have dF : Differentiable ℝ F := hF.differentiable (by norm_num)
  have dFj : ∀ j, Differentiable ℝ (S.projField (φ j) F) := fun j =>
    (S.contDiff_projField _ F hF).differentiable (by norm_num)
  have hadd : ∀ᵐ z ∂(S.γ), ∀ j,
      S.ramerDiv (K + S.projField (φ j) F) z =
        S.ramerDiv K z + S.ramerDiv (S.projField (φ j) F) z := by
    refine ae_all_iff.2 fun j => ?_
    filter_upwards [S.ramerDiv_add_ae K (S.projField (φ j) F) hK
      (S.contDiff_projField _ F hF)] with z hz
    exact hz
  have h0 : ∀ᵐ z ∂(S.γ),
      S.ramerDiv (K + F) z = S.ramerDiv K z + S.ramerDiv F z := by
    filter_upwards [S.ramerDiv_add_ae K F hK hF] with z hz
    exact hz
  have hz : ∀ᵐ z ∂(S.γ),
      Tendsto (fun j => S.ramerDiv (K + S.projField (φ j) F) z) atTop
        (𝓝 (S.ramerDiv (K + F) z)) := by
    filter_upwards [hadd, h0, hdiv] with z a b d
    rw [b]
    exact (tendsto_const_nhds.add d).congr (fun j => (a j).symm)
  filter_upwards [S.ae_of_ae_coordE hz] with x hx
  refine S.tendsto_ramerJac _ _ x ?_ ?_ hx
  · exact tendsto_const_nhds.add ((S.tendsto_projField_apply F x).comp hφ.tendsto_atTop)
  · have e : ∀ j, S.hsDerivH (K + S.projField (φ j) F) x =
        S.hsDerivH K x + S.hsDerivH (S.projField (φ j) F) x :=
      fun j => S.hsDerivH_add K _ dK (dFj j) x
    simp only [e, S.hsDerivH_add K F dK dF x]
    exact tendsto_const_nhds.add
      ((S.tendsto_hsDerivH_projField F dF x).comp hφ.tendsto_atTop)

/-- Step 3 (convergence in `k`): for fixed `m`, `J^{K_k + P_m G ∘ (I + iK_k)} → J^{K + P_m G ∘ (I+iK)}`. -/
theorem tendsto_ramerJac_compField_proj (m : ℕ)
    (G K : S.E → S.H) (hG : ContDiff ℝ 2 G) (hK : ContDiff ℝ 2 K)
    (κ : ℕ → ℕ) (hκ : StrictMono κ)
    (hdiv : ∀ᵐ z ∂(S.γ),
      Tendsto (fun j => S.ramerDiv (S.projField (κ j) K) z) atTop
        (𝓝 (S.ramerDiv K z))) :
    ∀ᵐ x ∂(S.γE),
      Tendsto (fun j => S.ramerJac
          (S.compField (S.projField (κ j) K) (S.projField m G)) x) atTop
        (𝓝 (S.ramerJac (S.compField K (S.projField m G)) x)) := by
  have dK : Differentiable ℝ K := hK.differentiable (by norm_num)
  have dKk : ∀ k, Differentiable ℝ (S.projField k K) := fun k =>
    (S.contDiff_projField k K hK).differentiable (by norm_num)
  have hRc : ∀ k : ℕ, ContDiff ℝ 2 (S.rangeComp m G (S.TM (S.projField k K))) := fun k =>
    S.contDiff_rangeComp m G _ hG (S.contDiff_projField k K hK)
  have hRcK : ContDiff ℝ 2 (S.rangeComp m G (S.TM K)) := S.contDiff_rangeComp m G K hG hK
  have dRc : ∀ k : ℕ, Differentiable ℝ (S.rangeComp m G (S.TM (S.projField k K))) := fun k =>
    (hRc k).differentiable (by norm_num)
  have dRcK : Differentiable ℝ (S.rangeComp m G (S.TM K)) := hRcK.differentiable (by norm_num)
  have hadd : ∀ᵐ z ∂(S.γ), ∀ j,
      S.ramerDiv (S.projField (κ j) K + S.rangeComp m G (S.TM (S.projField (κ j) K))) z =
        S.ramerDiv (S.projField (κ j) K) z +
          S.ramerDiv (S.rangeComp m G (S.TM (S.projField (κ j) K))) z := by
    refine ae_all_iff.2 fun j => ?_
    filter_upwards [S.ramerDiv_add_ae _ _ (S.contDiff_projField (κ j) K hK) (hRc (κ j))]
      with z hz
    exact hz
  have h0 : ∀ᵐ z ∂(S.γ),
      S.ramerDiv (K + S.rangeComp m G (S.TM K)) z =
        S.ramerDiv K z + S.ramerDiv (S.rangeComp m G (S.TM K)) z := by
    filter_upwards [S.ramerDiv_add_ae K _ hK hRcK] with z hz
    exact hz
  have hrc := S.ramerDiv_rangeComp_tendsto_ae m G K hG hK
  have hz : ∀ᵐ z ∂(S.γ),
      Tendsto (fun j => S.ramerDiv
          (S.projField (κ j) K + S.rangeComp m G (S.TM (S.projField (κ j) K))) z) atTop
        (𝓝 (S.ramerDiv (K + S.rangeComp m G (S.TM K)) z)) := by
    filter_upwards [hadd, h0, hdiv, hrc] with z a b d r
    rw [b]
    exact (d.add (r.comp hκ.tendsto_atTop)).congr (fun j => (a j).symm)
  filter_upwards [S.ae_of_ae_coordE hz] with x hx
  refine S.tendsto_ramerJac _ _ x ?_ ?_ hx
  · have h1 := (S.tendsto_projField_apply K x).comp hκ.tendsto_atTop
    have h2 := ((S.headProj m).continuous.tendsto _).comp
      ((hG.continuous.tendsto _).comp ((S.tendsto_TM_projField K x).comp hκ.tendsto_atTop))
    exact h1.add h2
  · have e : ∀ j, S.hsDerivH
        (S.projField (κ j) K + S.rangeComp m G (S.TM (S.projField (κ j) K))) x =
        S.hsDerivH (S.projField (κ j) K) x +
          S.hsDerivH (S.rangeComp m G (S.TM (S.projField (κ j) K))) x :=
      fun j => S.hsDerivH_add _ _ (dKk _) (dRc _) x
    show Tendsto (fun j => S.hsDerivH
        (S.projField (κ j) K + S.rangeComp m G (S.TM (S.projField (κ j) K))) x) atTop
      (𝓝 (S.hsDerivH (K + S.rangeComp m G (S.TM K)) x))
    simp only [e, S.hsDerivH_add K _ dK dRcK x]
    exact ((S.tendsto_hsDerivH_projField K dK x).comp hκ.tendsto_atTop).add
      ((S.tendsto_hsDerivH_rangeComp m G K (hG.of_le (by norm_num)) (hK.of_le (by norm_num)) x).comp
        hκ.tendsto_atTop)

/-- Step 3, continuity of `J^{I + P_m G}` along `T_k x → T x` (a.e. on `U`). -/
theorem tendsto_ramerJac_headG_ae (m : ℕ)
    (G K : S.E → S.H) (hG : ContDiff ℝ 2 G)
    (κ : ℕ → ℕ) (hκ : StrictMono κ) (U : Set (S.E))
    (hT : ∀ N : Set (S.E),
      S.γE N = 0 →
      S.γE (U ∩ S.TM K ⁻¹' N) = 0)
    (hTk : ∀ k : ℕ, ∀ N : Set (S.E),
      S.γE N = 0 →
      S.γE (U ∩ S.TM (S.projField k K) ⁻¹' N) = 0) :
    ∀ᵐ x ∂(S.γE), x ∈ U →
      Tendsto (fun j => S.ramerJac (S.projField m G) (S.TM (S.projField (κ j) K) x)) atTop
        (𝓝 (S.ramerJac (S.projField m G) (S.TM K x))) := by
  have hGm : ContDiff ℝ 2 (S.projField m G) := S.contDiff_projField m G hG
  have hae := S.ramerDiv_coordE_ae_eq (S.projField m G) hGm (fun x => S.headProj_idem _ _)
  have a0 := NlsGge.Ramer.Gen.ae_on_comp hT hae
  have ak : ∀ᵐ x ∂(S.γE), ∀ k : ℕ, x ∈ U →
      S.ramerDiv (S.projField m G) (S.coordE (S.TM (S.projField k K) x)) =
        S.ramerA m (S.projField m G)
          (S.coordE (S.TM (S.projField k K) x)) :=
    ae_all_iff.2 fun k => NlsGge.Ramer.Gen.ae_on_comp (hTk k) hae
  filter_upwards [a0, ak] with x h0 hk hxU
  have key : ∀ y, S.ramerDiv (S.projField m G) (S.coordE y) =
      S.ramerA m (S.projField m G) (S.coordE y) →
      S.ramerJac (S.projField m G) y =
        S.ramerJE (S.projField m G) (S.ramerA m (S.projField m G)) y :=
    fun y hy => by rw [S.ramerJac_eq, S.ramerJE_eq, hy]
  rw [key _ (h0 hxU)]
  exact (((S.continuous_ramerJE_ramerA m _ (hGm.of_le (by norm_num))).tendsto _).comp
    ((S.tendsto_TM_projField K x).comp hκ.tendsto_atTop)).congr
    (fun j => (key _ (hk (κ j) hxU)).symm)

/-- Local form of R9a's product formula: the null-set hypothesis is only needed on `U`. -/
theorem ramerJac_compField_ae_on {m : ℕ}
    (M₁ M₂ : S.E → S.H)
    (h₁ : ContDiff ℝ 2 M₁) (h₂ : ContDiff ℝ 2 M₂)
    (hm₁ : ∀ x, S.headProj m (M₁ x) = M₁ x) (hm₂ : ∀ x, S.headProj m (M₂ x) = M₂ x)
    (U : Set (S.E))
    (hnull : ∀ N : Set (S.E),
      S.γE N = 0 →
      S.γE (U ∩ S.TM M₁ ⁻¹' N) = 0) :
    ∀ᵐ x ∂(S.γE), x ∈ U →
      S.ramerJac (S.compField M₁ M₂) x =
        S.ramerJac M₂ (S.TM M₁ x) * S.ramerJac M₁ x := by
  have h12 := S.contDiff_compField M₁ M₂ h₁ h₂
  have hm12 := S.headProj_compField M₁ M₂ hm₁ hm₂
  have a12 := S.ramerDiv_coordE_ae_eq _ h12 hm12
  have a1 := S.ramerDiv_coordE_ae_eq _ h₁ hm₁
  have a2 := NlsGge.Ramer.Gen.ae_on_comp hnull (S.ramerDiv_coordE_ae_eq _ h₂ hm₂)
  filter_upwards [a12, a1, a2] with x x12 x1 x2 hxU
  have := S.ramerJE_compField M₁ M₂ (h₁.of_le (by norm_num)) (h₂.of_le (by norm_num))
    hm₁ hm₂ x
  rw [ramerJac, ramerJac, ramerJac, S.ramerJE_eq, S.ramerJE_eq, S.ramerJE_eq, x12, x1, x2 hxU]
  rw [S.ramerJE_eq, S.ramerJE_eq, S.ramerJE_eq] at this
  exact this

/-- Step 3 (assembled): the product formula for `K + P_m G ∘ T`, for every `m`. -/
theorem ramerJac_compField_proj_ae (m : ℕ)
    (G K : S.E → S.H) (hG : ContDiff ℝ 2 G) (hK : ContDiff ℝ 2 K)
    (U : Set (S.E))
    (hT : ∀ N : Set (S.E),
      S.γE N = 0 →
      S.γE (U ∩ S.TM K ⁻¹' N) = 0)
    (hTk : ∀ k : ℕ, ∀ N : Set (S.E),
      S.γE N = 0 →
      S.γE (U ∩ S.TM (S.projField k K) ⁻¹' N) = 0) :
    ∀ᵐ x ∂(S.γE), x ∈ U →
      S.ramerJac (S.compField K (S.projField m G)) x =
        S.ramerJac (S.projField m G) (S.TM K x) * S.ramerJac K x := by
  obtain ⟨κ, hκ, hdiv⟩ := S.ramerDiv_projField_subseq K hK
  have hdiv' : ∀ᵐ z ∂(S.γ),
      Tendsto (fun j => S.ramerDiv (S.projField (κ j) K) z) atTop
        (𝓝 (S.ramerDiv K z)) := hdiv.mono fun z h => h.2
  have A := S.tendsto_ramerJac_compField_proj m G K hG hK κ hκ hdiv'
  have D := S.tendsto_ramerJac_projField_ae K hK κ hκ hdiv'
  have C := S.tendsto_ramerJac_headG_ae m G K hG κ hκ U hT hTk
  have B : ∀ᵐ x ∂(S.γE), ∀ j, x ∈ U →
      S.ramerJac (S.compField (S.projField (κ j) K) (S.projField m G)) x =
        S.ramerJac (S.projField m G) (S.TM (S.projField (κ j) K) x) *
          S.ramerJac (S.projField (κ j) K) x := by
    refine ae_all_iff.2 fun j => ?_
    exact S.ramerJac_compField_ae_on (m := max (κ j) m) (S.projField (κ j) K) (S.projField m G)
      (S.contDiff_projField _ K hK) (S.contDiff_projField _ G hG)
      (fun x => S.headProj_projField_of_le (le_max_left _ _) K x)
      (fun x => S.headProj_projField_of_le (le_max_right _ _) G x) U (hTk (κ j))
  filter_upwards [A, D, C, B] with x hA hD hC hB hxU
  have lim2 := (hC hxU).mul hD
  exact tendsto_nhds_unique hA (lim2.congr (fun j => (hB j hxU).symm))

/-- **Ramer Lemma 5.4, local form (Step 9).**
For `U` open, `K`, `G` globally `C²`, `T = I + iK`: if `T` preserves `γ_E`-null sets on `U` and so does
each truncation `I + iP_kK` (explicit hypotheses `hT`, `hTk`), then for `γ_E`-a.e. `x ∈ U`,
`J^{K + G∘T}(x) = J^G(Tx) · J^K(x)`. -/
theorem ramer_lemma_5_4 (U : Set (S.E))
    (_hU : IsOpen U) (K G : S.E → S.H)
    (hK : ContDiff ℝ 2 K) (hG : ContDiff ℝ 2 G)
    (hT : ∀ N : Set (S.E),
      S.γE N = 0 →
      S.γE (U ∩ S.TM K ⁻¹' N) = 0)
    (hTk : ∀ k : ℕ, ∀ N : Set (S.E),
      S.γE N = 0 →
      S.γE (U ∩ S.TM (S.projField k K) ⁻¹' N) = 0) :
    ∀ᵐ x ∂(S.γE), x ∈ U →
      S.ramerJac (K + G ∘ S.TM K) x =
        S.ramerJac G (S.TM K x) * S.ramerJac K x := by
  have hF : ContDiff ℝ 2 (fun y => G (S.TM K y)) :=
    hG.comp (S.contDiff_TM K hK)
  obtain ⟨φ, hφ, hdiv⟩ := S.exists_common_subseq G (fun y => G (S.TM K y)) hG hF
  have S1 := S.tendsto_ramerJac_projField_ae G hG φ hφ (hdiv.mono fun z h => h.1)
  have S1' := NlsGge.Ramer.Gen.ae_on_comp hT S1
  have S4 := S.tendsto_ramerJac_add_projField K (fun y => G (S.TM K y)) hK hF φ hφ
    (hdiv.mono fun z h => h.2)
  have E1 : ∀ᵐ x ∂(S.γE), ∀ m : ℕ, x ∈ U →
      S.ramerJac (S.compField K (S.projField m G)) x =
        S.ramerJac (S.projField m G) (S.TM K x) * S.ramerJac K x :=
    ae_all_iff.2 fun m => S.ramerJac_compField_proj_ae m G K hG hK U hT hTk
  filter_upwards [S1', S4, E1] with x s1 s4 e1 hxU
  have lim := (s1 hxU).mul_const (S.ramerJac K x)
  exact tendsto_nhds_unique s4 (lim.congr (fun j => (e1 (φ j) hxU).symm))

/-! ### Corollaries -/

theorem ramerA_eq_zero_of_eqOn (n : ℕ)
    (M : S.E → S.H) (U : Set (S.E))
    (hU : IsOpen U) (hM : ∀ x ∈ U, M x = 0) (x : S.E) (hx : x ∈ U) :
    S.ramerA n M (S.coordE x) = 0 := by
  have hev : M =ᶠ[𝓝 x] fun _ => 0 :=
    Filter.mem_of_superset (hU.mem_nhds hx) (fun y hy => hM y hy)
  have hD : fderiv ℝ M x = 0 := by rw [hev.fderiv_eq]; simp
  have hz : ∀ b : S.H, ⟪b, (0 : S.H)⟫ = 0 := fun b => inner_zero_right b
  rw [S.ramerA_eq, S.realization_coordE]
  unfold NlsGge.Ramer.General.RamerSetting.ramerSum
  simp [hM x hx, hD, hz]

/-- A `C²` field vanishing on an open set `U` has Jacobian `1` a.e. on `U`. -/
theorem ramerJac_eq_one_of_eqOn_zero (M : S.E → S.H) (hM : ContDiff ℝ 2 M)
    (U : Set (S.E)) (hU : IsOpen U) (h0 : ∀ x ∈ U, M x = 0) :
    ∀ᵐ x ∂(S.γE), x ∈ U →
      S.ramerJac M x = 1 := by
  obtain ⟨φ, -, hlim⟩ := (S.ramerDiv_spec M hM).2.1
  filter_upwards [S.ae_of_ae_coordE hlim] with x hx hxU
  have hdiv : S.ramerDiv M (S.coordE x) = 0 := by
    have : Tendsto (fun j => S.ramerA (φ j) M (S.coordE x)) atTop
        (𝓝 0) :=
      tendsto_const_nhds.congr (fun j => (S.ramerA_eq_zero_of_eqOn (φ j) M U hU h0 x hxU).symm)
    exact tendsto_nhds_unique hx this
  have hev : M =ᶠ[𝓝 x] fun _ => 0 :=
    Filter.mem_of_superset (hU.mem_nhds hxU) (fun y hy => h0 y hy)
  rw [S.ramerJac_eq, hdiv, S.hsDerivH_eq_zero_of_eventuallyEq M x hev, h0 x hxU]
  simp

/-- **Corollary (a)** (Ramer Step 10): if `G ∘ T = -K` on `U`, then
`J^G(Tx) · J^K(x) = 1` a.e. on `U`. -/
theorem ramerJac_comp_mul_eq_one (U : Set (S.E))
    (hU : IsOpen U) (K G : S.E → S.H)
    (hK : ContDiff ℝ 2 K) (hG : ContDiff ℝ 2 G)
    (hT : ∀ N : Set (S.E),
      S.γE N = 0 →
      S.γE (U ∩ S.TM K ⁻¹' N) = 0)
    (hTk : ∀ k : ℕ, ∀ N : Set (S.E),
      S.γE N = 0 →
      S.γE (U ∩ S.TM (S.projField k K) ⁻¹' N) = 0)
    (hGT : ∀ x ∈ U, G (S.TM K x) = -K x) :
    ∀ᵐ x ∂(S.γE), x ∈ U →
      S.ramerJac G (S.TM K x) * S.ramerJac K x = 1 := by
  have hF : ContDiff ℝ 2 (K + G ∘ S.TM K) :=
    hK.add (hG.comp (S.contDiff_TM K hK))
  have h1 := S.ramerJac_eq_one_of_eqOn_zero _ hF U hU
    (fun x hx => by simp [hGT x hx])
  filter_upwards [S.ramer_lemma_5_4 U hU K G hK hG hT hTk, h1] with x ha hb hxU
  rw [← ha hxU]
  exact hb hxU

/-- The divergence approximants of a constant field are the finite Cameron–Martin scores. -/
theorem ramerA_const (n : ℕ) (e : S.H) (z : ℤ → ℂ) :
    S.ramerA n (fun _ => e) z =
      ∑ p ∈ basisIndex n,
        ⟪(S.headPt n z : S.H), weightedRealHilbertBasis S.cmWeight p⟫ *
          ⟪weightedRealHilbertBasis S.cmWeight p, e⟫ := by
  have hz : ∀ b : S.H, ⟪b, (0 : S.H)⟫ = 0 := fun b => inner_zero_right b
  unfold ramerA
  simp [hz]

/-- A constant field has Jacobian `exp(-δe - ½‖e‖²)` (`det₂ 0 = 1`), at every point. -/
theorem ramerJac_const (e : S.H) (x : S.E) :
    S.ramerJac (fun _ => e) x =
      Real.exp (-(S.ramerDiv (fun _ => e) (S.coordE x)) - ‖e‖ ^ 2 / 2) := by
  rw [S.ramerJac_eq, S.hsDerivH_const]
  simp

/-- **Corollary (b)**, the translation case: `K ≡ e`, `T x = x + i e`. -/
theorem ramer_translation (U : Set (S.E))
    (hU : IsOpen U) (e : S.H) (G : S.E → S.H)
    (hG : ContDiff ℝ 2 G)
    (hT : ∀ N : Set (S.E),
      S.γE N = 0 →
      S.γE
        (U ∩ (fun y => y + S.incl e) ⁻¹' N) = 0)
    (hTk : ∀ k : ℕ, ∀ N : Set (S.E),
      S.γE N = 0 →
      S.γE
        (U ∩ (fun y => y + S.incl (S.headProj k e)) ⁻¹' N) = 0) :
    ∀ᵐ x ∂(S.γE), x ∈ U →
      S.ramerJac ((fun _ => e) + G ∘ fun y => y + S.incl e) x =
        S.ramerJac G (x + S.incl e) *
          Real.exp (-(S.ramerDiv (fun _ => e) (S.coordE x)) - ‖e‖ ^ 2 / 2) := by
  filter_upwards [S.ramer_lemma_5_4 U hU (fun _ => e) G contDiff_const hG hT hTk] with x hx hxU
  rw [← S.ramerJac_const e x]
  exact hx hxU

end Lemma

end NlsGge.Ramer.General.RamerSetting
