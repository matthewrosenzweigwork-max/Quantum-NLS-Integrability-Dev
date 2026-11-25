import Mathlib
import NlsGge.Ramer.RamerJacobianLimits
import NlsGge.Ramer.RamerStep8Bridge
import NlsGge.Ramer.RamerStep8c
import NlsGge.Ramer.RamerFiniteChainRule

/-!
# R9c: Ramer Lemma 5.4, local form (Step 9)

See `RamerLemma54.md`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal RealInnerProductSpace

namespace NlsGge.Ramer

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant

section Prelim

/-- Null-set transfer through a map that preserves null sets on `U`. -/
theorem ae_on_comp {α : Type*} [MeasurableSpace α] {μ : Measure α} {U : Set α} {T : α → α}
    (hT : ∀ N : Set α, μ N = 0 → μ (U ∩ T ⁻¹' N) = 0) {P : α → Prop}
    (h : ∀ᵐ y ∂μ, P y) : ∀ᵐ x ∂μ, x ∈ U → P (T x) := by
  have h0 : μ {y | ¬ P y} = 0 := ae_iff.1 h
  have := measure_eq_zero_iff_ae_notMem.1 (hT _ h0)
  filter_upwards [this] with x hx hxU
  by_contra hP
  exact hx ⟨hxU, hP⟩

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

theorem headProj_headProj_of_le {k n : ℕ} (hkn : k ≤ n) (w : ActualCM c) :
    headProj c n (headProj c k w) = headProj c k w := by
  apply cmCoord_ext
  intro m
  simp only [headProj_apply, cmCoord_cmTrunc]
  split_ifs with h1 h2 h2 <;>
    first | rfl | exact absurd (symmetricModes_mono hkn h2) h1

variable {c s}

theorem headProj_projField_of_le {k n : ℕ} (hkn : k ≤ n) (M : FullWeightedHilbert c s → ActualCM c)
    (x : FullWeightedHilbert c s) : headProj c n (projField k M x) = projField k M x :=
  headProj_headProj_of_le c hkn _

theorem hsDerivH_apply (hs : (1 : ℝ) / 2 < s) (M : FullWeightedHilbert c s → ActualCM c)
    (x : FullWeightedHilbert c s) (v : ActualCM c) :
    (hsDerivH c s hs M x).toCLM v = fderiv ℝ M x (inclE c s hs v) :=
  congrArg (fun f => f v) (cmFactorHS_toCLM c s hs (fderiv ℝ M x))

theorem hsDerivH_add (hs : (1 : ℝ) / 2 < s) (M₁ M₂ : FullWeightedHilbert c s → ActualCM c)
    (h₁ : Differentiable ℝ M₁) (h₂ : Differentiable ℝ M₂) (x : FullWeightedHilbert c s) :
    hsDerivH c s hs (M₁ + M₂) x = hsDerivH c s hs M₁ x + hsDerivH c s hs M₂ x := by
  apply HilbertSchmidt.ext
  intro v
  have hf : fderiv ℝ (M₁ + M₂) x = fderiv ℝ M₁ x + fderiv ℝ M₂ x := fderiv_add (h₁ x) (h₂ x)
  rw [HilbertSchmidt.toCLM_add, add_apply, hsDerivH_apply, hsDerivH_apply, hsDerivH_apply]
  exact (congrArg (fun D => D (inclE c s hs v)) hf).trans rfl

theorem hsDerivH_const (hs : (1 : ℝ) / 2 < s) (e : ActualCM c) (x : FullWeightedHilbert c s) :
    hsDerivH c s hs (fun _ => e) x = 0 := by
  apply HilbertSchmidt.ext
  intro v
  rw [hsDerivH_apply]
  simp

/-- If `M = 0` near `x` then `hsDerivH M x = 0`. -/
theorem hsDerivH_eq_zero_of_eventuallyEq (hs : (1 : ℝ) / 2 < s)
    (M : FullWeightedHilbert c s → ActualCM c) (x : FullWeightedHilbert c s)
    (h : M =ᶠ[𝓝 x] fun _ => 0) : hsDerivH c s hs M x = 0 := by
  have : fderiv ℝ M x = fderiv ℝ (fun _ : FullWeightedHilbert c s => (0 : ActualCM c)) x :=
    h.fderiv_eq
  apply HilbertSchmidt.ext
  intro v
  rw [hsDerivH_apply, this]
  simp

variable (c s)

/-- `ramerDiv (P_n ∘ M) = ramerA n M` a.e. -/
theorem ramerDiv_projField_ae (hs : (1 : ℝ) / 2 < s) (n : ℕ)
    (M : FullWeightedHilbert c s → ActualCM c) (hM : ContDiff ℝ 2 M) :
    ramerDiv c s hs (projField n M) =ᵐ[NlsGge.Measure.fullWeightSequenceGaussian c.val]
      ramerA c s (zero_le_of_half_lt hs) n M := by
  filter_upwards [ramerDiv_ae_eq_ramerA c s hs (projField n M)
    (contDiff_projField _ M hM) (fun x => headProj_idem _ _)] with z hz
  rw [hz, ramerA_projField _ _ M (hM.differentiable (by norm_num))]

/-- A common subsequence along which the divergences of the projections of two fields converge. -/
theorem exists_common_subseq (hs : (1 : ℝ) / 2 < s) (G F : FullWeightedHilbert c s → ActualCM c)
    (hG : ContDiff ℝ 2 G) (hF : ContDiff ℝ 2 F) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
        Tendsto (fun j => ramerDiv c s hs (projField (φ j) G) z) atTop
          (𝓝 (ramerDiv c s hs G z)) ∧
        Tendsto (fun j => ramerDiv c s hs (projField (φ j) F) z) atTop
          (𝓝 (ramerDiv c s hs F z)) := by
  obtain ⟨ψ, hψ, a1⟩ := (ramerDiv_spec c s hs G hG).2.2.exists_seq_tendsto_ae
  obtain ⟨φ₂, hφ₂, a2⟩ := exists_subseq_ae_of_tendstoInMeasure (ramerDiv_spec c s hs F hF).2.2 hψ
  refine ⟨fun j => ψ (φ₂ j), hψ.comp hφ₂, ?_⟩
  have eG : ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val), ∀ j,
      ramerDiv c s hs (projField (ψ (φ₂ j)) G) z =
        ramerA c s (zero_le_of_half_lt hs) (ψ (φ₂ j)) G z :=
    ae_all_iff.2 fun j => ramerDiv_projField_ae c s hs _ G hG
  have eF : ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val), ∀ j,
      ramerDiv c s hs (projField (ψ (φ₂ j)) F) z =
        ramerA c s (zero_le_of_half_lt hs) (ψ (φ₂ j)) F z :=
    ae_all_iff.2 fun j => ramerDiv_projField_ae c s hs _ F hF
  filter_upwards [a1, a2, eG, eF] with z z1 z2 z3 z4
  refine ⟨?_, ?_⟩
  · exact (z1.comp hφ₂.tendsto_atTop).congr (fun j => (z3 j).symm)
  · exact z2.congr (fun j => (z4 j).symm)

end Prelim

section Conv

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

theorem continuous_ramerA_coordE (hs : (1 : ℝ) / 2 < s) (n : ℕ)
    (M : FullWeightedHilbert c s → ActualCM c) (hM : ContDiff ℝ 1 M) :
    Continuous (fun y => ramerA c s (zero_le_of_half_lt hs) n M (coordE c s y)) := by
  have hD : Continuous (fderiv ℝ M) := hM.continuous_fderiv one_ne_zero
  have hMc : Continuous M := hM.continuous
  have hh : Continuous (fun y => ((headCoord c s n y : actualCMHead c n) : ActualCM c)) :=
    continuous_subtype_val.comp (headCoord c s n).continuous
  simp only [ramerA_eq, realization_coordE]
  unfold ramerSum
  refine continuous_finsetSum _ (fun p _ => ?_)
  exact ((hh.inner continuous_const).mul (continuous_const.inner hMc)).sub
    (continuous_const.inner (hD.clm_apply continuous_const))

theorem continuous_ramerJE_ramerA (hs : (1 : ℝ) / 2 < s) (n : ℕ)
    (M : FullWeightedHilbert c s → ActualCM c) (hM : ContDiff ℝ 1 M) :
    Continuous (ramerJE c s hs M (ramerA c s (zero_le_of_half_lt hs) n M)) := by
  have : ramerJE c s hs M (ramerA c s (zero_le_of_half_lt hs) n M) = fun y =>
      |det2 (hsDerivH c s hs M y)| *
        Real.exp (-(ramerA c s (zero_le_of_half_lt hs) n M (coordE c s y)) - ‖M y‖ ^ 2 / 2) :=
    funext (ramerJE_eq c s hs _ _)
  rw [this]
  exact (continuous_det2_hsDerivH c s hs M hM).abs.mul
    (Real.continuous_exp.comp ((continuous_ramerA_coordE c s hs n M hM).neg.sub
      ((hM.continuous.norm.pow 2).div_const 2)))

variable {c s}

theorem hsDerivH_rangeComp (hs : (1 : ℝ) / 2 < s) (m : ℕ) (G : FullWeightedHilbert c s → ActualCM c)
    (hG : Differentiable ℝ G) (M : FullWeightedHilbert c s → ActualCM c)
    (hM : Differentiable ℝ M) (x : FullWeightedHilbert c s) :
    hsDerivH c s hs (rangeComp m G (TM c s hs M)) x =
      HilbertSchmidt.postcompose (headProj c m)
        (hsDerivH c s hs G (TM c s hs M x) +
          mulHS (hsDerivH c s hs G (TM c s hs M x)) (hsDerivH c s hs M x)) := by
  apply HilbertSchmidt.ext
  intro v
  rw [hsDerivH_apply, fderiv_rangeComp hs m G hG M hM]
  change _ = headProj c m ((hsDerivH c s hs G (TM c s hs M x) +
    mulHS (hsDerivH c s hs G (TM c s hs M x)) (hsDerivH c s hs M x)).toCLM v)
  simp only [HilbertSchmidt.toCLM_add, add_apply, toCLM_mulHS, ContinuousLinearMap.comp_apply,
    hsDerivH_apply, map_add]

variable (c s)

theorem tendsto_TM_projField (hs : (1 : ℝ) / 2 < s) (K : FullWeightedHilbert c s → ActualCM c)
    (y : FullWeightedHilbert c s) :
    Tendsto (fun k : ℕ => TM c s hs (projField k K) y) atTop (𝓝 (TM c s hs K y)) := by
  unfold TM
  exact tendsto_const_nhds.add ((inclE c s hs).continuous.continuousAt.tendsto.comp
    (tendsto_projField_apply c s K y))

theorem tendsto_hsDerivH_rangeComp (hs : (1 : ℝ) / 2 < s) (m : ℕ)
    (G K : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 1 G) (hK : ContDiff ℝ 1 K)
    (x : FullWeightedHilbert c s) :
    Tendsto (fun k : ℕ => hsDerivH c s hs (rangeComp m G (TM c s hs (projField k K))) x) atTop
      (𝓝 (hsDerivH c s hs (rangeComp m G (TM c s hs K)) x)) := by
  have dG := hG.differentiable one_ne_zero
  have dK := hK.differentiable one_ne_zero
  have dKk : ∀ k, Differentiable ℝ (projField k K) := fun k =>
    (contDiff_projField k K hK).differentiable one_ne_zero
  have e : ∀ k : ℕ, hsDerivH c s hs (rangeComp m G (TM c s hs (projField k K))) x =
      HilbertSchmidt.postcompose (headProj c m)
        (hsDerivH c s hs G (TM c s hs (projField k K) x) +
          mulHS (hsDerivH c s hs G (TM c s hs (projField k K) x))
            (hsDerivH c s hs (projField k K) x)) :=
    fun k => hsDerivH_rangeComp hs m G dG _ (dKk k) x
  simp only [e, hsDerivH_rangeComp hs m G dG K dK]
  have hD : Tendsto (fun k : ℕ => hsDerivH c s hs G (TM c s hs (projField k K) x)) atTop
      (𝓝 (hsDerivH c s hs G (TM c s hs K x))) :=
    ((continuous_hsDerivH c s hs G hG).tendsto _).comp (tendsto_TM_projField c s hs K x)
  have hA := tendsto_hsDerivH_projField c s hs K dK x
  have hm := (mulHS.continuous₂.tendsto (hsDerivH c s hs G (TM c s hs K x), hsDerivH c s hs K x)).comp
    (hD.prodMk_nhds hA)
  exact ((HilbertSchmidt.postcomposeContinuous (headProj c m)).continuous.tendsto _).comp
    (hD.add hm)

end Conv

section Lemma

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

/-- Step 2/Step 1: `J^{I+P_{φ j}M} → J^{I+M}` a.e., given convergence of the divergences. -/
theorem tendsto_ramerJac_projField_ae (hs : (1 : ℝ) / 2 < s)
    (M : FullWeightedHilbert c s → ActualCM c) (hM : ContDiff ℝ 2 M) (φ : ℕ → ℕ)
    (hφ : StrictMono φ)
    (hdiv : ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      Tendsto (fun j => ramerDiv c s hs (projField (φ j) M) z) atTop
        (𝓝 (ramerDiv c s hs M z))) :
    ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s),
      Tendsto (fun j => ramerJac c s hs (projField (φ j) M) x) atTop
        (𝓝 (ramerJac c s hs M x)) := by
  filter_upwards [ae_of_ae_coordE c s hs hdiv] with x hx
  exact tendsto_ramerJac c s hs (fun j => projField (φ j) M) M x
    ((tendsto_projField_apply c s M x).comp hφ.tendsto_atTop)
    ((tendsto_hsDerivH_projField c s hs M (hM.differentiable (by norm_num)) x).comp
      hφ.tendsto_atTop) hx

/-- Step 4: `J^{K + P_{φ j} F} → J^{K + F}` a.e. -/
theorem tendsto_ramerJac_add_projField (hs : (1 : ℝ) / 2 < s)
    (K F : FullWeightedHilbert c s → ActualCM c) (hK : ContDiff ℝ 2 K) (hF : ContDiff ℝ 2 F)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hdiv : ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      Tendsto (fun j => ramerDiv c s hs (projField (φ j) F) z) atTop
        (𝓝 (ramerDiv c s hs F z))) :
    ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s),
      Tendsto (fun j => ramerJac c s hs (K + projField (φ j) F) x) atTop
        (𝓝 (ramerJac c s hs (K + F) x)) := by
  have dK : Differentiable ℝ K := hK.differentiable (by norm_num)
  have dF : Differentiable ℝ F := hF.differentiable (by norm_num)
  have dFj : ∀ j, Differentiable ℝ (projField (φ j) F) := fun j =>
    (contDiff_projField _ F hF).differentiable (by norm_num)
  have hadd : ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val), ∀ j,
      ramerDiv c s hs (K + projField (φ j) F) z =
        ramerDiv c s hs K z + ramerDiv c s hs (projField (φ j) F) z := by
    refine ae_all_iff.2 fun j => ?_
    filter_upwards [ramerDiv_add_ae c s hs K (projField (φ j) F) hK
      (contDiff_projField _ F hF)] with z hz
    exact hz
  have h0 : ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      ramerDiv c s hs (K + F) z = ramerDiv c s hs K z + ramerDiv c s hs F z := by
    filter_upwards [ramerDiv_add_ae c s hs K F hK hF] with z hz
    exact hz
  have hz : ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      Tendsto (fun j => ramerDiv c s hs (K + projField (φ j) F) z) atTop
        (𝓝 (ramerDiv c s hs (K + F) z)) := by
    filter_upwards [hadd, h0, hdiv] with z a b d
    rw [b]
    exact (tendsto_const_nhds.add d).congr (fun j => (a j).symm)
  filter_upwards [ae_of_ae_coordE c s hs hz] with x hx
  refine tendsto_ramerJac c s hs _ _ x ?_ ?_ hx
  · exact tendsto_const_nhds.add ((tendsto_projField_apply c s F x).comp hφ.tendsto_atTop)
  · have e : ∀ j, hsDerivH c s hs (K + projField (φ j) F) x =
        hsDerivH c s hs K x + hsDerivH c s hs (projField (φ j) F) x :=
      fun j => hsDerivH_add hs K _ dK (dFj j) x
    simp only [e, hsDerivH_add hs K F dK dF x]
    exact tendsto_const_nhds.add
      ((tendsto_hsDerivH_projField c s hs F dF x).comp hφ.tendsto_atTop)

/-- Step 3 (convergence in `k`): for fixed `m`, `J^{K_k + P_m G ∘ (I + iK_k)} → J^{K + P_m G ∘ (I+iK)}`. -/
theorem tendsto_ramerJac_compField_proj (hs : (1 : ℝ) / 2 < s) (m : ℕ)
    (G K : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 2 G) (hK : ContDiff ℝ 2 K)
    (κ : ℕ → ℕ) (hκ : StrictMono κ)
    (hdiv : ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      Tendsto (fun j => ramerDiv c s hs (projField (κ j) K) z) atTop
        (𝓝 (ramerDiv c s hs K z))) :
    ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s),
      Tendsto (fun j => ramerJac c s hs
          (compField c s hs (projField (κ j) K) (projField m G)) x) atTop
        (𝓝 (ramerJac c s hs (compField c s hs K (projField m G)) x)) := by
  have dK : Differentiable ℝ K := hK.differentiable (by norm_num)
  have dKk : ∀ k, Differentiable ℝ (projField k K) := fun k =>
    (contDiff_projField k K hK).differentiable (by norm_num)
  have hRc : ∀ k : ℕ, ContDiff ℝ 2 (rangeComp m G (TM c s hs (projField k K))) := fun k =>
    contDiff_rangeComp hs m G _ hG (contDiff_projField k K hK)
  have hRcK : ContDiff ℝ 2 (rangeComp m G (TM c s hs K)) := contDiff_rangeComp hs m G K hG hK
  have dRc : ∀ k : ℕ, Differentiable ℝ (rangeComp m G (TM c s hs (projField k K))) := fun k =>
    (hRc k).differentiable (by norm_num)
  have dRcK : Differentiable ℝ (rangeComp m G (TM c s hs K)) := hRcK.differentiable (by norm_num)
  have hadd : ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val), ∀ j,
      ramerDiv c s hs (projField (κ j) K + rangeComp m G (TM c s hs (projField (κ j) K))) z =
        ramerDiv c s hs (projField (κ j) K) z +
          ramerDiv c s hs (rangeComp m G (TM c s hs (projField (κ j) K))) z := by
    refine ae_all_iff.2 fun j => ?_
    filter_upwards [ramerDiv_add_ae c s hs _ _ (contDiff_projField (κ j) K hK) (hRc (κ j))]
      with z hz
    exact hz
  have h0 : ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      ramerDiv c s hs (K + rangeComp m G (TM c s hs K)) z =
        ramerDiv c s hs K z + ramerDiv c s hs (rangeComp m G (TM c s hs K)) z := by
    filter_upwards [ramerDiv_add_ae c s hs K _ hK hRcK] with z hz
    exact hz
  have hrc := ramerDiv_rangeComp_tendsto_ae c s hs m G K hG hK
  have hz : ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      Tendsto (fun j => ramerDiv c s hs
          (projField (κ j) K + rangeComp m G (TM c s hs (projField (κ j) K))) z) atTop
        (𝓝 (ramerDiv c s hs (K + rangeComp m G (TM c s hs K)) z)) := by
    filter_upwards [hadd, h0, hdiv, hrc] with z a b d r
    rw [b]
    exact (d.add (r.comp hκ.tendsto_atTop)).congr (fun j => (a j).symm)
  filter_upwards [ae_of_ae_coordE c s hs hz] with x hx
  refine tendsto_ramerJac c s hs _ _ x ?_ ?_ hx
  · have h1 := (tendsto_projField_apply c s K x).comp hκ.tendsto_atTop
    have h2 := ((headProj c m).continuous.tendsto _).comp
      ((hG.continuous.tendsto _).comp ((tendsto_TM_projField c s hs K x).comp hκ.tendsto_atTop))
    exact h1.add h2
  · have e : ∀ j, hsDerivH c s hs
        (projField (κ j) K + rangeComp m G (TM c s hs (projField (κ j) K))) x =
        hsDerivH c s hs (projField (κ j) K) x +
          hsDerivH c s hs (rangeComp m G (TM c s hs (projField (κ j) K))) x :=
      fun j => hsDerivH_add hs _ _ (dKk _) (dRc _) x
    show Tendsto (fun j => hsDerivH c s hs
        (projField (κ j) K + rangeComp m G (TM c s hs (projField (κ j) K))) x) atTop
      (𝓝 (hsDerivH c s hs (K + rangeComp m G (TM c s hs K)) x))
    simp only [e, hsDerivH_add hs K _ dK dRcK x]
    exact ((tendsto_hsDerivH_projField c s hs K dK x).comp hκ.tendsto_atTop).add
      ((tendsto_hsDerivH_rangeComp c s hs m G K (hG.of_le (by norm_num)) (hK.of_le (by norm_num)) x).comp
        hκ.tendsto_atTop)

/-- Step 3, continuity of `J^{I + P_m G}` along `T_k x → T x` (a.e. on `U`). -/
theorem tendsto_ramerJac_headG_ae (hs : (1 : ℝ) / 2 < s) (m : ℕ)
    (G K : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 2 G)
    (κ : ℕ → ℕ) (hκ : StrictMono κ) (U : Set (FullWeightedHilbert c s))
    (hT : ∀ N : Set (FullWeightedHilbert c s),
      NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s (U ∩ TM c s hs K ⁻¹' N) = 0)
    (hTk : ∀ k : ℕ, ∀ N : Set (FullWeightedHilbert c s),
      NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s (U ∩ TM c s hs (projField k K) ⁻¹' N) = 0) :
    ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s), x ∈ U →
      Tendsto (fun j => ramerJac c s hs (projField m G) (TM c s hs (projField (κ j) K) x)) atTop
        (𝓝 (ramerJac c s hs (projField m G) (TM c s hs K x))) := by
  have hGm : ContDiff ℝ 2 (projField m G) := contDiff_projField m G hG
  have hae := ramerDiv_coordE_ae_eq c s hs (projField m G) hGm (fun x => headProj_idem _ _)
  have a0 := ae_on_comp hT hae
  have ak : ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s), ∀ k : ℕ, x ∈ U →
      ramerDiv c s hs (projField m G) (coordE c s (TM c s hs (projField k K) x)) =
        ramerA c s (zero_le_of_half_lt hs) m (projField m G)
          (coordE c s (TM c s hs (projField k K) x)) :=
    ae_all_iff.2 fun k => ae_on_comp (hTk k) hae
  filter_upwards [a0, ak] with x h0 hk hxU
  have key : ∀ y, ramerDiv c s hs (projField m G) (coordE c s y) =
      ramerA c s (zero_le_of_half_lt hs) m (projField m G) (coordE c s y) →
      ramerJac c s hs (projField m G) y =
        ramerJE c s hs (projField m G) (ramerA c s (zero_le_of_half_lt hs) m (projField m G)) y :=
    fun y hy => by rw [ramerJac_eq, ramerJE_eq, hy]
  rw [key _ (h0 hxU)]
  exact (((continuous_ramerJE_ramerA c s hs m _ (hGm.of_le (by norm_num))).tendsto _).comp
    ((tendsto_TM_projField c s hs K x).comp hκ.tendsto_atTop)).congr
    (fun j => (key _ (hk (κ j) hxU)).symm)

variable {c s}

/-- Local form of R9a's product formula: the null-set hypothesis is only needed on `U`. -/
theorem ramerJac_compField_ae_on (hs : (1 : ℝ) / 2 < s) {m : ℕ}
    (M₁ M₂ : FullWeightedHilbert c s → ActualCM c)
    (h₁ : ContDiff ℝ 2 M₁) (h₂ : ContDiff ℝ 2 M₂)
    (hm₁ : ∀ x, headProj c m (M₁ x) = M₁ x) (hm₂ : ∀ x, headProj c m (M₂ x) = M₂ x)
    (U : Set (FullWeightedHilbert c s))
    (hnull : ∀ N : Set (FullWeightedHilbert c s),
      NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s (U ∩ TM c s hs M₁ ⁻¹' N) = 0) :
    ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s), x ∈ U →
      ramerJac c s hs (compField c s hs M₁ M₂) x =
        ramerJac c s hs M₂ (TM c s hs M₁ x) * ramerJac c s hs M₁ x := by
  have h12 := contDiff_compField c s hs M₁ M₂ h₁ h₂
  have hm12 := headProj_compField c s hs M₁ M₂ hm₁ hm₂
  have a12 := ramerDiv_coordE_ae_eq c s hs _ h12 hm12
  have a1 := ramerDiv_coordE_ae_eq c s hs _ h₁ hm₁
  have a2 := ae_on_comp hnull (ramerDiv_coordE_ae_eq c s hs _ h₂ hm₂)
  filter_upwards [a12, a1, a2] with x x12 x1 x2 hxU
  have := ramerJE_compField c s hs M₁ M₂ (h₁.of_le (by norm_num)) (h₂.of_le (by norm_num))
    hm₁ hm₂ x
  rw [ramerJac, ramerJac, ramerJac, ramerJE_eq, ramerJE_eq, ramerJE_eq, x12, x1, x2 hxU]
  rw [ramerJE_eq, ramerJE_eq, ramerJE_eq] at this
  exact this

variable (c s)

/-- Step 3 (assembled): the product formula for `K + P_m G ∘ T`, for every `m`. -/
theorem ramerJac_compField_proj_ae (hs : (1 : ℝ) / 2 < s) (m : ℕ)
    (G K : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 2 G) (hK : ContDiff ℝ 2 K)
    (U : Set (FullWeightedHilbert c s))
    (hT : ∀ N : Set (FullWeightedHilbert c s),
      NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s (U ∩ TM c s hs K ⁻¹' N) = 0)
    (hTk : ∀ k : ℕ, ∀ N : Set (FullWeightedHilbert c s),
      NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s (U ∩ TM c s hs (projField k K) ⁻¹' N) = 0) :
    ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s), x ∈ U →
      ramerJac c s hs (compField c s hs K (projField m G)) x =
        ramerJac c s hs (projField m G) (TM c s hs K x) * ramerJac c s hs K x := by
  obtain ⟨κ, hκ, hdiv⟩ := ramerDiv_projField_subseq c s hs K hK
  have hdiv' : ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      Tendsto (fun j => ramerDiv c s hs (projField (κ j) K) z) atTop
        (𝓝 (ramerDiv c s hs K z)) := hdiv.mono fun z h => h.2
  have A := tendsto_ramerJac_compField_proj c s hs m G K hG hK κ hκ hdiv'
  have D := tendsto_ramerJac_projField_ae c s hs K hK κ hκ hdiv'
  have C := tendsto_ramerJac_headG_ae c s hs m G K hG κ hκ U hT hTk
  have B : ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s), ∀ j, x ∈ U →
      ramerJac c s hs (compField c s hs (projField (κ j) K) (projField m G)) x =
        ramerJac c s hs (projField m G) (TM c s hs (projField (κ j) K) x) *
          ramerJac c s hs (projField (κ j) K) x := by
    refine ae_all_iff.2 fun j => ?_
    exact ramerJac_compField_ae_on hs (m := max (κ j) m) (projField (κ j) K) (projField m G)
      (contDiff_projField _ K hK) (contDiff_projField _ G hG)
      (fun x => headProj_projField_of_le (le_max_left _ _) K x)
      (fun x => headProj_projField_of_le (le_max_right _ _) G x) U (hTk (κ j))
  filter_upwards [A, D, C, B] with x hA hD hC hB hxU
  have lim2 := (hC hxU).mul hD
  exact tendsto_nhds_unique hA (lim2.congr (fun j => (hB j hxU).symm))

/-- **Ramer Lemma 5.4, local form (Step 9).**
For `U` open, `K`, `G` globally `C²`, `T = I + iK`: if `T` preserves `γ_E`-null sets on `U` and so does
each truncation `I + iP_kK` (explicit hypotheses `hT`, `hTk`), then for `γ_E`-a.e. `x ∈ U`,
`J^{K + G∘T}(x) = J^G(Tx) · J^K(x)`. -/
theorem ramer_lemma_5_4 (hs : (1 : ℝ) / 2 < s) (U : Set (FullWeightedHilbert c s))
    (_hU : IsOpen U) (K G : FullWeightedHilbert c s → ActualCM c)
    (hK : ContDiff ℝ 2 K) (hG : ContDiff ℝ 2 G)
    (hT : ∀ N : Set (FullWeightedHilbert c s),
      NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s (U ∩ TM c s hs K ⁻¹' N) = 0)
    (hTk : ∀ k : ℕ, ∀ N : Set (FullWeightedHilbert c s),
      NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s (U ∩ TM c s hs (projField k K) ⁻¹' N) = 0) :
    ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s), x ∈ U →
      ramerJac c s hs (K + G ∘ TM c s hs K) x =
        ramerJac c s hs G (TM c s hs K x) * ramerJac c s hs K x := by
  have hF : ContDiff ℝ 2 (fun y => G (TM c s hs K y)) :=
    hG.comp (contDiff_TM c s hs K hK)
  obtain ⟨φ, hφ, hdiv⟩ := exists_common_subseq c s hs G (fun y => G (TM c s hs K y)) hG hF
  have S1 := tendsto_ramerJac_projField_ae c s hs G hG φ hφ (hdiv.mono fun z h => h.1)
  have S1' := ae_on_comp hT S1
  have S4 := tendsto_ramerJac_add_projField c s hs K (fun y => G (TM c s hs K y)) hK hF φ hφ
    (hdiv.mono fun z h => h.2)
  have E1 : ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s), ∀ m : ℕ, x ∈ U →
      ramerJac c s hs (compField c s hs K (projField m G)) x =
        ramerJac c s hs (projField m G) (TM c s hs K x) * ramerJac c s hs K x :=
    ae_all_iff.2 fun m => ramerJac_compField_proj_ae c s hs m G K hG hK U hT hTk
  filter_upwards [S1', S4, E1] with x s1 s4 e1 hxU
  have lim := (s1 hxU).mul_const (ramerJac c s hs K x)
  exact tendsto_nhds_unique s4 (lim.congr (fun j => (e1 (φ j) hxU).symm))

/-! ### Corollaries -/

variable {c s}

theorem ramerA_eq_zero_of_eqOn (hs : (1 : ℝ) / 2 < s) (n : ℕ)
    (M : FullWeightedHilbert c s → ActualCM c) (U : Set (FullWeightedHilbert c s))
    (hU : IsOpen U) (hM : ∀ x ∈ U, M x = 0) (x : FullWeightedHilbert c s) (hx : x ∈ U) :
    ramerA c s (zero_le_of_half_lt hs) n M (coordE c s x) = 0 := by
  have hev : M =ᶠ[𝓝 x] fun _ => 0 :=
    Filter.mem_of_superset (hU.mem_nhds hx) (fun y hy => hM y hy)
  have hD : fderiv ℝ M x = 0 := by rw [hev.fderiv_eq]; simp
  have hz : ∀ b : ActualCM c, ⟪b, (0 : ActualCM c)⟫ = 0 := fun b => inner_zero_right b
  rw [ramerA_eq, realization_coordE]
  unfold ramerSum
  simp [hM x hx, hD, hz]

/-- A `C²` field vanishing on an open set `U` has Jacobian `1` a.e. on `U`. -/
theorem ramerJac_eq_one_of_eqOn_zero (hs : (1 : ℝ) / 2 < s)
    (M : FullWeightedHilbert c s → ActualCM c) (hM : ContDiff ℝ 2 M)
    (U : Set (FullWeightedHilbert c s)) (hU : IsOpen U) (h0 : ∀ x ∈ U, M x = 0) :
    ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s), x ∈ U →
      ramerJac c s hs M x = 1 := by
  obtain ⟨φ, -, hlim⟩ := (ramerDiv_spec c s hs M hM).2.1
  filter_upwards [ae_of_ae_coordE c s hs hlim] with x hx hxU
  have hdiv : ramerDiv c s hs M (coordE c s x) = 0 := by
    have : Tendsto (fun j => ramerA c s (zero_le_of_half_lt hs) (φ j) M (coordE c s x)) atTop
        (𝓝 0) :=
      tendsto_const_nhds.congr (fun j => (ramerA_eq_zero_of_eqOn hs (φ j) M U hU h0 x hxU).symm)
    exact tendsto_nhds_unique hx this
  have hev : M =ᶠ[𝓝 x] fun _ => 0 :=
    Filter.mem_of_superset (hU.mem_nhds hxU) (fun y hy => h0 y hy)
  rw [ramerJac_eq, hdiv, hsDerivH_eq_zero_of_eventuallyEq hs M x hev, h0 x hxU]
  simp

/-- **Corollary (a)** (Ramer Step 10): if `G ∘ T = -K` on `U`, then
`J^G(Tx) · J^K(x) = 1` a.e. on `U`. -/
theorem ramerJac_comp_mul_eq_one (hs : (1 : ℝ) / 2 < s) (U : Set (FullWeightedHilbert c s))
    (hU : IsOpen U) (K G : FullWeightedHilbert c s → ActualCM c)
    (hK : ContDiff ℝ 2 K) (hG : ContDiff ℝ 2 G)
    (hT : ∀ N : Set (FullWeightedHilbert c s),
      NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s (U ∩ TM c s hs K ⁻¹' N) = 0)
    (hTk : ∀ k : ℕ, ∀ N : Set (FullWeightedHilbert c s),
      NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s (U ∩ TM c s hs (projField k K) ⁻¹' N) = 0)
    (hGT : ∀ x ∈ U, G (TM c s hs K x) = -K x) :
    ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s), x ∈ U →
      ramerJac c s hs G (TM c s hs K x) * ramerJac c s hs K x = 1 := by
  have hF : ContDiff ℝ 2 (K + G ∘ TM c s hs K) :=
    hK.add (hG.comp (contDiff_TM c s hs K hK))
  have h1 := ramerJac_eq_one_of_eqOn_zero hs _ hF U hU
    (fun x hx => by simp [hGT x hx])
  filter_upwards [ramer_lemma_5_4 c s hs U hU K G hK hG hT hTk, h1] with x ha hb hxU
  rw [← ha hxU]
  exact hb hxU

/-- The divergence approximants of a constant field are the finite Cameron–Martin scores. -/
theorem ramerA_const (hs : (1 : ℝ) / 2 < s) (n : ℕ) (e : ActualCM c) (z : ℤ → ℂ) :
    ramerA c s (zero_le_of_half_lt hs) n (fun _ => e) z =
      ∑ p ∈ basisIndex n,
        ⟪(headPt c n z : ActualCM c), weightedRealHilbertBasis (cmModeWeight c) p⟫ *
          ⟪weightedRealHilbertBasis (cmModeWeight c) p, e⟫ := by
  have hz : ∀ b : ActualCM c, ⟪b, (0 : ActualCM c)⟫ = 0 := fun b => inner_zero_right b
  unfold ramerA
  simp [hz]

/-- A constant field has Jacobian `exp(-δe - ½‖e‖²)` (`det₂ 0 = 1`), at every point. -/
theorem ramerJac_const (hs : (1 : ℝ) / 2 < s) (e : ActualCM c) (x : FullWeightedHilbert c s) :
    ramerJac c s hs (fun _ => e) x =
      Real.exp (-(ramerDiv c s hs (fun _ => e) (coordE c s x)) - ‖e‖ ^ 2 / 2) := by
  rw [ramerJac_eq, hsDerivH_const]
  simp

/-- **Corollary (b)**, the translation case: `K ≡ e`, `T x = x + i e`. -/
theorem ramer_translation (hs : (1 : ℝ) / 2 < s) (U : Set (FullWeightedHilbert c s))
    (hU : IsOpen U) (e : ActualCM c) (G : FullWeightedHilbert c s → ActualCM c)
    (hG : ContDiff ℝ 2 G)
    (hT : ∀ N : Set (FullWeightedHilbert c s),
      NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s
        (U ∩ (fun y => y + inclE c s hs e) ⁻¹' N) = 0)
    (hTk : ∀ k : ℕ, ∀ N : Set (FullWeightedHilbert c s),
      NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s
        (U ∩ (fun y => y + inclE c s hs (headProj c k e)) ⁻¹' N) = 0) :
    ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s), x ∈ U →
      ramerJac c s hs ((fun _ => e) + G ∘ fun y => y + inclE c s hs e) x =
        ramerJac c s hs G (x + inclE c s hs e) *
          Real.exp (-(ramerDiv c s hs (fun _ => e) (coordE c s x)) - ‖e‖ ^ 2 / 2) := by
  filter_upwards [ramer_lemma_5_4 c s hs U hU (fun _ => e) G contDiff_const hG hT hTk] with x hx hxU
  rw [← ramerJac_const hs e x]
  exact hx hxU

end Lemma

end NlsGge.Ramer
