import Mathlib
import NlsGge.Atomic.G1.G1062
import NlsGge.Atomic.G1.G1089
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport
import NlsGge.GK38.MolnarLocalizationC
import NlsGge.Analysis.PhysicalH1Bounds
import NlsGge.Atomic.G1.G1088
import NlsGge.GK38.PoissonMixedRealKappaDerivative
import NlsGge.Analysis.RegularizedDeterminant.RealHilbertSchmidt
import NlsGge.GK38.PoissonDirichletCommute
import NlsGge.GK38.GradEigenRealDirichlet

/- CORRECTED TARGET (owner deferred to root 2026-10-30; literal v2 statement false as printed).
   G1-091: Hilbert-Schmidt property of earlyDerivative u - earlyDerivative 0 and of its adjoint, for u in H^1.
   Authors: proof development (steps 0-1: definitions, differentiability, adjoint reduction), proof development (step 3a: row-wise
   Grebert-Kappeler section 10.8 proof via G1-088 and G1-062). Route differs from v2 lem:determinants; see G1091_3A_PLAN01.md. -/

/- G1-091 (corrected target) STEP 0/1, proof development AUTHOR; not reviewed.  Hosts defs3 design definitions verbatim
   (earlyCoordinates, normingDirichletMap, earlyDerivative, earlyDerivativeRemainder) in namespace
   NlsGge.GKDefinitionDesign; proves: Lib.L2Z is lp (fun _ : ℤ => ℂ) 2 (Step 0), normingDirichletMap = iota o (Kap,Mu),
   analyticity/differentiability everywhere, vacuum subtraction, and the adjoint reduction. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonMixed38
open NlsGge.GK38.PoissonDirichlet38 NlsGge.GK38.PoissonSpectral38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def earlyCoordinates (u : PhysicalL2) (n : ℤ) : ℂ :=
  (realKappa38 u n : ℂ) + Complex.I * ((gkMu u n - n * Real.pi : ℝ) : ℂ)

open Classical in
def normingDirichletMap (u : PhysicalL2) : Lib.L2Z :=
  if h : Memℓp (earlyCoordinates u) 2 then ⟨earlyCoordinates u, h⟩ else 0

def earlyDerivative (u : PhysicalL2) : PhysicalL2 →L[ℝ] Lib.L2Z :=
  fderiv ℝ normingDirichletMap u

def earlyDerivativeRemainder (u : PhysicalL2) : PhysicalL2 →L[ℝ] Lib.L2Z :=
  earlyDerivative u - earlyDerivative 0

namespace G1091S1

/-- Step 0: the bridge is definitional. -/
theorem L2Z_eq_lp : Lib.L2Z = lp (fun _ : ℤ => ℂ) 2 := rfl

theorem ofReal_memℓp (a : lp (fun _ : ℤ => ℝ) 2) : Memℓp (fun n : ℤ => ((a n : ℝ) : ℂ)) 2 := by
  refine (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mpr ?_
  have hs : Summable (fun n : ℤ => ‖a n‖ ^ 2) := by
    simpa using (lp.hasSum_norm (p := (2 : ENNReal)) (E := fun _ : ℤ => ℝ) (by norm_num) a).summable
  simpa [Complex.norm_real] using hs

def ofRealL2 : lp (fun _ : ℤ => ℝ) 2 →L[ℝ] Lib.L2Z :=
  LinearMap.mkContinuous
    { toFun := fun a => ⟨fun n => ((a n : ℝ) : ℂ), ofReal_memℓp a⟩
      map_add' := fun x y => by ext n; simp <;> rfl
      map_smul' := fun c x => by ext n; simp <;> rfl }
    1 (fun a => by
      have h2 : ∀ x : lp (fun _ : ℤ => ℝ) 2, ‖x‖ ^ 2 = ∑' n : ℤ, ‖x n‖ ^ 2 := fun x => by
        have he := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) x
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using he
      have h2c : ∀ x : Lib.L2Z, ‖x‖ ^ 2 = ∑' n : ℤ, ‖x n‖ ^ 2 := fun x => by
        have he := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) x
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using he
      set y : Lib.L2Z := ⟨fun n => ((a n : ℝ) : ℂ), ofReal_memℓp a⟩ with hy
      have : ‖y‖ ^ 2 = ‖a‖ ^ 2 := by
        rw [h2c, h2]
        refine tsum_congr (fun n => ?_)
        simp [hy, Complex.norm_real]
      have h3 : ‖y‖ = ‖a‖ := by
        have := sq_eq_sq₀ (norm_nonneg y) (norm_nonneg a) |>.mp this
        exact this
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      exact h3.le)

def iotaL2 : (lp (fun _ : ℤ => ℝ) 2 × lp (fun _ : ℤ => ℝ) 2) →L[ℝ] Lib.L2Z :=
  (ofRealL2.comp (ContinuousLinearMap.fst ℝ _ _)) +
    ((Complex.I • ContinuousLinearMap.id ℂ Lib.L2Z).restrictScalars ℝ).comp
      (ofRealL2.comp (ContinuousLinearMap.snd ℝ _ _))

theorem iotaL2_apply (a b : lp (fun _ : ℤ => ℝ) 2) (n : ℤ) :
    (iotaL2 (a, b) : ℤ → ℂ) n = (a n : ℂ) + Complex.I * (b n : ℂ) := by
  simp [iotaL2, ofRealL2] <;> rfl

theorem normingDirichletMap_eq
    (Kap Mu : PhysicalL2 → lp (fun _ : ℤ => ℝ) 2)
    (hK : ∀ u n, (Kap u : ℤ → ℝ) n = realKappa38 u n)
    (hM : ∀ u n, (Mu u : ℤ → ℝ) n = gkMu u n - (n : ℝ) * Real.pi) (u : PhysicalL2) :
    normingDirichletMap u = iotaL2 (Kap u, Mu u) := by
  have hc : earlyCoordinates u = (iotaL2 (Kap u, Mu u) : ℤ → ℂ) := by
    funext n
    rw [iotaL2_apply, hK, hM]
    unfold earlyCoordinates
    push_cast; ring
  have hmem : Memℓp (earlyCoordinates u) 2 := by rw [hc]; exact (iotaL2 (Kap u, Mu u)).2
  unfold normingDirichletMap
  rw [dif_pos hmem]
  ext n
  simp [hc]

theorem normingDirichletMap_analytic :
    AnalyticOnNhd ℝ normingDirichletMap Set.univ := by
  obtain ⟨Kap, Mu, hK, hM, han⟩ := NlsGge.Atomic.G1089.G1089_main
  have hfun : normingDirichletMap = fun u => iotaL2 (Kap u, Mu u) :=
    funext (normingDirichletMap_eq Kap Mu hK hM)
  rw [hfun]
  exact (iotaL2.analyticOnNhd Set.univ).comp han (fun _ _ => Set.mem_univ _)

theorem earlyDerivative_hasFDerivAt (u : PhysicalL2) :
    HasFDerivAt normingDirichletMap (earlyDerivative u) u :=
  ((normingDirichletMap_analytic u (Set.mem_univ u)).differentiableAt).hasFDerivAt

theorem earlyDerivativeRemainder_eq (u : PhysicalL2) :
    earlyDerivativeRemainder u = earlyDerivative u - earlyDerivative 0 := rfl

end G1091S1

open NlsGge.Analysis.RegularizedDeterminant in
theorem G1_091_corrected_of_HS (u : PhysicalL2)
    (h : IsHilbertSchmidt (earlyDerivativeRemainder u)) :
    IsHilbertSchmidt (earlyDerivativeRemainder u) ∧
    IsHilbertSchmidt (ContinuousLinearMap.adjoint (earlyDerivativeRemainder u)) :=
  ⟨h, (isHilbertSchmidt_adjoint_iff _).mpr h⟩


namespace G1091S3
open NlsGge.Schur

theorem refl_star (u : PhysicalL2) (n : ℤ) :
    ‖reflectedFourierL2 (star u : PhysicalL2) n‖ = ‖reflectedFourierL2 u (-n)‖ := by
  rw [reflectedFourierL2_apply, reflectedFourierL2_apply]
  unfold reflectedFourier
  rw [physicalFourier_star38, norm_neg, norm_neg, norm_star, neg_neg]

theorem physicalSobolev_star (u : PhysicalL2) (h : physicalSobolev 1 u) :
    physicalSobolev 1 (star u : PhysicalL2) := by
  unfold physicalSobolev SobolevSquareSummable at h ⊢
  have h' := (Equiv.neg ℤ).summable_iff.mpr h
  refine h'.congr (fun j => ?_)
  simp only [Function.comp, Equiv.neg_apply, refl_star, neg_neg]
  have : Real.rpow (japaneseBracket (-j)) (2 * 1) = Real.rpow (japaneseBracket j) (2 * 1) := by
    rw [NlsGge.Analysis.japaneseBracket_h1_weight, NlsGge.Analysis.japaneseBracket_h1_weight]; simp
  rw [this]

theorem pairSobolev_realSlice (u : PhysicalL2) (h : physicalSobolev 1 u) :
    pairSobolev 1 (realSlice u) := ⟨h, physicalSobolev_star u h⟩


open NlsGge.GK38.PoissonMixed38 in
theorem earlyDerivative_apply (u v : PhysicalL2) (n : ℤ) :
    ((earlyDerivative u v : Lib.L2Z) : ℤ → ℂ) n =
      (realKappaCLM38 u n v : ℂ) + Complex.I * ((fderiv ℝ (fun w => gkMu w n) u v : ℝ) : ℂ) := by
  let ev : Lib.L2Z →L[ℝ] ℂ := lp.evalCLM ℝ (fun _ : ℤ => ℂ) (p := 2) n
  have h1 : HasFDerivAt (fun w => ev (normingDirichletMap w)) (ev.comp (earlyDerivative u)) u :=
    ev.hasFDerivAt.comp u (G1091S1.earlyDerivative_hasFDerivAt u)
  have hfun : (fun w => ev (normingDirichletMap w)) =
      fun w => (realKappa38 w n : ℂ) + Complex.I * ((gkMu w n - (n : ℝ) * Real.pi : ℝ) : ℂ) := by
    obtain ⟨Kap, Mu, hK, hM, _⟩ := NlsGge.Atomic.G1089.G1089_main
    funext w
    rw [G1091S1.normingDirichletMap_eq Kap Mu hK hM w]
    show ((G1091S1.iotaL2 (Kap w, Mu w) : Lib.L2Z) : ℤ → ℂ) n = _
    rw [G1091S1.iotaL2_apply, hK, hM]
  have hk : HasFDerivAt (fun w => (realKappa38 w n : ℂ))
      (Complex.ofRealCLM.comp (realKappaCLM38 u n)) u :=
    Complex.ofRealCLM.hasFDerivAt.comp u (hasFDerivAt_realKappa38 u n)
  have hm : HasFDerivAt (fun w => gkMu w n) (fderiv ℝ (fun w => gkMu w n) u) u :=
    (analyticAt_gkMu38 u n).differentiableAt.hasFDerivAt
  have hm2 : HasFDerivAt (fun w => ((gkMu w n - (n : ℝ) * Real.pi : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ (fun w => gkMu w n) u)) u :=
    Complex.ofRealCLM.hasFDerivAt.comp u (hm.sub_const _)
  have h2 : HasFDerivAt (fun w => (realKappa38 w n : ℂ) + Complex.I * ((gkMu w n - (n : ℝ) * Real.pi : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (realKappaCLM38 u n) +
        Complex.I • Complex.ofRealCLM.comp (fderiv ℝ (fun w => gkMu w n) u)) u :=
    hk.add (hm2.const_mul Complex.I)
  have h2' : HasFDerivAt (fun w => ev (normingDirichletMap w))
      (Complex.ofRealCLM.comp (realKappaCLM38 u n) +
        Complex.I • Complex.ofRealCLM.comp (fderiv ℝ (fun w => gkMu w n) u)) u := by
    rw [hfun]; exact h2
  have h3 := h1.unique h2'
  have h4 := congrArg (fun L : PhysicalL2 →L[ℝ] ℂ => L v) h3
  show ev (earlyDerivative u v) = _
  simpa using h4

end G1091S3

section G1091L5Sec
open scoped ENNReal BigOperators InnerProductSpace
open NlsGge.Analysis.RegularizedDeterminant
namespace G1091L5

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Bessel/Parseval for a bounded real functional over the internal Hilbert basis. -/
theorem sum_sq_real (g : E →L[ℝ] ℝ) :
    HasSum (fun i => (g (basis E i)) ^ 2) (‖g‖ ^ 2) := by
  set w : E := (InnerProductSpace.toDual ℝ E).symm g with hw
  have hg : ∀ v, g v = ⟪w, v⟫_ℝ := fun v => by
    have := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := E) (x := v) (y := g)
    rw [hw]; exact this.symm
  have hn : ‖g‖ = ‖w‖ := by
    rw [hw, LinearIsometryEquiv.norm_map]
  have h := (basis E).hasSum_inner_mul_inner w w
  have e : ∀ i, g (basis E i) ^ 2 = ⟪w, basis E i⟫_ℝ * ⟪basis E i, w⟫_ℝ := by
    intro i
    rw [hg, real_inner_comm (basis E i) w, sq]
  simp only [e, hn]
  rw [real_inner_self_eq_norm_sq] at h
  exact h

theorem sum_sq_complex (f : E →L[ℝ] ℂ) :
    HasSum (fun i => ‖f (basis E i)‖ ^ 2)
      (‖Complex.reCLM.comp f‖ ^ 2 + ‖Complex.imCLM.comp f‖ ^ 2) := by
  have h1 := sum_sq_real (Complex.reCLM.comp f)
  have h2 := sum_sq_real (Complex.imCLM.comp f)
  convert h1.add h2 using 1
  funext i
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply]
  ring

theorem hs_of_rows (T : E →L[ℝ] lp (fun _ : ℤ => ℂ) 2) (r : ℤ → ℝ) (hr0 : ∀ n, 0 ≤ r n)
    (hr : Summable (fun n => r n ^ 2))
    (hT : ∀ v n, ‖(T v : ℤ → ℂ) n‖ ≤ r n * ‖v‖) : IsHilbertSchmidt T := by
  let f : ℤ → E →L[ℝ] ℂ := fun n => (lp.evalCLM ℝ (fun _ : ℤ => ℂ) (p := 2) n).comp T
  have hfn : ∀ n, ‖f n‖ ≤ r n := fun n =>
    ContinuousLinearMap.opNorm_le_bound _ (hr0 n) (fun v => hT v n)
  have hre : ∀ n, ‖Complex.reCLM.comp (f n)‖ ≤ r n := fun n =>
    ContinuousLinearMap.opNorm_le_bound _ (hr0 n) (fun v =>
      (Complex.abs_re_le_norm _).trans (hT v n))
  have him : ∀ n, ‖Complex.imCLM.comp (f n)‖ ≤ r n := fun n =>
    ContinuousLinearMap.opNorm_le_bound _ (hr0 n) (fun v =>
      (Complex.abs_im_le_norm _).trans (hT v n))
  have hnorm : ∀ i, HasSum (fun n : ℤ => ‖(T (basis E i) : ℤ → ℂ) n‖ ^ 2) (‖T (basis E i)‖ ^ 2) := by
    intro i
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) (T (basis E i))
  unfold IsHilbertSchmidt NlsGge.Analysis.RegularizedDeterminant.energy
  have e1 : ∀ i, ENNReal.ofReal (‖T (basis E i)‖ ^ 2) =
      ∑' n : ℤ, ENNReal.ofReal (‖(f n) (basis E i)‖ ^ 2) := by
    intro i
    rw [← (hnorm i).tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) (hnorm i).summable]
    rfl
  simp only [e1]
  rw [ENNReal.tsum_comm]
  have e2 : ∀ n : ℤ, ∑' i, ENNReal.ofReal (‖(f n) (basis E i)‖ ^ 2) ≤ ENNReal.ofReal (2 * r n ^ 2) := by
    intro n
    have h := sum_sq_complex (f n)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) h.summable, h.tsum_eq]
    apply ENNReal.ofReal_le_ofReal
    have a1 : ‖Complex.reCLM.comp (f n)‖ ^ 2 ≤ r n ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hre n) 2
    have a2 : ‖Complex.imCLM.comp (f n)‖ ^ 2 ≤ r n ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (him n) 2
    linarith
  refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum e2) ?_)
  have hs : Summable (fun n => 2 * r n ^ 2) := hr.mul_left 2
  exact lt_top_iff_ne_top.2 hs.tsum_ofReal_ne_top

end G1091L5
end G1091L5Sec

section G1091KSec
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.GK38.GradEigen38
  NlsGge.GK38.PoissonMixed38 NlsGge.GK38.PoissonDirichlet38 NlsGge.Atomic.G1062S2
namespace G1091K

theorem norm_integralPairDiff (g h : PairKernelCont38) (C : ℝ) (hC : ∀ t, ‖g t - h t‖ ≤ C) :
    ‖integralPairCLM38 g t1 - integralPairCLM38 h t1‖ ≤ 2 * C := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC t1)
  rw [← integralPairCLM38_kernelSub]
  have hn : ‖g - h‖ ≤ C := (ContinuousMap.norm_le _ hC0).2 (fun t => by simpa using hC t)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun ψ => ?_)
  have := norm_pairIntegral38_le (g - h) t1 ψ
  calc ‖integralPairCLM38 (g - h) t1 ψ‖ ≤ (2 * ‖g - h‖) * ‖ψ‖ := this
    _ ≤ (2 * C) * ‖ψ‖ := by gcongr

theorem realKappa_row_diff_le (u : PhysicalL2) (n : ℤ) (C : ℝ)
    (hC : ∀ t, ‖kappaKernel38 (realSlice u) (gkMu u n : ℂ) t -
      kappaKernel38 (realSlice 0) (gkMu 0 n : ℂ) t‖ ≤ C) :
    ‖realKappaCLM38 u n - realKappaCLM38 0 n‖ ≤ 2 * C := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC t1)
  have hD := norm_integralPairDiff (kappaKernel38 (realSlice u) (gkMu u n : ℂ))
    (kappaKernel38 (realSlice 0) (gkMu 0 n : ℂ)) C hC
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  have e : (realKappaCLM38 u n - realKappaCLM38 0 n) v =
      Complex.re ((integralPairCLM38 (kappaKernel38 (realSlice u) (gkMu u n : ℂ)) t1 -
        integralPairCLM38 (kappaKernel38 (realSlice 0) (gkMu 0 n : ℂ)) t1) (realSlice v)) := by
    simp [realKappaCLM38, kappaCLM38, ← Complex.sub_re]
  rw [e]
  calc ‖Complex.re _‖ ≤ ‖(integralPairCLM38 (kappaKernel38 (realSlice u) (gkMu u n : ℂ)) t1 -
        integralPairCLM38 (kappaKernel38 (realSlice 0) (gkMu 0 n : ℂ)) t1) (realSlice v)‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ‖integralPairCLM38 (kappaKernel38 (realSlice u) (gkMu u n : ℂ)) t1 -
        integralPairCLM38 (kappaKernel38 (realSlice 0) (gkMu 0 n : ℂ)) t1‖ * ‖realSlice v‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ (2 * C) * ‖v‖ := by
        rw [norm_realSlice]
        exact mul_le_mul_of_nonneg_right hD (norm_nonneg _)

theorem kappaKernel_eq (φ : PotPair) (n : ℤ) (t : Time) :
    kappaKernel38 φ (muSeq φ n) t =
      -Complex.I • (normingError φ n t + (ePlus n t - eMinus n t)) := by
  unfold normingError
  rw [sub_add_cancel, smul_smul]
  simp

theorem kappaKernel_diff_le (φ ψ : PotPair) (n : ℤ) (N M : ℕ)
    (hN : N ≤ n.natAbs) (hM : M ≤ n.natAbs)
    (bφ : BddAbove (Set.range (fun t : Time => ‖normingErrorTail N φ n t‖)))
    (bψ : BddAbove (Set.range (fun t : Time => ‖normingErrorTail M ψ n t‖))) (t : Time) :
    ‖kappaKernel38 φ (muSeq φ n) t - kappaKernel38 ψ (muSeq ψ n) t‖ ≤
      kernelSup (normingErrorTail N φ n) + kernelSup (normingErrorTail M ψ n) := by
  rw [kappaKernel_eq, kappaKernel_eq, ← smul_sub, norm_smul]
  have e : normingError φ n t + (ePlus n t - eMinus n t) -
      (normingError ψ n t + (ePlus n t - eMinus n t)) =
      normingError φ n t - normingError ψ n t := by abel
  rw [e]
  simp only [norm_neg, Complex.norm_I, one_mul]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · have := le_csSup bφ ⟨t, rfl⟩
    simpa [kernelSup, normingErrorTail, hN] using this
  · have := le_csSup bψ ⟨t, rfl⟩
    simpa [kernelSup, normingErrorTail, hM] using this

theorem finite_small (K : ℕ) : {n : ℤ | ¬ K ≤ n.natAbs}.Finite := by
  refine (Set.finite_Icc (-(K : ℤ)) (K : ℤ)).subset (fun n hn => ?_)
  simp only [Set.mem_setOf_eq, not_le] at hn
  simp only [Set.mem_Icc]
  omega

theorem sq_le_aux (x a b : ℝ) (hx : x ≤ 2 * (a + b)) (h0 : 0 ≤ x) :
    x ^ 2 ≤ 8 * (a ^ 2 + b ^ 2) := by
  have h1 : x ^ 2 ≤ (2 * (a + b)) ^ 2 := pow_le_pow_left₀ h0 hx 2
  nlinarith [sq_nonneg (a - b)]

theorem kappa_row_le (u : PhysicalL2) (n : ℤ) (N N' : ℕ)
    (hN : N ≤ n.natAbs) (hM : N' ≤ n.natAbs)
    (b1 : BddAbove (Set.range (fun t : Time => ‖normingErrorTail N (realSlice u) n t‖)))
    (b2 : BddAbove (Set.range (fun t : Time => ‖normingErrorTail N' (realSlice 0) n t‖))) :
    ‖realKappaCLM38 u n - realKappaCLM38 0 n‖ ≤
      2 * (kernelSup (normingErrorTail N (realSlice u) n) +
        kernelSup (normingErrorTail N' (realSlice 0) n)) := by
  refine realKappa_row_diff_le u n _ (fun t => ?_)
  have H := kappaKernel_diff_le (realSlice u) (realSlice 0) n N N' hN hM b1 b2 t
  rw [muSeq_eq_gkMu38, muSeq_eq_gkMu38] at H
  exact H

theorem kappa_rows_summable (u : PhysicalL2) (hu : pairSobolev 1 (realSlice u))
    (h0 : pairSobolev 1 (realSlice 0)) :
    Summable (fun n : ℤ => ‖realKappaCLM38 u n - realKappaCLM38 0 n‖ ^ 2) := by
  obtain ⟨C, -, N, h⟩ := G1_088 (pairSobolevNorm 1 (realSlice u)) (Real.sqrt_nonneg _)
  obtain ⟨C', -, N', h'⟩ := G1_088 (pairSobolevNorm 1 (realSlice 0)) (Real.sqrt_nonneg _)
  obtain ⟨-, b1, s1, -⟩ := h (realSlice u) hu le_rfl
  obtain ⟨-, b2, s2, -⟩ := h' (realSlice 0) h0 le_rfl
  refine Summable.of_norm_bounded_eventually
    (g := fun n : ℤ => 8 * ((kernelSup (normingErrorTail N (realSlice u) n)) ^ 2 +
      (kernelSup (normingErrorTail N' (realSlice 0) n)) ^ 2)) ((s1.add s2).mul_left 8) ?_
  rw [Filter.eventually_cofinite]
  refine (finite_small (max N N')).subset (fun n hn => ?_)
  simp only [Set.mem_setOf_eq] at hn ⊢
  intro hle
  apply hn
  have hk := kappa_row_le u n N N' ((le_max_left _ _).trans hle) ((le_max_right _ _).trans hle)
    (b1 n) (b2 n)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_le_aux _ _ _ hk (norm_nonneg _)


theorem mu_row_diff_le (u : PhysicalL2) (n : ℤ) (C : ℝ)
    (hu : dirichletChar (realSlice u) (gkMu u n : ℂ) = 0 ∧
      deriv (dirichletChar (realSlice u)) (gkMu u n : ℂ) ≠ 0)
    (h0 : dirichletChar (realSlice 0) (gkMu 0 n : ℂ) = 0 ∧
      deriv (dirichletChar (realSlice 0)) (gkMu 0 n : ℂ) ≠ 0)
    (hC : ∀ t, ‖dirEigenKernel38 (realSlice u) (gkMu u n : ℂ) t -
      dirEigenKernel38 (realSlice 0) (gkMu 0 n : ℂ) t‖ ≤ C) :
    ‖fderiv ℝ (fun w : PhysicalL2 => gkMu w n) u - fderiv ℝ (fun w : PhysicalL2 => gkMu w n) 0‖
      ≤ 2 * C := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC t1)
  have hD := norm_integralPairDiff (dirEigenKernel38 (realSlice u) (gkMu u n : ℂ))
    (dirEigenKernel38 (realSlice 0) (gkMu 0 n : ℂ)) C hC
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  have e : (((fderiv ℝ (fun w : PhysicalL2 => gkMu w n) u -
      fderiv ℝ (fun w : PhysicalL2 => gkMu w n) 0) v : ℝ) : ℂ) =
      (integralPairCLM38 (dirEigenKernel38 (realSlice u) (gkMu u n : ℂ)) t1 -
        integralPairCLM38 (dirEigenKernel38 (realSlice 0) (gkMu 0 n : ℂ)) t1) (realSlice v) := by
    rw [ContinuousLinearMap.sub_apply, Complex.ofReal_sub, actual_dirichlet_label_complex_gradient,
      actual_dirichlet_label_complex_gradient,
      dirImplicitGradient_eq_kernel38 _ _ hu.1 hu.2, dirImplicitGradient_eq_kernel38 _ _ h0.1 h0.2]
    rfl
  have e2 : ‖(fderiv ℝ (fun w : PhysicalL2 => gkMu w n) u -
      fderiv ℝ (fun w : PhysicalL2 => gkMu w n) 0) v‖ = ‖(((fderiv ℝ (fun w : PhysicalL2 => gkMu w n) u -
      fderiv ℝ (fun w : PhysicalL2 => gkMu w n) 0) v : ℝ) : ℂ)‖ := (Complex.norm_real _).symm
  rw [e2, e]
  calc _ ≤ ‖integralPairCLM38 (dirEigenKernel38 (realSlice u) (gkMu u n : ℂ)) t1 -
        integralPairCLM38 (dirEigenKernel38 (realSlice 0) (gkMu 0 n : ℂ)) t1‖ * ‖realSlice v‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ (2 * C) * ‖v‖ := by
        rw [norm_realSlice]
        exact mul_le_mul_of_nonneg_right hD (norm_nonneg _)


theorem dirKernel_diff_le (φ ψ : PotPair) (n : ℤ) (N M : ℕ)
    (hN : N ≤ n.natAbs) (hM : M ≤ n.natAbs)
    (bφ : BddAbove (Set.range (fun t : Time => ‖canonicalTail N φ n 4 t‖)))
    (bψ : BddAbove (Set.range (fun t : Time => ‖canonicalTail M ψ n 4 t‖))) (t : Time) :
    ‖dirEigenKernel38 φ (muSeq φ n) t - dirEigenKernel38 ψ (muSeq ψ n) t‖ ≤
      kernelSup (canonicalTail N φ n 4) + kernelSup (canonicalTail M ψ n 4) := by
  have e : dirEigenKernel38 φ (muSeq φ n) t - dirEigenKernel38 ψ (muSeq ψ n) t =
      canonicalError φ n 4 t - canonicalError ψ n 4 t := by
    simp [canonicalError]
  rw [e]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · have := le_csSup bφ ⟨t, rfl⟩
    simpa [kernelSup, canonicalTail, hN] using this
  · have := le_csSup bψ ⟨t, rfl⟩
    simpa [kernelSup, canonicalTail, hM] using this


theorem mu_row_le (u : PhysicalL2) (n : ℤ) (N N' : ℕ)
    (hN : N ≤ n.natAbs) (hM : N' ≤ n.natAbs)
    (hu : simpleDirichlet (realSlice u) (muSeq (realSlice u) n))
    (h0 : simpleDirichlet (realSlice 0) (muSeq (realSlice 0) n))
    (b1 : BddAbove (Set.range (fun t : Time => ‖canonicalTail N (realSlice u) n 4 t‖)))
    (b2 : BddAbove (Set.range (fun t : Time => ‖canonicalTail N' (realSlice 0) n 4 t‖))) :
    ‖fderiv ℝ (fun w : PhysicalL2 => gkMu w n) u - fderiv ℝ (fun w : PhysicalL2 => gkMu w n) 0‖
      ≤ 2 * (kernelSup (canonicalTail N (realSlice u) n 4) +
        kernelSup (canonicalTail N' (realSlice 0) n 4)) := by
  rw [muSeq_eq_gkMu38] at hu h0
  refine mu_row_diff_le u n _ hu h0 (fun t => ?_)
  have H := dirKernel_diff_le (realSlice u) (realSlice 0) n N N' hN hM b1 b2 t
  rw [muSeq_eq_gkMu38, muSeq_eq_gkMu38] at H
  exact H

theorem mu_rows_summable (u : PhysicalL2) (hu : pairSobolev 1 (realSlice u))
    (h0 : pairSobolev 1 (realSlice 0)) :
    Summable (fun n : ℤ => ‖fderiv ℝ (fun w : PhysicalL2 => gkMu w n) u -
      fderiv ℝ (fun w : PhysicalL2 => gkMu w n) 0‖ ^ 2) := by
  obtain ⟨C, -, N, h⟩ := G1_062 (pairSobolevNorm 1 (realSlice u)) (Real.sqrt_nonneg _)
  obtain ⟨C', -, N', h'⟩ := G1_062 (pairSobolevNorm 1 (realSlice 0)) (Real.sqrt_nonneg _)
  obtain ⟨hs1, hj1⟩ := h (realSlice u) hu le_rfl
  obtain ⟨hs2, hj2⟩ := h' (realSlice 0) h0 le_rfl
  obtain ⟨b1, s1, -⟩ := hj1 4
  obtain ⟨b2, s2, -⟩ := hj2 4
  refine Summable.of_norm_bounded_eventually
    (g := fun n : ℤ => 8 * ((kernelSup (canonicalTail N (realSlice u) n 4)) ^ 2 +
      (kernelSup (canonicalTail N' (realSlice 0) n 4)) ^ 2)) ((s1.add s2).mul_left 8) ?_
  rw [Filter.eventually_cofinite]
  refine (finite_small (max N N')).subset (fun n hn => ?_)
  simp only [Set.mem_setOf_eq] at hn ⊢
  intro hle
  apply hn
  have hN : N ≤ n.natAbs := (le_max_left _ _).trans hle
  have hM : N' ≤ n.natAbs := (le_max_right _ _).trans hle
  have hk := mu_row_le u n N N' hN hM (hs1 n hN).1 (hs2 n hM).1 (b1 n) (b2 n)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_le_aux _ _ _ hk (norm_nonneg _)

end G1091K
end G1091KSec


namespace G1091F
open NlsGge.Analysis.RegularizedDeterminant

theorem physicalSobolev_zero : physicalSobolev 1 (0 : PhysicalL2) := by
  unfold physicalSobolev SobolevSquareSummable
  simp

theorem ofReal_sub_apply_bound (x y : ℝ) : ‖(x : ℂ) + Complex.I * (y : ℂ)‖ ≤ |x| + |y| := by
  refine (norm_add_le _ _).trans ?_
  simp

theorem rows_bound (u : PhysicalL2) (v : PhysicalL2) (n : ℤ) :
    ‖((earlyDerivativeRemainder u v : Lib.L2Z) : ℤ → ℂ) n‖ ≤
      (‖realKappaCLM38 u n - realKappaCLM38 0 n‖ +
        ‖fderiv ℝ (fun w : PhysicalL2 => gkMu w n) u -
          fderiv ℝ (fun w : PhysicalL2 => gkMu w n) 0‖) * ‖v‖ := by
  have e : ((earlyDerivativeRemainder u v : Lib.L2Z) : ℤ → ℂ) n =
      (((realKappaCLM38 u n - realKappaCLM38 0 n) v : ℝ) : ℂ) +
        Complex.I * ((((fderiv ℝ (fun w : PhysicalL2 => gkMu w n) u -
          fderiv ℝ (fun w : PhysicalL2 => gkMu w n) 0) v : ℝ)) : ℂ) := by
    show (((earlyDerivative u v - earlyDerivative 0 v : Lib.L2Z)) : ℤ → ℂ) n = _
    rw [lp.coeFn_sub, Pi.sub_apply, G1091S3.earlyDerivative_apply, G1091S3.earlyDerivative_apply]
    simp only [ContinuousLinearMap.sub_apply, Complex.ofReal_sub]
    ring
  rw [e]
  refine (ofReal_sub_apply_bound _ _).trans ?_
  rw [add_mul]
  refine add_le_add ?_ ?_
  · simpa [Real.norm_eq_abs] using ContinuousLinearMap.le_opNorm (realKappaCLM38 u n - realKappaCLM38 0 n) v
  · simpa [Real.norm_eq_abs] using ContinuousLinearMap.le_opNorm (fderiv ℝ (fun w : PhysicalL2 => gkMu w n) u -
          fderiv ℝ (fun w : PhysicalL2 => gkMu w n) 0) v

end G1091F

open NlsGge.Analysis.RegularizedDeterminant in
theorem G1_091_corrected (u : PhysicalL2) (hu : physicalSobolev 1 u) :
    IsHilbertSchmidt (earlyDerivativeRemainder u) ∧
    IsHilbertSchmidt (ContinuousLinearMap.adjoint (earlyDerivativeRemainder u)) := by
  refine G1_091_corrected_of_HS u ?_
  have hu' : pairSobolev 1 (realSlice u) := G1091S3.pairSobolev_realSlice u hu
  have h0 : pairSobolev 1 (realSlice 0) :=
    G1091S3.pairSobolev_realSlice 0 G1091F.physicalSobolev_zero
  have sk := G1091K.kappa_rows_summable u hu' h0
  have sm := G1091K.mu_rows_summable u hu' h0
  refine G1091L5.hs_of_rows (earlyDerivativeRemainder u)
    (fun n => ‖realKappaCLM38 u n - realKappaCLM38 0 n‖ +
      ‖fderiv ℝ (fun w : PhysicalL2 => gkMu w n) u - fderiv ℝ (fun w : PhysicalL2 => gkMu w n) 0‖)
    (fun n => by positivity) ?_ (fun v n => G1091F.rows_bound u v n)
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) ((sk.add sm).mul_left 2)
  nlinarith [sq_nonneg (‖realKappaCLM38 u n - realKappaCLM38 0 n‖ -
      ‖fderiv ℝ (fun w : PhysicalL2 => gkMu w n) u - fderiv ℝ (fun w : PhysicalL2 => gkMu w n) 0‖)]



end
end NlsGge.GKDefinitionDesign
