/- G1-022 PRODUCTION02 (proof development batch-8 landing kit). Source: proof development/G1022_PROOF05.lean.txt. #check/#print lines removed; original namespaces kept; deleted verbatim copy: source lines 13-1055 (through "end NlsGge.Atomic.G1011S2"); imports added: NlsGge.Atomic.G1.G1011. No acceptance claimed. -/
import Mathlib
import NlsGge.Atomic.G1.G1004
import NlsGge.Atomic.G1.G1003
import NlsGge.Atomic.G1.G1008
import NlsGge.Atomic.Volterra
import NlsGge.GK38.PairAnalytic
import NlsGge.GK38.PairAnalyticOp
import NlsGge.GK38.PairPotential
import NlsGge.GK38.PairVolterraDefs
import NlsGge.GK38.PairVolterraOp
import NlsGge.GK38.PairVolterraPower
import NlsGge.Atomic.G1.G1011


/-! ============================================================================
G1-022 pre-approval proof (proof development, AUTHOR; not self-reviewed).
The text above (G1-005/G1-010 kits and the G1-011 proof) is a private verbatim copy of
proof development/G1011_PROOF02.lean.txt lines 1-1055 (namespace NlsGge.Atomic.G1011S2.*), unchanged.
Statement = proof development/G1-022_COMMAND02b, verbatim.
Route: F(ψ) = fundContT ψ z hT is differentiable (G1-004 analyticity), its derivative X = F'(φ) h solves
X = V_φ X + V_h F(φ) (product rule, V_ψ = L ψ linear in ψ, `volterraPT`); the formula function Y of G1-011
(column j, g_j = R Φ̃_h M e_j) solves the same Duhamel equation (G1011_main, direction ←) and (1 - V_φ) is a
unit, so X = Y; the entries of Y are those of M(t) ∫ M⁻¹ Φ̃_h M.
============================================================================ -/

namespace NlsGge.Atomic.G1022S3

open MeasureTheory Filter Topology Set NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations
open NlsGge.Atomic.G1004GenT NlsGge.Atomic.G1011S2 NlsGge.Pilot

noncomputable section

/-- The `j`-th standard basis vector. -/
def ej (j : Fin 2) : Fin 2 → ℂ := Pi.single j 1

theorem mulVec_ej (X : Mat2) (j k : Fin 2) : (X.mulVec (ej j)) k = X k j := by
  rw [ej, Matrix.mulVec_single_one]; rfl

theorem mul3_apply_col (E P N : Mat2) (i j : Fin 2) :
    (E * P * N) i j = (E.mulVec (P.mulVec (N.mulVec (ej j)))) i := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mulVec_ej]

theorem Mf_eq_ext (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    Mf φ z s = ext38T hT (fundContT φ z hT) s := by
  rw [ext38T_of_mem hT _ hs]
  exact tsum_terms_eq_fundContT φ z hT hs

theorem Mf_continuousOn (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (i j : Fin 2) :
    ContinuousOn (fun s => Mf φ z s i j) (Set.Icc (0 : ℝ) T) := by
  have hc : Continuous (fun s => ext38T hT (fundContT φ z hT) s i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp (continuous_ext38T hT _))
  refine hc.continuousOn.congr fun s hs => ?_
  show Mf φ z s i j = ext38T hT (fundContT φ z hT) s i j
  rw [Mf_eq_ext φ z hT hs]

theorem Rm_mulVec_mulVec (v : Fin 2 → ℂ) : Rm.mulVec (Rm.mulVec v) = -v := by
  funext i
  rcases fin2_cases i with rfl | rfl
  · rw [Rm_apply0, Rm_apply0]
    simp only [Pi.neg_apply]
    linear_combination (v 0) * Complex.I_mul_I
  · rw [Rm_apply1, Rm_apply1]
    simp only [Pi.neg_apply]
    linear_combination (v 1) * Complex.I_mul_I

/-- The inhomogeneity of the column `j` (so that `-R g = Φ̃_h M e_j`). -/
def gcol (φ h : PotPair) (z : ℂ) (j : Fin 2) (s : ℝ) : Fin 2 → ℂ :=
  Rm.mulVec ((PCm h s).mulVec ((Mf φ z s).mulVec (ej j)))

theorem gcol_zero (φ h : PotPair) (z : ℂ) (j : Fin 2) (s : ℝ) :
    gcol φ h z j s 0 = -(potRepFst38 h s * Mf φ z s 1 j) := by
  have hy : (Mf φ z s).mulVec (ej j) = fun k => Mf φ z s k j := funext fun k => mulVec_ej _ j k
  rw [gcol, Rm_apply0, hy]
  simp only [PCm, rawPotCoeff38, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
  have : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (potRepFst38 h s * Mf φ z s 1 j) * this

theorem gcol_one (φ h : PotPair) (z : ℂ) (j : Fin 2) (s : ℝ) :
    gcol φ h z j s 1 = -(potRepSnd38 h s * Mf φ z s 0 j) := by
  have hy : (Mf φ z s).mulVec (ej j) = fun k => Mf φ z s k j := funext fun k => mulVec_ej _ j k
  rw [gcol, Rm_apply1, hy]
  simp only [PCm, rawPotCoeff38, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
  have : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (potRepSnd38 h s * Mf φ z s 0 j) * this

theorem memLp_cr_mul (f : PhysicalL2) {T : ℝ} (hT : 0 ≤ T) {m : ℝ → ℂ}
    (hm : ContinuousOn m (Set.Icc (0 : ℝ) T)) :
    MemLp (fun s => coverRep38 f s * m s) 2 (volume.restrict (Set.Icc (0 : ℝ) T)) := by
  obtain ⟨G, hG⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hm
  have hmeas : AEStronglyMeasurable (fun s => coverRep38 f s * m s)
      (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    (stronglyMeasurable_coverRep38 f).aestronglyMeasurable.mul
      (hm.aestronglyMeasurable measurableSet_Icc)
  refine (memLp_two_iff_integrable_sq_norm hmeas).2 ?_
  have hI : IntegrableOn (fun s => ‖coverRep38 f s‖ ^ 2) (Set.Icc (0 : ℝ) T) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT).1
      (NlsGge.Atomic.G1008.intervalIntegrable_cr_sq_any f 0 T)
  refine Integrable.mono' (hI.const_mul (G ^ 2)) (hmeas.norm.pow 2) ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
  have h1 : ‖m s‖ ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hG s hs) 2
  nlinarith [sq_nonneg ‖coverRep38 f s‖]

theorem gcol_memLp (φ h : PotPair) (z : ℂ) (j : Fin 2) :
    ∀ T : ℝ, 0 ≤ T → ∀ i : Fin 2,
      MemLp (fun s => gcol φ h z j s i) 2 (volume.restrict (Set.Icc (0 : ℝ) T)) := by
  intro T hT i
  rcases fin2_cases i with rfl | rfl
  · have e : (fun s => gcol φ h z j s 0) = fun s => -(coverRep38 h.1 s * Mf φ z s 1 j) :=
      funext fun s => gcol_zero φ h z j s
    rw [e]
    exact (memLp_cr_mul h.1 hT (Mf_continuousOn φ z hT 1 j)).neg
  · have e : (fun s => gcol φ h z j s 1) = fun s => -(coverRep38 h.2 s * Mf φ z s 0 j) :=
      funext fun s => gcol_one φ h z j s
    rw [e]
    exact (memLp_cr_mul h.2 hT (Mf_continuousOn φ z hT 0 j)).neg

/-- The column `j` of `M(t) ∫₀ᵗ M⁻¹ Φ̃_h M` in the form produced by G1-011 (`v0 = 0`). -/
def Yv (φ h : PotPair) (z : ℂ) (j : Fin 2) (t : ℝ) : Fin 2 → ℂ :=
  (Mf φ z t).mulVec (0 - ∫ s in (0 : ℝ)..t, ((Mf φ z s)⁻¹).mulVec (Rm.mulVec (gcol φ h z j s)))

theorem Yv_sol (φ h : PotPair) (z : ℂ) (j : Fin 2) :
    (∀ T : ℝ, 0 ≤ T → ∀ i : Fin 2,
      AbsolutelyContinuousOnInterval (fun t => Yv φ h z j t i) 0 T) ∧
    (∀ t : ℝ, 0 ≤ t → Yv φ h z j t = (freeE z t).mulVec 0 +
      ∫ s in (0 : ℝ)..t, (freeE z (t - s)).mulVec
        ((PCm φ s).mulVec (Yv φ h z j s) - Rm.mulVec (gcol φ h z j s))) :=
  (G1011_main φ z (gcol φ h z j) 0 (gcol_memLp φ h z j) (Yv φ h z j)).2 (fun t _ => rfl)

/-! ### The operator-level derivative equation -/

/-- `ψ ↦ 𝒱_ψ` at fixed `z` as a continuous linear map (the construction of `volterraZeroLT` at general `z`). -/
def volterraLT (z : ℂ) {T : ℝ} (hT : 0 ≤ T) : PotPair →L[ℂ] (PairContT T →L[ℂ] PairContT T) :=
  LinearMap.mkContinuous
    { toFun := fun φ => volterraPT φ z hT
      map_add' := fun φ ψ => volterraPT_add φ ψ z hT
      map_smul' := fun c φ => by
        show volterraPT (c • φ) z hT = c • volterraPT φ z hT
        exact volterraPT_smul_potential c φ z hT }
    (Real.exp (|z.im| * T) * (2 * (Nat.ceil T : ℝ))) fun φ => by
      refine (norm_volterraPT_le φ z hT).trans ?_
      have h := potL1Norm38_le_two_mul φ
      have hc : (0 : ℝ) ≤ Nat.ceil T := Nat.cast_nonneg _
      have he := Real.exp_pos (|z.im| * T)
      calc Real.exp (|z.im| * T) * ((Nat.ceil T : ℝ) * potL1Norm38 φ)
          ≤ Real.exp (|z.im| * T) * ((Nat.ceil T : ℝ) * (2 * ‖φ‖)) := by gcongr
        _ = Real.exp (|z.im| * T) * (2 * (Nat.ceil T : ℝ)) * ‖φ‖ := by ring

theorem volterraLT_apply (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (φ : PotPair) :
    volterraLT z hT φ = volterraPT φ z hT := rfl


theorem fund_deriv_eq (φ h : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) :
    DifferentiableAt ℂ (fun ψ : PotPair => fundContT ψ z hT) φ ∧
    (fderiv ℂ (fun ψ : PotPair => fundContT ψ z hT) φ) h =
      volterraPT φ z hT ((fderiv ℂ (fun ψ : PotPair => fundContT ψ z hT) φ) h) +
        volterraPT h z hT (fundContT φ z hT) := by
  have hF : DifferentiableAt ℂ (fun ψ : PotPair => fundContT ψ z hT) φ := by
    have h1 : AnalyticAt ℂ (fun ψ : PotPair => fundContT ψ z hT) φ :=
      AnalyticAt.comp (g := fun p : PotPair × ℂ => fundContT p.1 p.2 hT)
        (f := fun ψ : PotPair => (ψ, z))
        (analyticOnNhd_fundContT hT (φ, z) (Set.mem_univ _))
        (analyticAt_id.prod analyticAt_const)
    exact h1.differentiableAt
  refine ⟨hF, ?_⟩
  have hLd : HasFDerivAt (volterraLT z hT) (volterraLT z hT) φ := ContinuousLinearMap.hasFDerivAt (𝕜 := ℂ) (E := PotPair)
    (F := PairContT T →L[ℂ] PairContT T) (volterraLT z hT)
  have hFd : HasFDerivAt (fun ψ : PotPair => fundContT ψ z hT)
      (fderiv ℂ (fun ψ : PotPair => fundContT ψ z hT) φ) φ := hF.hasFDerivAt
  have hRHS := (hLd.clm_apply hFd).const_add (freeFundT T z)
  have hRHS' : HasFDerivAt (fun ψ : PotPair => fundContT ψ z hT) _ φ :=
    hRHS.congr_of_eventuallyEq (Eventually.of_forall fun ψ => by
      show fundContT ψ z hT = freeFundT T z + volterraPT ψ z hT (fundContT ψ z hT)
      exact fundContT_eq_add ψ z hT)
  have hU := hFd.unique hRHS'
  have := congrArg (fun L => L h) hU
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply] at this
  exact this

/-! ### The formula column solves the same operator equation -/

theorem Ycm_exists (φ h : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ Y : PairContT T, (∀ (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) T) (i j : Fin 2),
        Y ⟨s, hs⟩ i j = Yv φ h z j s i) ∧
      Y = volterraPT φ z hT Y + volterraPT h z hT (fundContT φ z hT) := by
  have hcont : ∀ i j : Fin 2, Continuous (fun t : Set.Icc (0 : ℝ) T => Yv φ h z j t.1 i) := by
    intro i j
    have h1 := ((Yv_sol φ h z j).1 T hT i).continuousOn
    rw [Set.uIcc_of_le hT] at h1
    exact continuousOn_iff_continuous_restrict.1 h1
  let Y : PairContT T :=
    ⟨fun t i j => Yv φ h z j t.1 i, continuous_pi fun i => continuous_pi fun j => hcont i j⟩
  have hY : ∀ (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) T) (i j : Fin 2),
      Y ⟨s, hs⟩ i j = Yv φ h z j s i := fun _ _ _ _ => rfl
  refine ⟨Y, hY, ?_⟩
  ext ⟨t, ht⟩ i j
  show Yv φ h z j t i =
    (∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 φ s * ext38T hT Y s) i j) +
    ∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 h s * ext38T hT (fundContT φ z hT) s) i j
  have ht0 : 0 ≤ t := ht.1
  have hsub : ∀ s ∈ Set.uIcc (0 : ℝ) t, s ∈ Set.Icc (0 : ℝ) T := fun s hs => by
    rw [Set.uIcc_of_le ht0] at hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  have hpt : ∀ k : Fin 2, ∀ s ∈ Set.uIcc (0 : ℝ) t,
      ((freeE z (t - s)).mulVec ((PCm φ s).mulVec (Yv φ h z j s) - Rm.mulVec (gcol φ h z j s))) k =
        (freeE z (t - s) * potCoeff38 φ s * ext38T hT Y s) k j +
        (freeE z (t - s) * potCoeff38 h s * ext38T hT (fundContT φ z hT) s) k j := by
    intro k s hs
    have hs' := hsub s hs
    have hYs : (ext38T hT Y s).mulVec (ej j) = Yv φ h z j s := funext fun l => by
      rw [mulVec_ej, ext38T_of_mem hT _ hs']
      exact hY s hs' l j
    have hMs : (ext38T hT (fundContT φ z hT) s).mulVec (ej j) = (Mf φ z s).mulVec (ej j) := by
      rw [Mf_eq_ext φ z hT hs']
    rw [mul3_apply_col, mul3_apply_col, hYs, hMs]
    have hg : Rm.mulVec (gcol φ h z j s) = -((PCm h s).mulVec ((Mf φ z s).mulVec (ej j))) :=
      Rm_mulVec_mulVec _
    rw [hg, sub_neg_eq_add, Matrix.mulVec_add, Pi.add_apply]
    rfl
  have hK : Continuous fun s : ℝ => freeE z (t - s) :=
    (continuous_freeE z).comp (continuous_const.sub continuous_id)
  have hI1 : ∀ k : Fin 2, IntervalIntegrable
      (fun s => (freeE z (t - s) * potCoeff38 φ s * ext38T hT Y s) k j) volume 0 t := fun k =>
    intervalIntegrable_triple_entryT_of_mem φ hT hK (continuous_ext38T hT Y) ht k j
  have hI2 : ∀ k : Fin 2, IntervalIntegrable
      (fun s => (freeE z (t - s) * potCoeff38 h s * ext38T hT (fundContT φ z hT) s) k j)
      volume 0 t := fun k =>
    intervalIntegrable_triple_entryT_of_mem h hT hK (continuous_ext38T hT _) ht k j
  have hv : ∀ k : Fin 2, IntervalIntegrable
      (fun s => ((freeE z (t - s)).mulVec
        ((PCm φ s).mulVec (Yv φ h z j s) - Rm.mulVec (gcol φ h z j s))) k) volume 0 t := fun k =>
    ((hI1 k).add (hI2 k)).congr (fun s hs => (hpt k s (Set.uIoc_subset_uIcc hs)).symm)
  have e1 : Yv φ h z j t i = ∫ s in (0 : ℝ)..t, ((freeE z (t - s)).mulVec
      ((PCm φ s).mulVec (Yv φ h z j s) - Rm.mulVec (gcol φ h z j s))) i := by
    have := congrFun ((Yv_sol φ h z j).2 t ht0) i
    simp only [Matrix.mulVec_zero, Pi.add_apply, Pi.zero_apply, zero_add] at this
    rw [this]
    exact ivInt_apply ht0 hv i
  rw [e1, intervalIntegral.integral_congr (fun s hs => hpt i s hs),
    intervalIntegral.integral_add (hI1 i) (hI2 i)]

/-! ### Uniqueness: the derivative column is the formula column -/

theorem fund_deriv_formula (φ h : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) (i j : Fin 2) :
    (fderiv ℂ (fun ψ : PotPair => fundContT ψ z hT) φ h) ⟨t, ht⟩ i j = Yv φ h z j t i := by
  obtain ⟨-, heq⟩ := fund_deriv_eq φ h z hT
  obtain ⟨Y, hY, hYeq⟩ := Ycm_exists φ h z hT
  set X := (fderiv ℂ (fun ψ : PotPair => fundContT ψ z hT) φ h) with hX
  set V := volterraPT φ z hT with hV
  set W := volterraPT h z hT (fundContT φ z hT) with hW
  have hU : IsUnit (1 - V) := isUnit_one_sub_volterraPT φ z hT
  have hXW : (1 - V) X = W := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    exact sub_eq_of_eq_add' heq
  have hYW : (1 - V) Y = W := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    exact sub_eq_of_eq_add' hYeq
  have hinv : ∀ N : PairContT T, N = Ring.inverse (1 - V) ((1 - V) N) := fun N => by
    have := congrArg (fun L => L N) (Ring.inverse_mul_cancel _ hU)
    exact this.symm
  have hXY : X = Y := by
    rw [hinv X, hinv Y, hXW, hYW]
  rw [hXY]
  exact hY t ht i j

/-! ### Entries of the right-hand side -/

open scoped Matrix.Norms.L2Operator in
theorem matInt_apply {A : ℝ → Mat2} {t : ℝ}
    (hA : ∀ i j, IntervalIntegrable (fun s => A s i j) volume 0 t) (k j : Fin 2) :
    (∫ s in (0 : ℝ)..t, A s) k j = ∫ s in (0 : ℝ)..t, A s k j := by
  have hrep : A = fun s => ∑ i : Fin 2, ∑ j : Fin 2, (A s i j) • Matrix.single i j (1 : ℂ) := by
    funext s
    conv_lhs => rw [Matrix.matrix_eq_sum_single (A s)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_single]; simp
  have hAint : IntervalIntegrable A volume 0 t := by
    have h2 : ∀ i j : Fin 2, IntervalIntegrable (fun s => (A s i j) • Matrix.single i j (1 : ℂ))
        volume 0 t := fun i j =>
      intervalIntegrable_iff.2 ((intervalIntegrable_iff.1 (hA i j)).smul_const _)
    have := IntervalIntegrable.sum Finset.univ
      (fun i _ => IntervalIntegrable.sum Finset.univ (fun j _ => h2 i j))
    simp only [Finset.sum_fn] at this
    rwa [← hrep] at this
  let ε : Matrix (Fin 2) (Fin 2) ℂ →L[ℂ] ℂ :=
    { toLinearMap := Matrix.entryLinearMap ℂ ℂ k j
      cont := LinearMap.continuous_of_finiteDimensional _ }
  have hcomm := ε.intervalIntegral_comp_comm hAint
  exact hcomm.symm

theorem v_integrable (φ h : PotPair) (z : ℂ) (j : Fin 2) {t : ℝ} (ht : 0 ≤ t) (k : Fin 2) :
    IntervalIntegrable
      (fun s => (((Mf φ z s)⁻¹).mulVec (Rm.mulVec (gcol φ h z j s))) k) volume 0 t := by
  have hcd := coreData φ z (gcol φ h z j) (gcol_memLp φ h z j)
  refine (hcd.adjh_int ht k).congr (fun s hs => ?_)
  rw [Set.uIoc_of_le ht] at hs
  show ((Nf φ z s).adjugate.mulVec (hf z (gcol φ h z j) s)) k =
    (((Mf φ z s)⁻¹).mulVec (Rm.mulVec (gcol φ h z j s))) k
  rw [Mf_inv φ z hs.1.le hcd, ← Matrix.mulVec_mulVec]
  rfl

open scoped Matrix.Norms.L2Operator in
theorem rhs_entry (φ h : PotPair) (z : ℂ) {t : ℝ} (ht : 0 ≤ t) (i j : Fin 2) :
    (Mf φ z t * ∫ s in (0 : ℝ)..t, ((Mf φ z s)⁻¹ * PCm h s * Mf φ z s)) i j = Yv φ h z j t i := by
  have hAv : ∀ (k l : Fin 2) (s : ℝ), ((Mf φ z s)⁻¹ * PCm h s * Mf φ z s) k l =
      -((((Mf φ z s)⁻¹).mulVec (Rm.mulVec (gcol φ h z l s))) k) := by
    intro k l s
    have hg : Rm.mulVec (gcol φ h z l s) = -((PCm h s).mulVec ((Mf φ z s).mulVec (ej l))) :=
      Rm_mulVec_mulVec _
    rw [mul3_apply_col, hg, Matrix.mulVec_neg, Pi.neg_apply, neg_neg]
  have hA : ∀ k l : Fin 2, IntervalIntegrable
      (fun s => ((Mf φ z s)⁻¹ * PCm h s * Mf φ z s) k l) volume 0 t := fun k l => by
    have := (v_integrable φ h z l ht k).neg
    refine this.congr (fun s _ => ?_)
    exact (hAv k l s).symm
  have hIv : ∀ k, (∫ s in (0 : ℝ)..t, ((Mf φ z s)⁻¹).mulVec (Rm.mulVec (gcol φ h z j s))) k =
      ∫ s in (0 : ℝ)..t, (((Mf φ z s)⁻¹).mulVec (Rm.mulVec (gcol φ h z j s))) k :=
    fun k => ivInt_apply ht (fun l => v_integrable φ h z j ht l) k
  have hIA : ∀ k, (∫ s in (0 : ℝ)..t, ((Mf φ z s)⁻¹ * PCm h s * Mf φ z s)) k j =
      -∫ s in (0 : ℝ)..t, (((Mf φ z s)⁻¹).mulVec (Rm.mulVec (gcol φ h z j s))) k := by
    intro k
    rw [matInt_apply hA k j, ← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun s _ => hAv k j s
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Yv, Matrix.mulVec, dotProduct, Pi.sub_apply,
    Pi.zero_apply]
  rw [hIA 0, hIA 1, hIv 0, hIv 1]
  ring

/-! ### The theorem (G1-022 COMMAND02b, verbatim) -/

open scoped Matrix.Norms.L2Operator in
theorem G1022_main :
    ((∀ (φ h : PotPair) (z : ℂ) (t : ℝ), 0 ≤ t →
  let Mf : PotPair → ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun ψ s => ∑' n : ℕ, potentialVolterraTerm38 ψ z n s
  DifferentiableAt ℂ (fun ψ : PotPair => Mf ψ t) φ ∧
  fderiv ℂ (fun ψ : PotPair => Mf ψ t) φ h =
    Mf φ t * ∫ s in (0 : ℝ)..t,
      ((Mf φ s)⁻¹ * rawPotCoeff38 (potRepFst38 h) (potRepSnd38 h) s * Mf φ s))
  : Prop) := by
  intro φ h z t ht Mg
  have ht' : t ∈ Set.Icc (0 : ℝ) t := ⟨ht, le_rfl⟩
  have hdiff : DifferentiableAt ℂ (fun ψ : PotPair => Mg ψ t) φ := by
    have h1 : AnalyticAt ℂ (fun p : ℂ × PotPair => ∑' n : ℕ, potentialVolterraTerm38 p.2 p.1 n t)
        (z, φ) := analytic_all t ht (z, φ) (Set.mem_univ _)
    have h2 : AnalyticAt ℂ (fun ψ : PotPair => ((z, ψ) : ℂ × PotPair)) φ :=
      analyticAt_const.prod analyticAt_id
    exact (h1.comp h2).differentiableAt
  refine ⟨hdiff, ?_⟩
  have hentry : ∀ i j : Fin 2,
      (fderiv ℂ (fun ψ : PotPair => Mg ψ t) φ h) i j = Yv φ h z j t i := by
    intro i j
    let ε : Matrix (Fin 2) (Fin 2) ℂ →L[ℂ] ℂ :=
      { toLinearMap := Matrix.entryLinearMap ℂ ℂ i j
        cont := LinearMap.continuous_of_finiteDimensional _ }
    have h1 : HasFDerivAt (fun ψ : PotPair => (Mg ψ t) i j)
        (ε.comp (fderiv ℂ (fun ψ : PotPair => Mg ψ t) φ)) φ :=
      (ContinuousLinearMap.hasFDerivAt (𝕜 := ℂ) (E := Matrix (Fin 2) (Fin 2) ℂ) (F := ℂ) ε).comp φ
        hdiff.hasFDerivAt
    have hF := (fund_deriv_eq φ h z ht).1
    have h2 : HasFDerivAt (fun ψ : PotPair => fundContT ψ z ht ⟨t, ht'⟩ i j)
        ((fundEntryLT ⟨t, ht'⟩ i j).comp
          (fderiv ℂ (fun ψ : PotPair => fundContT ψ z ht) φ)) φ :=
      (ContinuousLinearMap.hasFDerivAt (𝕜 := ℂ) (E := PairContT t) (F := ℂ)
        (fundEntryLT ⟨t, ht'⟩ i j)).comp φ hF.hasFDerivAt
    have hfun : (fun ψ : PotPair => (Mg ψ t) i j) =
        fun ψ : PotPair => fundContT ψ z ht ⟨t, ht'⟩ i j := by
      funext ψ
      have := tsum_terms_eq_fundContT ψ z ht ht'
      show (∑' n : ℕ, potentialVolterraTerm38 ψ z n t) i j = _
      rw [this]
    rw [hfun] at h1
    have hu := h1.unique h2
    have := congrArg (fun L => L h) hu
    simp only [ContinuousLinearMap.comp_apply] at this
    exact this.trans (fund_deriv_formula φ h z ht ht' i j)
  ext i j
  rw [hentry i j]
  exact (rhs_entry φ h z ht i j).symm

end

end NlsGge.Atomic.G1022S3
