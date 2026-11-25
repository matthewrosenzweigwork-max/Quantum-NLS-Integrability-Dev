import Mathlib
import NlsGge.Atomic.G6.G6041CoordCore
import NlsGge.Atomic.G6.G6039Host
import NlsGge.Atomic.G6.G6039Sup1Core
import NlsGge.Atomic.G6.G6036Core
import NlsGge.Atomic.G6.G6035Host

/- G6041 TOOL CORE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G6/G6041ToolCore.lean, namespace NlsGge.ThirdConsultation.G6041S.  SUPPORT (no packet
   increment): the linear maps of Pro's r16 §Q3 common-neighbourhood assembly (L987-998), with coordinates and norms:
   flipCLM (flipComplexCoordinate as an isometric ℂ-CLM; fixes vectors with vanishing n-th coordinate; intertwines
   diagC with the real flip G6036S.flipR), tailCLM (complexTailProjection, a contraction), headCLM
   (complexHeadLift on the finite head), rootR (real square root of a positive action sequence), tailAct (real-to-
   complex tail action map) and evalR (real coordinate into ℂ).
   Own imports: Mathlib, G6041CoordCore, G6039Host, G6039Sup1Core (coe_finsum_single), G6036Core (flipR), G6035Host. -/
set_option autoImplicit false

open Set Filter Topology
open scoped ENNReal
open NlsGge.GK38 NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.G6041S
noncomputable section

/-! ### Coordinate flips -/

theorem flipC_apply (n : ℤ) (z : ComplexDiagonalSpace) (m : ℤ) :
    flipComplexCoordinate n z m = if m = n then -z m else z m := by
  unfold flipComplexCoordinate
  rw [lp.coeFn_sub, Pi.sub_apply, lp.single_apply]
  by_cases hm : m = n
  · subst hm; simp [Pi.single_apply]; ring
  · simp [Pi.single_apply, hm]

def flipCLM (n : ℤ) : ComplexDiagonalSpace →L[ℂ] ComplexDiagonalSpace :=
  LinearMap.mkContinuous
    { toFun := flipComplexCoordinate n
      map_add' := fun z w => by
        apply lp.ext; funext m
        rw [flipC_apply, lp.coeFn_add, Pi.add_apply, lp.coeFn_add, Pi.add_apply, flipC_apply, flipC_apply]
        split_ifs <;> ring
      map_smul' := fun a z => by
        apply lp.ext; funext m
        rw [flipC_apply, lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply, lp.coeFn_smul, Pi.smul_apply,
          flipC_apply]
        split_ifs <;> simp [smul_eq_mul] }
    1 (fun z => by
      rw [one_mul]
      exact (norm_eq_of_coord _ _ fun m => by
        show ‖flipComplexCoordinate n z m‖ = ‖z m‖
        rw [flipC_apply]; split_ifs <;> simp).le)

theorem flipCLM_apply (n : ℤ) (z : ComplexDiagonalSpace) : flipCLM n z = flipComplexCoordinate n z := rfl

theorem norm_flipC (n : ℤ) (z : ComplexDiagonalSpace) : ‖flipComplexCoordinate n z‖ = ‖z‖ :=
  norm_eq_of_coord _ _ fun m => by rw [flipC_apply]; split_ifs <;> simp

theorem flipC_fix (n : ℤ) (z : ComplexDiagonalSpace) (hz : z n = 0) : flipComplexCoordinate n z = z := by
  apply lp.ext; funext m
  rw [flipC_apply]
  split_ifs with hm
  · subst hm; rw [hz, neg_zero]
  · rfl

theorem dist_flipC (n : ℤ) (z w : ComplexDiagonalSpace) :
    dist (flipComplexCoordinate n z) (flipComplexCoordinate n w) = dist z w := by
  rw [dist_eq_norm, dist_eq_norm, ← flipCLM_apply, ← flipCLM_apply, ← map_sub, flipCLM_apply, norm_flipC]

theorem flipC_diagC (n : ℤ) (y : RealDiagonalSpace) :
    flipComplexCoordinate n (diagC (y, 0)) = diagC (NlsGge.ThirdConsultation.G6036S.flipR n y, 0) := by
  apply lp.ext; funext m
  rw [flipC_apply, diagC_real_apply, diagC_real_apply, NlsGge.ThirdConsultation.G6036S.flipR_coe]
  split_ifs <;> push_cast <;> rfl

theorem norm_flipR (n : ℤ) (y : RealDiagonalSpace) : ‖NlsGge.ThirdConsultation.G6036S.flipR n y‖ = ‖y‖ :=
  norm_eq_of_coord _ _ fun m => by rw [NlsGge.ThirdConsultation.G6036S.flipR_coe]; split_ifs <;> simp

theorem dist_flipR (n : ℤ) (y y' : RealDiagonalSpace) :
    dist (NlsGge.ThirdConsultation.G6036S.flipR n y) (NlsGge.ThirdConsultation.G6036S.flipR n y') = dist y y' := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, norm_flipR]

theorem flipR_fix (n : ℤ) (y : RealDiagonalSpace) (hy : y n = 0) :
    NlsGge.ThirdConsultation.G6036S.flipR n y = y := by
  apply lp.ext; funext m
  rw [NlsGge.ThirdConsultation.G6036S.flipR_coe]
  split_ifs with hm
  · subst hm; rw [hy, neg_zero]
  · rfl

/-! ### Tail projection and head lift -/

theorem tail_apply (A : Finset ℤ) (y : ComplexDiagonalSpace) (m : ℤ) :
    complexTailProjection A y m = if m ∈ A then 0 else y m := by
  unfold complexTailProjection
  rw [lp.coeFn_sub, Pi.sub_apply, NlsGge.ThirdConsultation.G6039S.coe_finsum_single]
  split_ifs <;> ring

def tailCLM (A : Finset ℤ) : ComplexDiagonalSpace →L[ℂ] ComplexDiagonalSpace :=
  LinearMap.mkContinuous
    { toFun := complexTailProjection A
      map_add' := fun z w => by
        apply lp.ext; funext m
        rw [tail_apply, lp.coeFn_add, Pi.add_apply, lp.coeFn_add, Pi.add_apply, tail_apply, tail_apply]
        split_ifs <;> ring
      map_smul' := fun a z => by
        apply lp.ext; funext m
        rw [tail_apply, lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply, lp.coeFn_smul, Pi.smul_apply,
          tail_apply]
        split_ifs <;> simp [smul_eq_mul] }
    1 (fun z => by
      rw [one_mul]
      exact norm_le_of_coord _ _ fun m => by
        show ‖complexTailProjection A z m‖ ≤ ‖z m‖
        rw [tail_apply]; split_ifs <;> simp)

theorem tailCLM_apply (A : Finset ℤ) (z : ComplexDiagonalSpace) : tailCLM A z = complexTailProjection A z := rfl

theorem norm_tail_le (A : Finset ℤ) (z : ComplexDiagonalSpace) : ‖complexTailProjection A z‖ ≤ ‖z‖ :=
  norm_le_of_coord _ _ fun m => by rw [tail_apply]; split_ifs <;> simp

theorem head_apply (A : Finset ℤ) (p : A → ℂ) (m : ℤ) :
    complexHeadLift A p m = if h : m ∈ A then p ⟨m, h⟩ else 0 := by
  unfold complexHeadLift
  have hs := map_sum (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m) (fun k : A => lp.single 2 (k : ℤ) (p k)) Finset.univ
  have e : ∀ x : ComplexDiagonalSpace, lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m x = (x : ℤ → ℂ) m := fun x => rfl
  rw [e] at hs
  rw [hs]
  simp only [e, lp.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨m, h⟩ : A)]
    · simp
    · intro b _ hb
      have : (b : ℤ) ≠ m := fun hbm => hb (Subtype.ext hbm)
      simp [Pi.single_apply, Ne.symm this]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · refine Finset.sum_eq_zero (fun k _ => ?_)
    have : m ≠ (k : ℤ) := fun hmk => h (hmk ▸ k.2)
    simp [Pi.single_apply, this]

def headLin (A : Finset ℤ) : (A → ℂ) →ₗ[ℂ] ComplexDiagonalSpace where
  toFun := complexHeadLift A
  map_add' p q := by
    apply lp.ext; funext m
    rw [head_apply, lp.coeFn_add, Pi.add_apply, head_apply, head_apply]
    split_ifs <;> simp
  map_smul' a p := by
    apply lp.ext; funext m
    rw [head_apply, lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply, head_apply]
    split_ifs <;> simp

def headCLM (A : Finset ℤ) : (A → ℂ) →L[ℂ] ComplexDiagonalSpace :=
  LinearMap.toContinuousLinearMap (headLin A)

theorem headCLM_apply (A : Finset ℤ) (p : A → ℂ) : headCLM A p = complexHeadLift A p := rfl

/-! ### Real roots and real-to-complex action maps -/

theorem rootR_mem (I : PositiveActionSpace) : Memℓp (fun n : ℤ => Real.sqrt (I.val n)) 2 := by
  refine memℓp_gen ?_
  have he : (fun n : ℤ => ‖Real.sqrt (I.val n)‖ ^ (2 : ℝ≥0∞).toReal) = fun n => ‖I.val n‖ := by
    funext n
    rw [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (I.2 n),
      Real.norm_of_nonneg (I.2 n)]
  rw [he]
  have h := (lp.memℓp I.val).summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
  simpa only [ENNReal.toReal_one, Real.rpow_one] using h

def rootR (I : PositiveActionSpace) : RealDiagonalSpace := ⟨fun n => Real.sqrt (I.val n), rootR_mem I⟩

theorem rootR_apply (I : PositiveActionSpace) (n : ℤ) : rootR I n = Real.sqrt (I.val n) := rfl

theorem rootR_sq (I : PositiveActionSpace) (n : ℤ) : (rootR I n) ^ 2 = I.val n := by
  rw [rootR_apply, Real.sq_sqrt (I.2 n)]

theorem memℓp1_of_le {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f : ℤ → E) (g : ℤ → F) (hg : Memℓp g 1) (h : ∀ n, ‖f n‖ ≤ ‖g n‖) : Memℓp f 1 := by
  refine memℓp_gen ?_
  have hs := hg.summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
  exact Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => Real.rpow_le_rpow (norm_nonneg _) (h n) (by norm_num)) hs

theorem norm1_le_of_coord {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f : lp (fun _ : ℤ => E) 1) (g : lp (fun _ : ℤ => F) 1) (h : ∀ n, ‖f n‖ ≤ ‖g n‖) : ‖f‖ ≤ ‖g‖ := by
  have hf := lp.hasSum_norm (p := (1 : ℝ≥0∞)) (by norm_num) f
  have hg := lp.hasSum_norm (p := (1 : ℝ≥0∞)) (by norm_num) g
  simp only [ENNReal.toReal_one, Real.rpow_one] at hf hg
  exact hasSum_le h hf hg

def tailActFun (A : Finset ℤ) (J : WeightedActionSpace) : ComplexActionSpace :=
  ⟨fun m => if m ∈ A then 0 else ((J m : ℝ) : ℂ), memℓp1_of_le _ _ (lp.memℓp J) fun m => by
    split_ifs
    · simp
    · rw [Complex.norm_real]⟩

theorem tailActFun_apply (A : Finset ℤ) (J : WeightedActionSpace) (m : ℤ) :
    tailActFun A J m = if m ∈ A then 0 else ((J m : ℝ) : ℂ) := rfl

def tailAct (A : Finset ℤ) : WeightedActionSpace →L[ℝ] ComplexActionSpace :=
  LinearMap.mkContinuous
    { toFun := tailActFun A
      map_add' := fun J K => by
        apply lp.ext; funext m
        rw [tailActFun_apply, lp.coeFn_add, Pi.add_apply, lp.coeFn_add, Pi.add_apply, tailActFun_apply,
          tailActFun_apply]
        split_ifs <;> push_cast <;> ring
      map_smul' := fun a J => by
        apply lp.ext; funext m
        rw [tailActFun_apply, lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply, lp.coeFn_smul, Pi.smul_apply,
          tailActFun_apply]
        split_ifs <;> simp [Complex.real_smul] }
    1 (fun J => by
      rw [one_mul]
      exact norm1_le_of_coord _ _ fun m => by
        show ‖tailActFun A J m‖ ≤ ‖J m‖
        rw [tailActFun_apply]; split_ifs
        · simp
        · rw [Complex.norm_real])

theorem tailAct_apply (A : Finset ℤ) (J : WeightedActionSpace) (m : ℤ) :
    tailAct A J m = if m ∈ A then 0 else ((J m : ℝ) : ℂ) := rfl

def evalR (n : ℤ) : WeightedActionSpace →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (lp.evalCLM ℝ (fun _ : ℤ => ℝ) 1 n)

theorem evalR_apply (n : ℤ) (J : WeightedActionSpace) : evalR n J = ((J n : ℝ) : ℂ) := rfl

end
end NlsGge.ThirdConsultation.G6041S
