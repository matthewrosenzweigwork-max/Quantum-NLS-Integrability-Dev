/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license; see docs/licenses/TauCeti-Apache-2.0.txt.
Authors: The Tau Ceti contributors; adapted for this development.

Canonical complexification core adapted from
TauCeti/Analysis/Normed/Module/Complexification.lean, lines 81-354,
commit 95f09254dec44b756e90d78f20f93dc4d3572783.
Changes: Mathlib-only legacy import/header, project-local namespace, explicit
autoImplicit setting. The real Banach norm and module definitions are preserved.

UNCOMPILED AUTHOR CANDIDATE. Root owns the only compiler lane.
This packet supplies canonical complex Banach spaces; the generic analytic
extension-on-compact theorem is not claimed proved by this core.
-/
import Mathlib

set_option autoImplicit false
noncomputable section
open Set

namespace NlsGge.ThirdConsultation.Narrative.G07C

/-- The complexification `X ⊕ i X` of a real vector space `X`: an element with real part `re` and
imaginary part `im` stands for the formal sum `re + i im`. -/
@[ext]
structure Complexification (X : Type*) where
  /-- The real part of an element of the complexification. -/
  re : X
  /-- The imaginary part of an element of the complexification. -/
  im : X

namespace Complexification

section Module

variable {X : Type*}

instance [Zero X] : Zero (Complexification X) := ⟨⟨0, 0⟩⟩

instance [Add X] : Add (Complexification X) := ⟨fun z w ↦ ⟨z.re + w.re, z.im + w.im⟩⟩

instance [Neg X] : Neg (Complexification X) := ⟨fun z ↦ ⟨-z.re, -z.im⟩⟩

instance [Sub X] : Sub (Complexification X) := ⟨fun z w ↦ ⟨z.re - w.re, z.im - w.im⟩⟩

instance [SMul ℕ X] : SMul ℕ (Complexification X) := ⟨fun n z ↦ ⟨n • z.re, n • z.im⟩⟩

instance [SMul ℤ X] : SMul ℤ (Complexification X) := ⟨fun n z ↦ ⟨n • z.re, n • z.im⟩⟩

@[simp] theorem zero_re [Zero X] : (0 : Complexification X).re = 0 := (rfl)
@[simp] theorem zero_im [Zero X] : (0 : Complexification X).im = 0 := (rfl)
@[simp] theorem add_re [Add X] (z w : Complexification X) : (z + w).re = z.re + w.re := (rfl)
@[simp] theorem add_im [Add X] (z w : Complexification X) : (z + w).im = z.im + w.im := (rfl)
@[simp] theorem neg_re [Neg X] (z : Complexification X) : (-z).re = -z.re := (rfl)
@[simp] theorem neg_im [Neg X] (z : Complexification X) : (-z).im = -z.im := (rfl)
@[simp] theorem sub_re [Sub X] (z w : Complexification X) : (z - w).re = z.re - w.re := (rfl)
@[simp] theorem sub_im [Sub X] (z w : Complexification X) : (z - w).im = z.im - w.im := (rfl)

instance [AddCommGroup X] : AddCommGroup (Complexification X) :=
  Function.Injective.addCommGroup (fun z : Complexification X ↦ (z.re, z.im))
    (fun _ _ h ↦ by
      simp only [Prod.mk.injEq] at h
      exact Complexification.ext h.1 h.2)
    (rfl) (fun _ _ ↦ (rfl)) (fun _ ↦ (rfl)) (fun _ _ ↦ (rfl)) (fun _ _ ↦ (rfl))
    (fun _ _ ↦ (rfl))

/-- The embedding `x ↦ x + i 0` of a real vector space into its complexification. -/
def ofReal [Zero X] (x : X) : Complexification X := ⟨x, 0⟩

@[simp] theorem ofReal_re [Zero X] (x : X) : (ofReal x).re = x := (rfl)
@[simp] theorem ofReal_im [Zero X] (x : X) : (ofReal x).im = 0 := (rfl)

variable [AddCommGroup X] [Module ℝ X]

/-- Complex scalars act by `(a + b i) • (x + i y) = (a x - b y) + i (b x + a y)`. -/
instance : SMul ℂ (Complexification X) :=
  ⟨fun c z ↦ ⟨c.re • z.re - c.im • z.im, c.im • z.re + c.re • z.im⟩⟩

@[simp]
theorem smul_re (c : ℂ) (z : Complexification X) : (c • z).re = c.re • z.re - c.im • z.im :=
  (rfl)

@[simp]
theorem smul_im (c : ℂ) (z : Complexification X) : (c • z).im = c.im • z.re + c.re • z.im :=
  (rfl)

instance : Module ℂ (Complexification X) where
  one_smul z := by ext <;> simp
  mul_smul c d z := by ext <;> simp only [smul_re, smul_im, Complex.mul_re, Complex.mul_im] <;>
    module
  smul_zero c := by ext <;> simp
  smul_add c z w := by ext <;> simp only [smul_re, smul_im, add_re, add_im] <;> module
  add_smul c d z := by ext <;> simp only [smul_re, smul_im, add_re, add_im, Complex.add_re,
    Complex.add_im] <;> module
  zero_smul z := by ext <;> simp

/-- Real scalars act componentwise. -/
@[simp]
theorem real_smul_re (r : ℝ) (z : Complexification X) : (r • z).re = r • z.re := by
  simp [← Complex.coe_smul]

/-- Real scalars act componentwise. -/
@[simp]
theorem real_smul_im (r : ℝ) (z : Complexification X) : (r • z).im = r • z.im := by
  simp [← Complex.coe_smul]

/-- Every element of the complexification is `re + i im`. -/
theorem re_add_I_smul_im (z : Complexification X) :
    ofReal z.re + Complex.I • ofReal z.im = z := by
  ext <;> simp

/-- Complex-linear maps out of the complexification agree once they agree on real vectors. -/
theorem ext_ofReal {E : Type*} [AddCommGroup E] [Module ℂ E]
    {f g : Complexification X →ₗ[ℂ] E} (h : ∀ x, f (ofReal x) = g (ofReal x)) : f = g := by
  ext z
  rw [← re_add_I_smul_im z, map_add, map_add, map_smul, map_smul, h, h]

end Module

section Norm

variable {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]

/-- The Taylor seminorm `‖z‖ = ⨆ w ∈ 𝕋, ‖Re (w • z)‖` on the complexification. -/
instance : Norm (Complexification X) := ⟨fun z ↦ ⨆ w : Circle, ‖((w : ℂ) • z).re‖⟩

theorem norm_def (z : Complexification X) : ‖z‖ = ⨆ w : Circle, ‖((w : ℂ) • z).re‖ := (rfl)

/-- The real part of a scalar multiple is controlled by the two components. -/
private theorem norm_smul_re_le_aux (c : ℂ) (z : Complexification X) :
    ‖(c • z).re‖ ≤ ‖c‖ * (‖z.re‖ + ‖z.im‖) := by
  rw [smul_re, mul_add]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_smul] <;>
    gcongr <;> simp [Complex.abs_re_le_norm, Complex.abs_im_le_norm]

private theorem bddAbove_range_norm_smul_re (z : Complexification X) :
    BddAbove (range fun w : Circle ↦ ‖((w : ℂ) • z).re‖) :=
  ⟨‖z.re‖ + ‖z.im‖, by
    rintro _ ⟨w, rfl⟩
    simpa using norm_smul_re_le_aux (w : ℂ) z⟩

/-- The seminorm of the real part of every rotation is bounded by the Taylor seminorm. -/
theorem norm_circle_smul_re_le (w : Circle) (z : Complexification X) :
    ‖((w : ℂ) • z).re‖ ≤ ‖z‖ :=
  le_ciSup (bddAbove_range_norm_smul_re z) w

/-- The Taylor seminorm is the least bound on the real parts of all rotations. -/
theorem norm_le_iff {z : Complexification X} {r : ℝ} :
    ‖z‖ ≤ r ↔ ∀ w : Circle, ‖((w : ℂ) • z).re‖ ≤ r :=
  ciSup_le_iff (bddAbove_range_norm_smul_re z)

/-- The seminorm of the real part is at most the Taylor seminorm. -/
theorem norm_re_le (z : Complexification X) : ‖z.re‖ ≤ ‖z‖ := by
  simpa using norm_circle_smul_re_le 1 z

/-- The seminorm of the imaginary part is at most the Taylor seminorm. -/
theorem norm_im_le (z : Complexification X) : ‖z.im‖ ≤ ‖z‖ := by
  have h := norm_circle_smul_re_le ⟨-Complex.I, by simp [Submonoid.unitSphere]⟩ z
  simpa using h

/-- The Taylor seminorm is at most the sum of the seminorms of the two components. -/
theorem norm_le_norm_re_add_norm_im (z : Complexification X) : ‖z‖ ≤ ‖z.re‖ + ‖z.im‖ :=
  norm_le_iff.2 fun w ↦ by simpa using norm_smul_re_le_aux (w : ℂ) z

/-- The seminorm of the real part of a complex multiple is bounded by the scalar norm times
the Taylor seminorm. -/
theorem norm_smul_re_le (c : ℂ) (z : Complexification X) : ‖(c • z).re‖ ≤ ‖c‖ * ‖z‖ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hnorm : (0 : ℝ) < ‖c‖ := norm_pos_iff.2 hc
  let u : Circle := ⟨c / (‖c‖ : ℂ), by
    simp [Submonoid.unitSphere, hnorm.ne']⟩
  have hu : ((‖c‖ : ℝ) : ℂ) * (u : ℂ) = c :=
    mul_div_cancel₀ c (Complex.ofReal_ne_zero.2 hnorm.ne')
  have hcu : c • z = ‖c‖ • ((u : ℂ) • z) := by
    rw [← Complex.coe_smul, smul_smul]
    exact congrArg (· • z) hu.symm
  rw [hcu, real_smul_re, norm_smul, Real.norm_of_nonneg hnorm.le]
  exact mul_le_mul_of_nonneg_left (norm_circle_smul_re_le u z) hnorm.le

private theorem norm_nonneg' (z : Complexification X) : 0 ≤ ‖z‖ :=
  (norm_nonneg z.re).trans (norm_re_le z)

@[simp]
theorem norm_ofReal (x : X) : ‖ofReal x‖ = ‖x‖ :=
  le_antisymm ((norm_le_norm_re_add_norm_im _).trans (by simp)) (by
    simpa using norm_re_le (ofReal x))

/-- The Taylor seminorm satisfies the axioms of a complex seminormed space. -/
theorem seminormedSpaceCore : SeminormedSpace.Core ℂ (Complexification X) where
  norm_nonneg := norm_nonneg'
  norm_smul c z := by
    have hle : ∀ (c : ℂ) (z : Complexification X), ‖c • z‖ ≤ ‖c‖ * ‖z‖ := fun c z ↦
      norm_le_iff.2 fun w ↦ by
        rw [smul_smul]
        simpa using norm_smul_re_le ((w : ℂ) * c) z
    refine le_antisymm (hle c z) ?_
    rcases eq_or_ne c 0 with rfl | hc
    · simpa using norm_nonneg' (0 : Complexification X)
    calc ‖c‖ * ‖z‖ = ‖c‖ * ‖c⁻¹ • c • z‖ := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ ≤ ‖c‖ * (‖c⁻¹‖ * ‖c • z‖) := by
        gcongr
        exact hle _ _
      _ = ‖c • z‖ := by rw [norm_inv, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.2 hc),
          one_mul]
  norm_triangle z w := norm_le_iff.2 fun u ↦ by
    rw [smul_add, add_re]
    exact (norm_add_le _ _).trans (add_le_add (norm_circle_smul_re_le u z)
      (norm_circle_smul_re_le u w))
instance instSeminormedAddCommGroup : SeminormedAddCommGroup (Complexification X) :=
  SeminormedAddCommGroup.ofCore seminormedSpaceCore

/-- The complexification carries the complex seminormed space structure from its Taylor seminorm. -/
instance instNormedSpace : NormedSpace ℂ (Complexification X) where
  norm_smul_le c z := (seminormedSpaceCore.norm_smul c z).le

variable (X)

/-- The real part, as a bounded real-linear map of norm at most one. -/
def reCLM : Complexification X →L[ℝ] X :=
  LinearMap.mkContinuous
    { toFun := re
      map_add' := add_re
      map_smul' := real_smul_re } 1 fun z ↦ by simpa using norm_re_le z

/-- The imaginary part, as a bounded real-linear map of norm at most one. -/
def imCLM : Complexification X →L[ℝ] X :=
  LinearMap.mkContinuous
    { toFun := im
      map_add' := add_im
      map_smul' := real_smul_im } 1 fun z ↦ by simpa using norm_im_le z

/-- The real embedding, as a real-linear isometry. -/
def ofRealLI : X →ₗᵢ[ℝ] Complexification X where
  toFun := ofReal
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp
  norm_map' := norm_ofReal

variable {X}

@[simp] theorem reCLM_apply (z : Complexification X) : reCLM X z = z.re := (rfl)
@[simp] theorem imCLM_apply (z : Complexification X) : imCLM X z = z.im := (rfl)
@[simp] theorem ofRealLI_apply (x : X) : ofRealLI X x = ofReal x := (rfl)

variable (X)

/-- Taking real parts undoes the real embedding. -/
@[simp]
theorem reCLM_comp_ofRealLI :
    reCLM X ∘L (ofRealLI X).toContinuousLinearMap = ContinuousLinearMap.id ℝ X := by
  ext x
  simp

/-- The complexification is real-linearly homeomorphic to `X × X` via `z ↦ (re z, im z)`. -/
def equivProd : Complexification X ≃L[ℝ] X × X :=
  LinearEquiv.toContinuousLinearEquivOfBounds
    { toFun := fun z ↦ (z.re, z.im)
      invFun := fun p ↦ ⟨p.1, p.2⟩
      map_add' := fun _ _ ↦ (rfl)
      map_smul' := fun r z ↦ by ext <;> simp
      left_inv := fun _ ↦ (rfl)
      right_inv := fun _ ↦ (rfl) } 1 2
    (fun z ↦ by simpa using ⟨norm_re_le z, norm_im_le z⟩)
    (fun p ↦ by
      refine (norm_le_norm_re_add_norm_im (⟨p.1, p.2⟩ : Complexification X)).trans ?_
      have h1 : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
      have h2 : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
      dsimp only
      linarith)

variable {X}

@[simp]
theorem equivProd_apply (z : Complexification X) : equivProd X z = (z.re, z.im) := (rfl)

@[simp]
theorem equivProd_symm_apply (p : X × X) : (equivProd X).symm p = ⟨p.1, p.2⟩ := (rfl)

/-- The complexification is complete whenever the original real seminormed space is complete. -/
instance instCompleteSpace [CompleteSpace X] : CompleteSpace (Complexification X) :=
  ((equivProd X).isUniformEmbedding.isUniformInducing.completeSpace_congr
    (equivProd X).surjective).2 inferInstance

end Norm

/-- The Taylor seminorm is a norm when the original real seminorm is a norm. -/
instance instNormedAddCommGroup {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedAddCommGroup (Complexification X) where
  eq_of_dist_eq_zero {z w} h := by
    rw [dist_eq_norm] at h
    ext
    · exact sub_eq_zero.1 (norm_le_zero_iff.1 (h ▸ norm_re_le (z - w)))
    · exact sub_eq_zero.1 (norm_le_zero_iff.1 (h ▸ norm_im_le (z - w)))

end Complexification

end NlsGge.ThirdConsultation.Narrative.G07C

/- G07C second diagnostic repair 04. All spaces below use the fixed canonical
circle-sup complexification constructed in PRODUCTION01. No new structure
assumption on a complexification is accepted as a parameter. -/

namespace NlsGge.ThirdConsultation.Narrative.G07C

open scoped BigOperators NNReal ENNReal
open Complexification

section Lift

variable {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Extend a bounded real map into an already complex space by `T x + i T y`. -/
def liftReal (T : X →L[ℝ] V) : Complexification X →L[ℂ] V where
  toFun z := T z.re + Complex.I • T z.im
  map_add' z w := by
    simp only [Complexification.add_re, Complexification.add_im, map_add, smul_add]
    abel
  map_smul' c z := by
    change T (c.re • z.re - c.im • z.im) +
      Complex.I • T (c.im • z.re + c.re • z.im) =
        c • (T z.re + Complex.I • T z.im)
    simp only [map_sub, map_add, map_smul, RingHom.id_apply, ← Complex.coe_smul]
    conv_rhs => rw [← Complex.re_add_im c]
    have hsmul (a b : ℂ) (v : V) : a • b • v = (a * b) • v :=
      smul_smul a b v
    simp only [add_smul, smul_add, smul_sub, hsmul, mul_assoc,
      Complex.I_mul_I, neg_smul, one_smul]
    match_scalars <;> ring_nf <;>
      (try simp only [Complex.I_mul_I, Complex.I_sq, mul_neg, mul_one]) <;> ring
  cont := (T.continuous.comp (reCLM X).continuous).add
    ((T.continuous.comp (imCLM X).continuous).const_smul Complex.I)

@[simp] theorem liftReal_apply (T : X →L[ℝ] V) (z : Complexification X) :
    liftReal T z = T z.re + Complex.I • T z.im := rfl

@[simp] theorem liftReal_ofReal (T : X →L[ℝ] V) (x : X) :
    liftReal T (ofReal x) = T x := by
  simp only [liftReal_apply, ofReal_re, ofReal_im, map_zero, smul_zero, add_zero]

theorem norm_liftReal_le (T : X →L[ℝ] V) : ‖liftReal T‖ ≤ 2 * ‖T‖ := by
  refine ContinuousLinearMap.opNorm_le_bound (liftReal T) (by positivity) ?_
  intro z
  calc
    ‖liftReal T z‖ ≤ ‖T z.re‖ + ‖Complex.I • T z.im‖ := norm_add_le _ _
    _ = ‖T z.re‖ + ‖T z.im‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
    _ ≤ ‖T‖ * ‖z.re‖ + ‖T‖ * ‖z.im‖ := add_le_add (T.le_opNorm _) (T.le_opNorm _)
    _ ≤ (2 * ‖T‖) * ‖z‖ := by
      have h1 := mul_le_mul_of_nonneg_left (norm_re_le z) (norm_nonneg T)
      have h2 := mul_le_mul_of_nonneg_left (norm_im_le z) (norm_nonneg T)
      linarith

/-- Real-linear dependence of the complex-linear lift on its original real map. -/
def liftRealL : (X →L[ℝ] V) →L[ℝ] (Complexification X →L[ℂ] V) :=
  LinearMap.mkContinuous
    { toFun := liftReal
      map_add' := fun T S => by
        ext z
        simp only [liftReal_apply, ContinuousLinearMap.add_apply, smul_add]
        abel
      map_smul' := fun r T => by
        ext z
        simp only [liftReal_apply, ContinuousLinearMap.smul_apply, RingHom.id_apply]
        rw [smul_add, smul_comm r Complex.I] }
    2 norm_liftReal_le

@[simp] theorem liftRealL_apply (T : X →L[ℝ] V) : liftRealL T = liftReal T := rfl

end Lift

section Multilinear

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Complexify every argument by recursion through the genuine curry isometries. -/
def complexifyMultilinear : (n : ℕ) →
    ContinuousMultilinearMap ℝ (fun _ : Fin n => X) Y →L[ℝ]
      ContinuousMultilinearMap ℂ (fun _ : Fin n => Complexification X) (Complexification Y)
  | 0 =>
    let ec := continuousMultilinearCurryFin0 ℂ (Complexification X) (Complexification Y)
    let er := continuousMultilinearCurryFin0 ℝ X Y
    ((ec.symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ).comp
      ((ofRealLI Y).toContinuousLinearMap.comp er.toContinuousLinearEquiv.toContinuousLinearMap)
  | n + 1 =>
    let ec := continuousMultilinearCurryLeftEquiv ℂ
      (fun _ : Fin (n + 1) => Complexification X) (Complexification Y)
    let er := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => X) Y
    ((ec.symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ).comp
      (liftRealL.comp
        ((ContinuousLinearMap.compL ℝ X
            (ContinuousMultilinearMap ℝ (fun _ : Fin n => X) Y)
            (ContinuousMultilinearMap ℂ (fun _ : Fin n => Complexification X) (Complexification Y))
            (complexifyMultilinear n)).comp er.toContinuousLinearEquiv.toContinuousLinearMap))

theorem complexifyMultilinear_zero
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => X) Y) :
    complexifyMultilinear 0 p =
      ContinuousMultilinearMap.uncurry0 ℂ (Complexification X) (ofReal (p 0)) := by
  ext v <;> rfl

theorem complexifyMultilinear_succ (n : ℕ)
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => X) Y) :
    complexifyMultilinear (n + 1) p =
      (liftReal ((complexifyMultilinear n).comp p.curryLeft)).uncurryLeft := by
  ext v <;> rfl

theorem complexifyMultilinear_norm_le : ∀ (n : ℕ)
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => X) Y),
    ‖complexifyMultilinear n p‖ ≤ (2 : ℝ) ^ n * ‖p‖
  | 0, p => by
    simpa only [complexifyMultilinear_zero, ContinuousMultilinearMap.uncurry0_norm,
      norm_ofReal, ContinuousMultilinearMap.fin0_apply_norm, pow_zero, one_mul] using
      (le_rfl : ‖p‖ ≤ ‖p‖)
  | n + 1, p => by
    have hc : ‖(complexifyMultilinear n).comp p.curryLeft‖ ≤ (2 : ℝ) ^ n * ‖p‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
      intro x
      calc
        ‖complexifyMultilinear n (p.curryLeft x)‖ ≤ (2 : ℝ) ^ n * ‖p.curryLeft x‖ :=
          complexifyMultilinear_norm_le n _
        _ ≤ (2 : ℝ) ^ n * (‖p.curryLeft‖ * ‖x‖) :=
          mul_le_mul_of_nonneg_left (p.curryLeft.le_opNorm x) (by positivity)
        _ = ((2 : ℝ) ^ n * ‖p‖) * ‖x‖ := by
          rw [ContinuousMultilinearMap.curryLeft_norm, mul_assoc]
    rw [complexifyMultilinear_succ, ContinuousLinearMap.uncurryLeft_norm]
    calc
      ‖liftReal ((complexifyMultilinear n).comp p.curryLeft)‖ ≤
          2 * ‖(complexifyMultilinear n).comp p.curryLeft‖ := norm_liftReal_le _
      _ ≤ 2 * ((2 : ℝ) ^ n * ‖p‖) := mul_le_mul_of_nonneg_left hc (by norm_num)
      _ = (2 : ℝ) ^ (n + 1) * ‖p‖ := by rw [pow_succ]; ring

theorem complexifyMultilinear_ofReal : ∀ (n : ℕ)
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => X) Y) (v : Fin n → X),
    complexifyMultilinear n p (fun i => ofReal (v i)) = ofReal (p v)
  | 0, p, v => by
    rw [complexifyMultilinear_zero, ContinuousMultilinearMap.uncurry0_apply]
    congr 1
    exact congrArg p (Subsingleton.elim _ _)
  | n + 1, p, v => by
    rw [complexifyMultilinear_succ, ContinuousLinearMap.uncurryLeft_apply]
    change liftReal ((complexifyMultilinear n).comp p.curryLeft) (ofReal (v 0))
      (fun i => ofReal (v i.succ)) = _
    rw [liftReal_ofReal, ContinuousLinearMap.comp_apply,
      complexifyMultilinear_ofReal n, ContinuousMultilinearMap.curryLeft_apply]
    exact congrArg (fun w => ofReal (p w)) (Fin.cons_self_tail v)

/-- Termwise extension on the canonical Banach complexifications. -/
def complexifySeries (p : FormalMultilinearSeries ℝ X Y) :
    FormalMultilinearSeries ℂ (Complexification X) (Complexification Y) :=
  fun n => complexifyMultilinear n (p n)

theorem complexifySeries_norm_le (p : FormalMultilinearSeries ℝ X Y) (n : ℕ) :
    ‖complexifySeries p n‖ ≤ (2 : ℝ) ^ n * ‖p n‖ :=
  complexifyMultilinear_norm_le n (p n)

theorem complexifySeries_ofReal (p : FormalMultilinearSeries ℝ X Y)
    (n : ℕ) (v : Fin n → X) :
    complexifySeries p n (fun i => ofReal (v i)) = ofReal (p n v) :=
  complexifyMultilinear_ofReal n (p n) v

/-- Shrinking the power-series radius by a fixed factor two suffices. -/
theorem le_radius_complexifySeries (p : FormalMultilinearSeries ℝ X Y) {r : ℝ≥0}
    (hr : ((2 * r : ℝ≥0) : ℝ≥0∞) < p.radius) :
    (r : ℝ≥0∞) ≤ (complexifySeries p).radius := by
  apply FormalMultilinearSeries.le_radius_of_summable
  have hs := p.summable_norm_mul_pow hr
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ hs
  intro n
  calc
    ‖complexifySeries p n‖ * (r : ℝ) ^ n ≤
        ((2 : ℝ) ^ n * ‖p n‖) * (r : ℝ) ^ n :=
      mul_le_mul_of_nonneg_right (complexifySeries_norm_le p n) (by positivity)
    _ = ‖p n‖ * ((2 * r : ℝ≥0) : ℝ) ^ n := by
      simp [mul_pow]
      <;> ring

end Multilinear

end NlsGge.ThirdConsultation.Narrative.G07C

/- Exact quantitative series transfer on the fixed canonical Banach
complexifications. Root owns compilation; no new arbitrary structures. -/

namespace NlsGge.ThirdConsultation.Narrative.G07C

open Complexification Filter Metric Set
open scoped NNReal ENNReal Topology

/-- The canonical complexification of a real Banach space is Banach. The
instance is already proved through equivProd in the checked core. -/
theorem completeSpace_complexification (X : Type*) [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] : CompleteSpace (Complexification X) :=
  inferInstance

section Local

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- The coefficient bound of the checked block gives the exact half-radius
lower bound, including infinite radius. -/
theorem half_radius_le_complexifySeries (p : FormalMultilinearSeries ℝ X Y) :
    p.radius / 2 ≤ (complexifySeries p).radius := by
  apply ENNReal.le_of_forall_nnreal_lt
  intro r hr
  apply le_radius_complexifySeries p
  have h : (r : ℝ≥0∞) * 2 < p.radius :=
    (ENNReal.lt_div_iff_mul_lt (a := p.radius) (b := 2) (c := (r : ℝ≥0∞))
      (Or.inl (by norm_num)) (Or.inl (by norm_num))).1 hr
  simpa [mul_comm] using h

/-- A convergent real series is sent to its genuine embedded sum. -/
theorem complexifySeries_hasSum_ofReal (p : FormalMultilinearSeries ℝ X Y)
    (x : X) (y : Y) (h : HasSum (fun n => p n (fun _ => x)) y) :
    HasSum (fun n => complexifySeries p n (fun _ => ofReal x)) (ofReal y) := by
  have hm := (ofRealLI Y).toContinuousLinearMap.hasSum h
  change HasSum (fun n => ofReal (p n (fun _ => x))) (ofReal y) at hm
  simpa only [complexifySeries_ofReal] using hm

/-- Transfer the original real expansion at a to a genuine complex expansion
at ofReal a, on the ball of radius R/2. -/
theorem hasFPowerSeriesOnBall_complexify {F : X → Y}
    {p : FormalMultilinearSeries ℝ X Y} {a : X} {R : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall F p a R) :
    HasFPowerSeriesOnBall
      (fun z => (complexifySeries p).sum (z - ofReal a))
      (complexifySeries p) (ofReal a) (R / 2) := by
  let q := complexifySeries p
  have hRpos : 0 < R / 2 := ENNReal.div_pos hp.r_pos.ne' (by norm_num)
  have hRq : R / 2 ≤ q.radius :=
    (ENNReal.div_le_div_right hp.r_le 2).trans (half_radius_le_complexifySeries p)
  have hqpos : 0 < q.radius := hRpos.trans_le hRq
  simpa only [zero_add] using
    (((q.hasFPowerSeriesOnBall hqpos).mono hRpos hRq).comp_sub (ofReal a))

/-- The complex extension agrees with the original real function throughout
the real ball on which the transferred series is asserted. -/
theorem complexifySeries_sum_ofReal_of_mem {F : X → Y}
    {p : FormalMultilinearSeries ℝ X Y} {a y : X} {R : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall F p a R) (hy : y ∈ eball a (R / 2)) :
    (complexifySeries p).sum (ofReal y - ofReal a) = ofReal (F y) := by
  have hhalf : R / 2 ≤ R := by
    simpa only [div_one] using
      ENNReal.div_le_div_left (by norm_num : (1 : ℝ≥0∞) ≤ 2) R
  have hyR : y ∈ eball a R := Metric.eball_subset_eball hhalf hy
  have hd : edist (ofReal y) (ofReal a) = edist y a :=
    (ofRealLI X).isometry.edist_eq _ _
  have hyc : ofReal y ∈ eball (ofReal a) (R / 2) := by
    change edist (ofReal y) (ofReal a) < R / 2
    rw [hd]
    exact hy
  have hsum := (hasFPowerSeriesOnBall_complexify hp).hasSum_sub hyc
  have hsub : ofReal y - ofReal a = ofReal (y - a) :=
    ((ofRealLI X).map_sub y a).symm
  rw [hsub] at hsum ⊢
  exact hsum.unique (complexifySeries_hasSum_ofReal p (y - a) (F y) (hp.hasSum_sub hyR))

/-- A real analytic germ has a holomorphic extension on a real-centred complex
ball, agreeing with the original function throughout the real ball. -/
theorem exists_complexification_on_ball {F : X → Y} {a : X}
    (hF : AnalyticAt ℝ F a) :
    ∃ r : ℝ, 0 < r ∧ ∃ FC : Complexification X → Complexification Y,
      AnalyticOnNhd ℂ FC (ball (ofReal a) r) ∧
      ∀ y ∈ ball a r, FC (ofReal y) = ofReal (F y) := by
  rcases hF with ⟨p, R, hp⟩
  have hC := hasFPowerSeriesOnBall_complexify hp
  obtain ⟨r, hr0, hrR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hC.r_pos
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (ENNReal.coe_pos.1 hr0)
  refine ⟨(r : ℝ), hrpos, fun z => (complexifySeries p).sum (z - ofReal a), ?_, ?_⟩
  · intro z hz
    apply hC.analyticOnNhd z
    apply Metric.eball_subset_eball hrR.le
    simpa only [Metric.eball_coe] using hz
  · intro y hy
    apply complexifySeries_sum_ofReal_of_mem hp
    apply Metric.eball_subset_eball hrR.le
    simpa only [Metric.eball_coe] using hy

end Local

end NlsGge.ThirdConsultation.Narrative.G07C

/- Generic real-Banach overlap uniqueness and gluing continuation. The
complexification is the fixed canonical one, with no additional instances. -/

namespace NlsGge.ThirdConsultation.Narrative.G07C

open Complexification Filter Metric Set
open scoped Topology

section Glue

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [hX : CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

theorem re_mem_real_ball {z : Complexification X} {a : X} {r : ℝ}
    (hz : z ∈ ball (ofReal a) r) : z.re ∈ ball a r := by
  rw [mem_ball, dist_eq_norm] at hz ⊢
  have h := norm_re_le (z - ofReal a)
  simpa only [sub_re, ofReal_re] using h.trans_lt hz

theorem ofReal_re_mem_ball {z : Complexification X} {a : X} {r : ℝ}
    (hz : z ∈ ball (ofReal a) r) : ofReal z.re ∈ ball (ofReal a) r := by
  have h := re_mem_real_ball hz
  have hd : dist (ofReal z.re) (ofReal a) = dist z.re a :=
    (ofRealLI X).isometry.dist_eq _ _
  change dist (ofReal z.re) (ofReal a) < r
  rw [hd]
  exact h

/-- Two holomorphic maps on real-centred balls agree on their overlap as
soon as their real restrictions agree. Reduction is to a single complex
line through Re(z), not to a finite-dimensional hypothesis on X. -/
theorem eqOn_inter_ball_of_eqOn_real
    {FC GC : Complexification X → Complexification Y} {a b : X} {r s : ℝ}
    (hF : AnalyticOnNhd ℂ FC (ball (ofReal a) r))
    (hG : AnalyticOnNhd ℂ GC (ball (ofReal b) s))
    (hreal : ∀ y ∈ ball a r ∩ ball b s, FC (ofReal y) = GC (ofReal y)) :
    EqOn FC GC (ball (ofReal a) r ∩ ball (ofReal b) s) := by
  intro z hz
  let W : Set (Complexification X) := ball (ofReal a) r ∩ ball (ofReal b) s
  let L : ℂ → Complexification X := fun t => ofReal z.re + t • ofReal z.im
  let D : Set ℂ := L ⁻¹' W
  have hw : z.re ∈ ball a r ∩ ball b s :=
    ⟨re_mem_real_ball hz.1, re_mem_real_ball hz.2⟩
  have hwc : ofReal z.re ∈ W :=
    ⟨ofReal_re_mem_ball hz.1, ofReal_re_mem_ball hz.2⟩
  let l : ℂ →L[ℂ] Complexification X :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (ofReal z.im)
  let A : ℂ →ᵃ[ℝ] Complexification X :=
    AffineMap.const ℝ ℂ (ofReal z.re) +
      (l.restrictScalars ℝ).toLinearMap.toAffineMap
  have hconv : Convex ℝ D := by
    change Convex ℝ (A ⁻¹' W)
    exact Convex.affine_preimage A ((convex_ball _ _).inter (convex_ball _ _))
  have h0 : (0 : ℂ) ∈ D := by
    change ofReal z.re + (0 : ℂ) • ofReal z.im ∈ W
    simpa only [zero_smul, add_zero] using hwc
  have hL : ∀ t : ℂ, AnalyticAt ℂ L t := fun _ =>
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hFl : AnalyticOnNhd ℂ (FC ∘ L) D := fun t ht =>
    (hF (L t) ht.1).comp (hL t)
  have hGl : AnalyticOnNhd ℂ (GC ∘ L) D := fun t ht =>
    (hG (L t) ht.2).comp (hL t)
  have hLreal (t : ℝ) : L (t : ℂ) = ofReal (z.re + t • z.im) := by
    ext <;> simp [L, ofReal, smul_re, smul_im]
  have hc : Continuous (fun t : ℝ => z.re + t • z.im) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have ht : Tendsto (fun t : ℝ => z.re + t • z.im) (𝓝 (0 : ℝ)) (𝓝 z.re) := by
    simpa only [zero_smul, add_zero] using hc.tendsto (0 : ℝ)
  have he : ∀ᶠ t : ℝ in 𝓝 0, (FC ∘ L) (t : ℂ) = (GC ∘ L) (t : ℂ) := by
    filter_upwards [ht.eventually ((isOpen_ball.inter isOpen_ball).mem_nhds hw)] with t h
    change FC (L (t : ℂ)) = GC (L (t : ℂ))
    rw [hLreal]
    exact hreal _ h
  have hcast : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
    apply Filter.Tendsto.inf
    · simpa using Complex.continuous_ofReal.tendsto (0 : ℝ)
    · exact tendsto_principal_principal.2 (fun t ht' => by simpa using ht')
  have hfreq : ∃ᶠ t : ℝ in 𝓝[≠] 0, (FC ∘ L) (t : ℂ) = (GC ∘ L) (t : ℂ) :=
    (he.filter_mono nhdsWithin_le_nhds).frequently
  have heq := hFl.eqOn_of_preconnected_of_frequently_eq hGl hconv.isPreconnected h0
    (hcast.frequently hfreq)
  have hLI : L Complex.I = z := re_add_I_smul_im z
  have hI : Complex.I ∈ D := by
    change L Complex.I ∈ W
    rw [hLI]
    exact hz
  have hz' := heq hI
  change FC (L Complex.I) = GC (L Complex.I) at hz'
  simpa only [hLI] using hz'

/-- Compatible real-centred local extensions glue on an open complex
neighbourhood of the original real domain. -/
theorem exists_complexification_on_open {O : Set X} (hO : IsOpen O) (F : X → Y)
    (hF : AnalyticOnNhd ℝ F O) :
    ∃ U : Set (Complexification X), IsOpen U ∧
      (∀ x ∈ O, ofReal x ∈ U) ∧
      ∃ FC : Complexification X → Complexification Y,
        AnalyticOnNhd ℂ FC U ∧ (∀ x ∈ O, FC (ofReal x) = ofReal (F x)) := by
  classical
  have hlocal (x : O) := exists_complexification_on_ball (hF x x.2)
  choose r hr G hG hGr using hlocal
  have hagree (x y : O) : EqOn (G x) (G y)
      (ball (ofReal (x : X)) (r x) ∩ ball (ofReal (y : X)) (r y)) :=
    eqOn_inter_ball_of_eqOn_real (hG x) (hG y) fun v hv => by
      rw [hGr x v hv.1, hGr y v hv.2]
  let U : Set (Complexification X) := ⋃ x : O, ball (ofReal (x : X)) (r x)
  let FC : Complexification X → Complexification Y := fun z =>
    if hz : z ∈ U then G (mem_iUnion.1 hz).choose z else 0
  have hFC (x : O) {z : Complexification X} (hz : z ∈ ball (ofReal (x : X)) (r x)) :
      FC z = G x z := by
    have hu : z ∈ U := mem_iUnion.2 ⟨x, hz⟩
    simp only [FC, hu, ↓reduceDIte]
    exact hagree _ _ ⟨(mem_iUnion.1 hu).choose_spec, hz⟩
  refine ⟨U, isOpen_iUnion fun _ => isOpen_ball, ?_, FC, ?_, ?_⟩
  · intro x hx
    exact mem_iUnion.2 ⟨⟨x, hx⟩, mem_ball_self (hr _)⟩
  · intro z hz
    obtain ⟨x, hx⟩ := mem_iUnion.1 hz
    exact (hG x z hx).congr
      (eventually_of_mem (isOpen_ball.mem_nhds hx) fun z' hz' => (hFC x hz').symm)
  · intro x hx
    rw [hFC ⟨x, hx⟩ (mem_ball_self (hr _)), hGr ⟨x, hx⟩ x (mem_ball_self (hr _))]

include hX in
/-- The source complexification extension lemma for arbitrary real Banach spaces. -/
theorem exists_complexification_extension_on_compact
    {O : Set X} (hO : IsOpen O) (F : X → Y)
    (hF : AnalyticOnNhd ℝ F O) (K : Set X)
    (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ U : Set (Complexification X), IsOpen U ∧
      (∀ x ∈ K, ofReal x ∈ U) ∧
      ∃ FC : Complexification X → Complexification Y,
        AnalyticOnNhd ℂ FC U ∧
        (∀ x ∈ K, FC (ofReal x) = ofReal (F x)) := by
  obtain ⟨U, hU, hOU, FC, hFC, hreal⟩ := exists_complexification_on_open hO F hF
  exact ⟨U, hU, fun x hx => hOU x (hKO hx), FC, hFC,
    fun x hx => hreal x (hKO hx)⟩

end Glue

end NlsGge.ThirdConsultation.Narrative.G07C
