import QuantumNLS.Ext025LGP03
import QuantumNLS.HolomorphicStageD3
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# EXT-025 GP-03 complexification fix, part 1: the genuine complexification datum

Printed hypothesis (FINAL_EXTERNAL_THEOREM_INSTANCES.json, sha256
82876b0400535292c74c814f70269d4dea6778fb05d4d3066b73e8a3d0d13782, instance
`FIN-EXT025-GP-03`): "For the analytic version, the real map admits a holomorphic
complexification on a neighborhood. The inverse of its real derivative complexifies to a
bounded inverse. The relevant field or contour variables lie in a smaller common
neighborhood."

Reading of "complexification" (stated explicitly and minimally; this is the standard
topological notion).  A complex Banach space `XC` is a complexification of the real Banach
space `X`, via a continuous real-linear map `ι : X →L[ℝ] XC`, iff
`(x, y) ↦ ι x + i • ι y` is a topological real-linear isomorphism `(X × X) ≃L[ℝ] XC`
(`IsComplexification ι`).  Equivalent standard descriptions are proved below:
`ι` is injective (a closed real-linear embedding), the real part `re` and imaginary part `im`
are continuous real-linear, `re (ι x) = x`, `im (ι x) = 0`, `ι (re z) + i • ι (im z) = z`
(so `XC = ι X ⊕ i • ι X`, the complex span of `ι X` is `XC` and `ι X ∩ i ι X = 0`), and
`conj z := ι (re z) - i • ι (im z)` is a conjugate-linear involution of `XC` whose fixed
points are exactly `ι X`.  No isometry or particular norm is demanded (any norm on `XC`
making the decomposition a topological isomorphism is allowed; analyticity is invariant
under equivalent norms).  The real part of the target is NOT an extra datum: it is derived.

Complex Banach spaces are NOT forced into a common universe: an adapter
`analyticAt_gen` lifts through `ULift` to the frozen same-universe bridge
`HolomorphicStageD3.analyticAt_of_differentiableOn`.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Set Filter Topology

namespace QuantumNLS.Ext025GP03Cx

universe v1 v2

section Datum
variable {X XC : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup XC] [NormedSpace ℂ XC]

/-- `XC` is a (topological) complexification of `X` along the real-linear embedding `ι`. -/
def IsComplexification (ι : X →L[ℝ] XC) : Prop :=
  ∃ Φ : (X × X) ≃L[ℝ] XC, ∀ x y, Φ (x, y) = ι x + Complex.I • ι y

namespace IsComplexification
variable {ι : X →L[ℝ] XC} (h : IsComplexification ι)
include h

/-- Real part. -/
def re : XC →L[ℝ] X :=
  (ContinuousLinearMap.fst ℝ X X).comp (h.choose.symm : XC →L[ℝ] X × X)

/-- Imaginary part. -/
def im : XC →L[ℝ] X :=
  (ContinuousLinearMap.snd ℝ X X).comp (h.choose.symm : XC →L[ℝ] X × X)

theorem symm_decomp (a b : X) : h.choose.symm (ι a + Complex.I • ι b) = (a, b) := by
  rw [← h.choose_spec a b]; simp

theorem re_decomp (a b : X) : h.re (ι a + Complex.I • ι b) = a := by
  simp [re, h.symm_decomp]

theorem im_decomp (a b : X) : h.im (ι a + Complex.I • ι b) = b := by
  simp [im, h.symm_decomp]

theorem decomp (z : XC) : ι (h.re z) + Complex.I • ι (h.im z) = z := by
  have e := h.choose_spec (h.re z) (h.im z)
  have e2 : h.choose (h.re z, h.im z) = z := by
    show h.choose ((h.choose.symm z).1, (h.choose.symm z).2) = z
    simp
  rw [← e, e2]

theorem re_ι (x : X) : h.re (ι x) = x := by
  simpa using h.re_decomp x 0

theorem im_ι (x : X) : h.im (ι x) = 0 := by
  simpa using h.im_decomp x 0

theorem re_I_ι (x : X) : h.re (Complex.I • ι x) = 0 := by
  simpa using h.re_decomp 0 x

theorem im_I_ι (x : X) : h.im (Complex.I • ι x) = x := by
  simpa using h.im_decomp 0 x

/-- The embedding is injective. -/
theorem injective : Function.Injective ι := fun x y hxy => by
  rw [← h.re_ι x, ← h.re_ι y, hxy]

/-- The embedding is a closed (topological) embedding: it has the continuous left inverse `re`. -/
theorem isEmbedding : Topology.IsEmbedding ι :=
  Topology.IsEmbedding.of_leftInverse h.re_ι h.re.continuous ι.continuous

/-- Every vector is `ι a + i • ι b` with unique `(a, b)`. -/
theorem exists_unique_decomp (z : XC) : ∃! p : X × X, ι p.1 + Complex.I • ι p.2 = z := by
  refine ⟨(h.re z, h.im z), h.decomp z, ?_⟩
  rintro ⟨a, b⟩ hab
  have h1 := congrArg h.re hab
  have h2 := congrArg h.im hab
  rw [h.re_decomp] at h1
  rw [h.im_decomp] at h2
  simp only [Prod.mk.injEq]
  exact ⟨h1, h2⟩

/-- Complex-linear maps out of `XC` are determined by their values on the real slice `ι X`. -/
theorem ext_ι {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] {L₁ L₂ : XC →L[ℂ] Y}
    (hL : ∀ x, L₁ (ι x) = L₂ (ι x)) : L₁ = L₂ := by
  ext z
  rw [← h.decomp z, map_add, map_add, map_smul, map_smul, hL, hL]

omit h in
theorem I_smul_decomp (a b : X) :
    Complex.I • (ι a + Complex.I • ι b) = ι (-b) + Complex.I • ι a := by
  rw [smul_add, smul_smul, Complex.I_mul_I, neg_smul, one_smul, map_neg, add_comm]

theorem re_I_smul (z : XC) : h.re (Complex.I • z) = -h.im z := by
  obtain ⟨a, b, rfl⟩ : ∃ a b, z = ι a + Complex.I • ι b := ⟨_, _, (h.decomp z).symm⟩
  rw [I_smul_decomp, h.re_decomp, h.im_decomp]

theorem im_I_smul (z : XC) : h.im (Complex.I • z) = h.re z := by
  obtain ⟨a, b, rfl⟩ : ∃ a b, z = ι a + Complex.I • ι b := ⟨_, _, (h.decomp z).symm⟩
  rw [I_smul_decomp, h.im_decomp, h.re_decomp]

/-- Complex conjugation (the real structure) of the complexification. -/
def conj (z : XC) : XC := ι (h.re z) - Complex.I • ι (h.im z)

theorem conj_decomp (a b : X) : h.conj (ι a + Complex.I • ι b) = ι a - Complex.I • ι b := by
  simp [conj, re_decomp, im_decomp]

theorem conj_ι (x : X) : h.conj (ι x) = ι x := by
  simpa using h.conj_decomp x 0

theorem conj_conj (z : XC) : h.conj (h.conj z) = z := by
  have h1 : h.conj z = ι (h.re z) + Complex.I • ι (-h.im z) := by
    simp [conj, sub_eq_add_neg]
  rw [h1, conj_decomp]
  simpa [sub_eq_add_neg] using h.decomp z

theorem conj_add (z w : XC) : h.conj (z + w) = h.conj z + h.conj w := by
  simp only [conj, map_add, smul_add]
  abel

theorem conj_real_smul (r : ℝ) (z : XC) : h.conj (r • z) = r • h.conj z := by
  simp only [conj, map_smul, smul_sub]
  rw [smul_comm Complex.I r (ι (h.im z))]

theorem conj_I_smul (z : XC) : h.conj (Complex.I • z) = -(Complex.I • h.conj z) := by
  simp only [conj, re_I_smul, im_I_smul, map_neg, smul_sub, smul_smul, Complex.I_mul_I, neg_smul,
    one_smul]
  abel

/-- The fixed points of the conjugation are exactly the real slice `ι X`. -/
theorem conj_eq_self_iff (z : XC) : h.conj z = z ↔ ∃ x, z = ι x := by
  constructor
  · intro hz
    have h2 : h.im (h.conj z) = h.im z := by rw [hz]
    have h3 : h.im (h.conj z) = -h.im z := by
      simp [conj, map_sub, im_ι, im_I_ι]
    have h4 : h.im z = 0 := by
      have : h.im z = -h.im z := h2.symm.trans h3
      have h5 : (2 : ℝ) • h.im z = 0 := by rw [two_smul]; nth_rewrite 1 [this]; simp
      simpa using h5
    refine ⟨h.re z, ?_⟩
    have := h.decomp z
    rw [h4] at this
    simpa using this.symm
  · rintro ⟨x, rfl⟩
    exact h.conj_ι x

/-- The real part is the average of `z` and `conj z`, read in the real slice. -/
theorem two_smul_ι_re (z : XC) : (2 : ℝ) • ι (h.re z) = z + h.conj z := by
  have hc : h.conj z = ι (h.re z) - Complex.I • ι (h.im z) := rfl
  have e : z + h.conj z = (ι (h.re z) + Complex.I • ι (h.im z)) + (ι (h.re z) - Complex.I • ι (h.im z)) := by
    rw [hc, h.decomp z]
  rw [e, two_smul]
  abel

end IsComplexification

/-- Sanity check: `ℝ ⊂ ℂ` is a complexification. -/
theorem isComplexification_ofReal : IsComplexification (Complex.ofRealCLM : ℝ →L[ℝ] ℂ) :=
  ⟨Complex.equivRealProdCLM.symm, fun x y => by
    apply Complex.ext <;> simp⟩

/-- Sanity check: the zero map is NOT a complexification (first mismatch of the round 78
receipt: a non-injective parameter map). -/
theorem not_isComplexification_zero : ¬ IsComplexification (0 : ℝ →L[ℝ] ℂ) := by
  rintro ⟨Φ, hΦ⟩
  have h1 := hΦ 1 0
  have h2 := hΦ 0 0
  have : Φ (1, 0) = Φ (0, 0) := by rw [h1, h2]; simp
  have := Φ.injective this
  simp at this

/-- Sanity check: `x ↦ (x, 0)` into `ℂ × ℂ` is NOT a complexification (second mismatch of the
round 78 receipt: the complex span of the real image is not everything). -/
theorem not_isComplexification_split :
    ¬ IsComplexification
      ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).prod (0 : ℝ →L[ℝ] ℂ) : ℝ →L[ℝ] (ℂ × ℂ)) := by
  rintro ⟨Φ, hΦ⟩
  obtain ⟨⟨a, b⟩, hab⟩ := Φ.surjective ((0 : ℂ), (1 : ℂ))
  have h1 := hΦ a b
  rw [hab] at h1
  have h2 := congrArg Prod.snd h1
  simp at h2

/-- Derivative compatibility: if a holomorphic `f'` extends the real map `f₀` along the real
slices, the complex derivative extends the real derivative. -/
theorem deriv_compat {X Y : Type*} {XC YC : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup XC] [NormedSpace ℂ XC] [NormedAddCommGroup YC] [NormedSpace ℂ YC]
    (ιX : X →L[ℝ] XC) (ιY : Y →L[ℝ] YC) {f₀ : X → Y} {f' : XC → YC} {a : X}
    (hf' : DifferentiableAt ℂ f' (ιX a)) (hf₀ : DifferentiableAt ℝ f₀ a)
    (hext : ∀ᶠ x in 𝓝 a, f' (ιX x) = ιY (f₀ x)) (v : X) :
    fderiv ℂ f' (ιX a) (ιX v) = ιY (fderiv ℝ f₀ a v) := by
  have h1 : HasFDerivAt (fun x => f' (ιX x))
      (((fderiv ℂ f' (ιX a)).restrictScalars ℝ).comp ιX) a :=
    (hf'.hasFDerivAt.restrictScalars ℝ).comp a ιX.hasFDerivAt
  have h2 : HasFDerivAt (fun x => ιY (f₀ x)) (ιY.comp (fderiv ℝ f₀ a)) a :=
    ιY.hasFDerivAt.comp a hf₀.hasFDerivAt
  have h3 := h1.unique (h2.congr_of_eventuallyEq hext)
  exact congrArg (fun L => L v) h3

end Datum

section Lift
variable {E : Type v1} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The canonical isometric complex-linear map `E → ULift E`. -/
def upCLM : E →L[ℂ] ULift.{v2} E :=
  LinearMap.mkContinuous
    { toFun := ULift.up, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } 1
    (fun z => by simp)

/-- The canonical isometric complex-linear map `ULift E → E`. -/
def downCLM : ULift.{v2} E →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := ULift.down, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } 1
    (fun z => by simp)

@[simp] theorem upCLM_apply (z : E) : (upCLM.{v1, v2} z) = ULift.up z := rfl
@[simp] theorem downCLM_apply (z : ULift.{v2} E) : (downCLM.{v1, v2} z) = z.down := rfl

end Lift

/-- Universe-general bridge: holomorphic (complex differentiable on an open set) implies analytic
at each point, for complex Banach codomain, with domain and codomain in ARBITRARY universes.
Reduces to the frozen same-universe `HolomorphicStageD3.analyticAt_of_differentiableOn` by
`ULift` (isometric complex-linear lifts). -/
theorem analyticAt_gen {E : Type v1} {F : Type v2} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {f : E → F} {V : Set E}
    (hV : IsOpen V) (hf : DifferentiableOn ℂ f V) {x : E} (hx : x ∈ V) :
    AnalyticAt ℂ f x := by
  let upE : E →L[ℂ] ULift.{v2} E := upCLM
  let downE : ULift.{v2} E →L[ℂ] E := downCLM
  let upF : F →L[ℂ] ULift.{v1} F := upCLM
  let downF : ULift.{v1} F →L[ℂ] F := downCLM
  let fL : ULift.{v2} E → ULift.{v1} F := fun e => upF (f (downE e))
  have hV' : IsOpen (downE ⁻¹' V) := hV.preimage downE.continuous
  have hd : DifferentiableOn ℂ fL (downE ⁻¹' V) :=
    upF.differentiable.comp_differentiableOn (hf.comp downE.differentiable.differentiableOn
      (fun e he => he))
  have hA : AnalyticAt ℂ fL (upE x) :=
    HolomorphicStageD3.analyticAt_of_differentiableOn hV' hd (by simpa [upE, downE] using hx)
  have hB : AnalyticAt ℂ (fun y => downF (fL (upE y))) x :=
    (downF.analyticAt _).comp (f := fun y => fL (upE y)) (hA.comp (f := upE) (upE.analyticAt x))
  exact hB.congr (Eventually.of_forall fun y => by simp [fL, upE, downE, upF, downF])

end QuantumNLS.Ext025GP03Cx

#print axioms QuantumNLS.Ext025GP03Cx.IsComplexification.decomp
#print axioms QuantumNLS.Ext025GP03Cx.IsComplexification.injective
#print axioms QuantumNLS.Ext025GP03Cx.IsComplexification.isEmbedding
#print axioms QuantumNLS.Ext025GP03Cx.IsComplexification.exists_unique_decomp
#print axioms QuantumNLS.Ext025GP03Cx.IsComplexification.ext_ι
#print axioms QuantumNLS.Ext025GP03Cx.IsComplexification.conj_conj
#print axioms QuantumNLS.Ext025GP03Cx.IsComplexification.conj_I_smul
#print axioms QuantumNLS.Ext025GP03Cx.IsComplexification.conj_eq_self_iff
#print axioms QuantumNLS.Ext025GP03Cx.IsComplexification.two_smul_ι_re
#print axioms QuantumNLS.Ext025GP03Cx.isComplexification_ofReal
#print axioms QuantumNLS.Ext025GP03Cx.not_isComplexification_zero
#print axioms QuantumNLS.Ext025GP03Cx.not_isComplexification_split
#print axioms QuantumNLS.Ext025GP03Cx.deriv_compat
#print axioms QuantumNLS.Ext025GP03Cx.analyticAt_gen
