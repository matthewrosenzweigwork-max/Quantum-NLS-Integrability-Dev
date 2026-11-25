import QuantumNLS.Prop021StrongProductR131
import QuantumNLS.Prop024WWeylPhysical
import QuantumNLS.Prop021DisplacementR129
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! The central phase of the actual Weyl product on torus Fock, derived
from the radial Stone derivative and the frozen affine field identities. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
open scoped InnerProductSpace
namespace QuantumNLS.Prop021WeylLawR131

open PhysicalTensor Ext025B3PhysicalSectors Prop024WWeylPhysical Prop022OVacuum
open Ext006KernelHilbertSchmidt Ext006SmoothOperatorsR34a Ext006StrongFieldR41a
open Prop021DisplacementR129
variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

/-- Actual Weyl generator on the common physical moment domain. -/
def G (v : L2T L) : Module.End ℂ (physSmooth L) := creP v - annP v

lemma G_eq (v : L2T L) (x : physSmooth L) :
    (G v x).val = generator v x.val x.property := by
  unfold G creP annP generator
  let c := C ((physicalBasis L).repr v)
  let a := A ((physicalBasis L).repr v)
  have h := congrArg (fun S : Module.End ℂ (physSmooth L) => (S x).val)
    ((transport (L := L)).map_sub c a)
  exact h.symm.trans (transport_coe (c-a) x)

lemma G_add (v w : L2T L) : G (v+w) = G v + G w := by
  simp only [G, creP, annP, map_add, A_add_smear, C_add_smear]
  abel

lemma G_weyl (v w : L2T L) (x : physSmooth L) :
    (G v (printedWeylD w x)).val =
      printedWeyl w ((G v x).val + (⟪w,v⟫_ℂ - ⟪v,w⟫_ℂ) • x.val) := by
  have ha := congrArg (printedWeyl w) (weyl_conj_ann_apply w v x)
  have hc := congrArg (printedWeyl w) (weyl_conj_cre_apply w v x)
  rw [LinearIsometryEquiv.apply_symm_apply] at ha hc
  simp only [G, LinearMap.sub_apply, Submodule.coe_sub, ha, hc, ← map_sub]
  congr 1
  module

def ray (v : L2T L) (t : ℝ) : Fock L ≃ₗᵢ[ℂ] Fock L := printedWeyl ((t : ℂ) • v)

def rayD (v : L2T L) (t : ℝ) : Module.End ℂ (physSmooth L) :=
  printedWeylD ((t : ℂ) • v)

lemma rayD_val (v : L2T L) (t : ℝ) (x : physSmooth L) : (rayD v t x).val = ray v t x.val :=
  printedWeylD_coe _ _

lemma ray_continuous (v : L2T L) (x : Fock L) : Continuous (fun t => ray v t x) :=
  displacement_ray_continuous v x

lemma ray_zero (v : L2T L) (x : Fock L) : ray v 0 x = x := by
  change displacement ((0 : ℂ) • v) x = x
  exact displacement_ray_zero v x

lemma G_rayD (v : L2T L) (t : ℝ) (x : physSmooth L) :
    (G v (rayD v t x)).val = ray v t (G v x).val := by
  have h := G_weyl v ((t : ℂ) • v) x
  have hz : ⟪(t : ℂ) • v,v⟫_ℂ - ⟪v,(t : ℂ) • v⟫_ℂ = 0 := by
    rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, sub_self]
  simpa only [rayD, ray, hz, zero_smul, add_zero] using h

lemma ray_hasDerivAt (v : L2T L) (t : ℝ) (x : physSmooth L) :
    HasDerivAt (fun r => ray v r x.val) (G v (rayD v t x)).val t := by
  rw [G_rayD, G_eq]
  exact displacement_ray_hasDerivAt v x.val x.property t

private def realIso (U : Fock L ≃ₗᵢ[ℂ] Fock L) : Fock L →ₗᵢ[ℝ] Fock L where
  toLinearMap := U.toLinearEquiv.toLinearMap.restrictScalars ℝ
  norm_map' := U.norm_map

lemma moving_ray_hasDerivAt (v : L2T L) (t : ℝ) (x : ℝ → physSmooth L) (dx : Fock L)
    (hd : HasDerivAt (fun s => (x s).val) dx t) :
    HasDerivAt (fun s => ray v s (x s).val)
      (ray v t dx + (G v (rayD v t (x t))).val) t := by
  exact Prop021StrongProductR131.hasDerivAt_apply (U := fun s => realIso (ray v s))
    (fun y => (ray_continuous v y).continuousAt) (ray_hasDerivAt v t (x t)) hd

private lemma inner_phase (v w : L2T L) (t : ℝ) :
    ⟪(t : ℂ) • v,w⟫_ℂ - ⟪w,(t : ℂ) • v⟫_ℂ =
      2 * Complex.I * (t : ℂ) * (⟪v,w⟫_ℂ).im := by
  let z : ℂ := ⟪v,w⟫_ℂ
  have hconj : ⟪w,v⟫_ℂ = star z := (inner_conj_symm (𝕜 := ℂ) w v).symm
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, hconj]
  change (t : ℂ)*z - (t : ℂ)*star z = 2*Complex.I*(t : ℂ)*z.im
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im]
  · simp [Complex.mul_re, Complex.mul_im]
    ring

private lemma ray_composite_deriv (v w : L2T L) (x : physSmooth L) (t : ℝ) :
    let y : ℝ → physSmooth L := fun s => rayD v s (rayD w s x)
    HasDerivAt (fun s => (y s).val)
      ((G (v+w) (y t)).val - (2 * Complex.I * (t : ℂ) * (⟪v,w⟫_ℂ).im) • (y t).val) t := by
  let y₀ := fun s => rayD w s x
  have hd := moving_ray_hasDerivAt v t y₀ (G w (y₀ t)).val
    (by simpa only [y₀, rayD_val] using ray_hasDerivAt w t x)
  have hg := G_weyl w ((t : ℂ) • v) (y₀ t)
  rw [inner_phase, map_add, map_smul] at hg
  have hg' : (G w (rayD v t (y₀ t))).val =
      ray v t (G w (y₀ t)).val +
        (2 * Complex.I * (t : ℂ) * (⟪v,w⟫_ℂ).im) • (rayD v t (y₀ t)).val := by
    rw [rayD_val]
    exact hg
  have hfun : (fun s => ray v s (y₀ s).val) = (fun s => (rayD v s (y₀ s)).val) := by
    funext s
    exact (rayD_val v s (y₀ s)).symm
  rw [hfun] at hd
  have hvel : (G (v+w) (rayD v t (y₀ t))).val -
      (2 * Complex.I * (t : ℂ) * (⟪v,w⟫_ℂ).im) • (rayD v t (y₀ t)).val =
      ray v t (G w (y₀ t)).val + (G v (rayD v t (y₀ t))).val := by
    rw [G_add, LinearMap.add_apply, Submodule.coe_add, hg']
    abel
  change HasDerivAt (fun s => (rayD v s (y₀ s)).val)
    ((G (v+w) (rayD v t (y₀ t))).val -
      (2 * Complex.I * (t : ℂ) * (⟪v,w⟫_ℂ).im) • (rayD v t (y₀ t)).val) t
  rw [hvel]
  exact hd

private def phase (d t : ℝ) : ℂ := Complex.exp (Complex.I * (t : ℂ)^2 * (d : ℂ))

private lemma phase_hasDerivAt (d t : ℝ) :
    HasDerivAt (phase d) ((2 * Complex.I * (t : ℂ) * (d : ℂ)) * phase d t) t := by
  have ht := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_id t)
  change HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t at ht
  have hd : HasDerivAt (fun s : ℝ => Complex.I * (s : ℂ)^2 * (d : ℂ))
      (2 * Complex.I * (t : ℂ) * (d : ℂ)) t := by
    convert (((ht.pow 2).const_mul Complex.I).mul_const (d : ℂ)) using 1
    ring
  have h := hd.cexp
  change HasDerivAt (phase d) (phase d t * (2 * Complex.I * (t : ℂ) * (d : ℂ))) t at h
  rw [mul_comm] at h
  exact h

private theorem corrected_ray_deriv (v w : L2T L) (x : physSmooth L) (t : ℝ) :
    let f : ℝ → physSmooth L := fun s => phase (⟪v,w⟫_ℂ).im s • rayD v s (rayD w s x)
    HasDerivAt (fun s => (f s).val) (G (v+w) (f t)).val t := by
  let d := (⟪v,w⟫_ℂ).im
  let y := fun s => rayD v s (rayD w s x)
  let a : ℂ := 2 * Complex.I * (t : ℂ) * (d : ℂ)
  have h := (phase_hasDerivAt d t).smul (ray_composite_deriv v w x t)
  have hvel : phase d t • ((G (v+w) (y t)).val - a • (y t).val) +
      (a * phase d t) • (y t).val = phase d t • (G (v+w) (y t)).val := by
    rw [smul_sub, smul_smul, mul_comm (phase d t)]
    abel
  change HasDerivAt (fun s => phase d s • (y s).val) _ t at h
  rw [hvel] at h
  simpa only [LinearMap.map_smul, Submodule.coe_smul] using h

theorem smooth_dense : Dense (physSmooth L : Set (Fock L)) := by
  intro y
  refine mem_closure_of_tendsto (projection_hasSum L y).tendsto_sum_nat ?_
  exact Filter.Eventually.of_forall fun n => (mem_physSmooth_iff_moments _).mpr
    (fun p => Submodule.sum_mem _ (fun j _ => Ext005Moments.sector_mem_momentDomain p j y))

private lemma backward_ray_deriv (v : L2T L) (f : ℝ → physSmooth L) (t : ℝ)
    (hf : HasDerivAt (fun s => (f s).val) (G v (f t)).val t) :
    HasDerivAt (fun s => ray v (-s) (f s).val) 0 t := by
  have hU (z : Fock L) : ContinuousAt (fun s => ray v (-s) z) t :=
    ((ray_continuous v z).comp continuous_neg).continuousAt
  have hfix := (ray_hasDerivAt v (-t) (f t)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_neg t)
  rw [ContinuousLinearMap.toSpanSingleton_apply, neg_one_smul] at hfix
  have hfixed : HasDerivAt (fun s => ray v (-s) (f t).val)
      (-(G v (rayD v (-t) (f t))).val) t := hfix
  have h := Prop021StrongProductR131.hasDerivAt_apply
    (E := Fock L) (U := fun s => realIso (ray v (-s))) (v := fun s => (f s).val) (t := t)
    (dv := (G v (f t)).val) (dU := -(G v (rayD v (-t) (f t))).val)
    hU hfixed hf
  change HasDerivAt (fun s => ray v (-s) (f s).val)
    (ray v (-t) (G v (f t)).val + -(G v (rayD v (-t) (f t))).val) t at h
  rwa [G_rayD, add_neg_cancel] at h

private lemma projective_ray (v w : L2T L) (x : physSmooth L) (t : ℝ) :
    ray (v+w) t x.val = phase (⟪v,w⟫_ℂ).im t • (rayD v t (rayD w t x)).val := by
  let f : ℝ → physSmooth L := fun s => phase (⟪v,w⟫_ℂ).im s • rayD v s (rayD w s x)
  let y : ℝ → Fock L := fun s => ray (v+w) (-s) (f s).val
  have hy (s : ℝ) : HasDerivAt y 0 s :=
    backward_ray_deriv (v+w) f s (corrected_ray_deriv v w x s)
  have he : ∀ s r : ℝ, y s = y r := is_const_of_deriv_eq_zero
    (fun s => (hy s).differentiableAt) (fun s => (hy s).deriv)
  have hh := he t 0
  have h0 : y 0 = x.val := by
    simp only [y, neg_zero, ray_zero, f, Submodule.coe_smul, rayD_val, phase, Complex.ofReal_zero,
      zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, Complex.exp_zero, one_smul]
  rw [h0] at hh
  have hinv : ray (v+w) t (y t) = (f t).val := by
    unfold y ray
    rw [Complex.ofReal_neg, neg_smul]
    simpa only [neg_neg] using printedWeyl_neg_apply (-((t : ℂ) • (v+w))) (f t).val
  change ray (v+w) t x.val = (f t).val
  rw [← hh, hinv]
/-- The exact projective law with the inner product linear in its second
argument, extended by continuity on the same physical Fock space. -/
theorem printedWeyl_add (v w : L2T L) (x : Fock L) :
    printedWeyl (v+w) x =
      Complex.exp (Complex.I * (⟪v,w⟫_ℂ).im) • printedWeyl v (printedWeyl w x) := by
  have hcomp : Continuous (fun y : Fock L => printedWeyl v (printedWeyl w y)) :=
    (printedWeyl v).continuous.comp (printedWeyl w).continuous
  let c := Complex.exp (Complex.I * (⟪v,w⟫_ℂ).im)
  have hscaled : Continuous (fun y : Fock L => c • printedWeyl v (printedWeyl w y)) :=
    (continuous_const_smul (T := Fock L) c).comp hcomp
  have hclosed : IsClosed {y : Fock L | printedWeyl (v+w) y =
      c • printedWeyl v (printedWeyl w y)} := isClosed_eq (printedWeyl (v+w)).continuous hscaled
  have hin : (physSmooth L : Set (Fock L)) ⊆ {y | printedWeyl (v+w) y =
      c • printedWeyl v (printedWeyl w y)} := by
    intro y hy
    have h := projective_ray v w ⟨y,hy⟩ 1
    simp only [ray, rayD_val, phase, Complex.ofReal_one, one_smul, one_pow, mul_one] at h
    exact h
  exact closure_minimal hin hclosed (smooth_dense x)

end QuantumNLS.Prop021WeylLawR131

#print axioms QuantumNLS.Prop021WeylLawR131.printedWeyl_add

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if ["Prop021WeylLawR131"].any
        (fun m => n.toString.startsWith ("QuantumNLS." ++ m ++ ".") ||
          n.toString.startsWith ("_private.QuantumNLS." ++ m ++ ".")) then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").contains "HeldGP14Tonelli" ||
          (n.toString.splitOn ".").contains "RegularCut" then
        throwError "Forbidden held dependency: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"R131 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
