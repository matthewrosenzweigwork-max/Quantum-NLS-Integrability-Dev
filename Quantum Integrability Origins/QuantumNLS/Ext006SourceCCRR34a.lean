import QuantumNLS.Ext006SmoothOperatorsR34a
import QuantumNLS.Ext006PhysSymplectic

/-! Bogoliubov CCR for the ORIGINAL source P,Q blocks of a symplectic
map. The block scalar identities follow from symplecticity. No supplied
covariance, CCR, Gram matrix, vacuum or implementation is a hypothesis. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006SourceCCRR34a
open Ext006BogoliubovAlg Ext006KernelHilbertSchmidt Ext006SymplecticKernel
open Ext006SmoothOperatorsR34a
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

omit [CompleteSpace E] in
/-- Polarize the norm difference for two actual complex linear maps. -/
lemma inner_difference (P Q : E →L[ℂ] E)
    (hn : ∀ z, ‖P z‖^2-‖Q z‖^2=‖z‖^2) (f g : E) :
    inner ℂ (P f) (P g)-inner ℂ (Q f) (Q g)=inner ℂ f g := by
  have hr (x y : E) : (inner ℂ (P x) (P y)).re-(inner ℂ (Q x) (Q y)).re =
      (inner ℂ x y).re := by
    have ha := hn (x+y)
    simp only [map_add,norm_add_sq (𝕜 := ℂ)] at ha
    have hx := hn x
    have hy := hn y
    simp only [RCLike.re_to_complex] at ha
    linarith
  apply Complex.ext
  · exact hr f g
  · have hi := hr f (Complex.I • g)
    simp only [map_smul,inner_smul_right,Complex.I_mul_re] at hi
    simp only [Complex.sub_im]
    linarith

/-- The original source rows, expressed in the fixed occupation basis. -/
def p (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (f : E) : H :=
  b.repr (sourceP S f)
def r (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (f : E) : H :=
  b.repr (conjugation b (sourceQ b S f))

omit [CompleteSpace E] in
lemma r_star (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (f : E) :
    r b S f = star (b.repr (sourceQ b S f)) := by
  simp only [r,conjugation_apply,LinearIsometryEquiv.apply_symm_apply]

/-- Full scalar mixed identity, derived by polarization of the symplectic
norm identity, with the conjugation order displayed. -/
lemma source_mixed (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Symplectic S.toContinuousLinearMap) (f g : E) :
    inner ℂ (p b S f) (p b S g)-inner ℂ (r b S g) (r b S f)=inner ℂ f g := by
  have hn (z : E) : ‖sourceP S z‖^2-‖sourceQ b S z‖^2=‖z‖^2 := by
    change ‖Ext006Blocks.complexPart S.toContinuousLinearMap z‖^2-
      ‖conjugation b (Ext006Blocks.antilinearPart S.toContinuousLinearMap z)‖^2=‖z‖^2
    rw [conjugation_norm]
    exact norm_identity S hS z
  rw [p,p,r_star,r_star,Ext006PhysSymplectic.inner_star',inner_conj_symm,
    LinearIsometryEquiv.inner_map_map,LinearIsometryEquiv.inner_map_map]
  exact inner_difference (sourceP S) (sourceQ b S) hn f g

lemma kernel_sourceP (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Symplectic S.toContinuousLinearMap) (f : E) :
    kernel S hS (sourceP S f) = conjugation b (sourceQ b S f) := by
  change Ext006Blocks.antilinearPart S.toContinuousLinearMap
    ((linearBlock S hS).symm (Ext006Blocks.complexPart S.toContinuousLinearMap f)) =
    conjugation b (conjugation b (Ext006Blocks.antilinearPart S.toContinuousLinearMap f))
  rw [← linearBlock_apply S hS,ContinuousLinearEquiv.symm_apply_apply,conjugation_sq]

/-- The scalar cross identity is a conclusion of the symmetric intrinsic
kernel, evaluated on the two original source P rows. -/
lemma source_cross (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Symplectic S.toContinuousLinearMap) (f g : E) :
    inner ℂ (p b S f) (r b S g)=inner ℂ (p b S g) (r b S f) := by
  have hc := kernel_complex_symmetric S hS (sourceP S f) (sourceP S g)
  rw [kernel_sourceP b S hS, kernel_sourceP b S hS] at hc
  simpa only [p,r,LinearIsometryEquiv.inner_map_map] using hc

/-- Actual source annihilation and creation endomorphisms. -/
def sourceAnn (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (f : E) : Module.End ℂ D :=
  B (p b S f) (r b S f)
def sourceCre (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (f : E) : Module.End ℂ D :=
  Bstar (p b S f) (r b S f)

/-- Bogoliubov mixed CCR on the full invariant domain for actual source
blocks. No Hilbert-Schmidt assumption is needed for the algebra. -/
theorem source_AC (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Symplectic S.toContinuousLinearMap) (f g : E) :
    sourceAnn b S f*sourceCre b S g-sourceCre b S g*sourceAnn b S f =
      (inner ℂ f g) • (1 : Module.End ℂ D) := by
  rw [sourceAnn,sourceCre,BBstar,source_mixed b S hS]

theorem source_AA (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Symplectic S.toContinuousLinearMap) (f g : E) :
    sourceAnn b S f*sourceAnn b S g = sourceAnn b S g*sourceAnn b S f := by
  apply sub_eq_zero.mp
  rw [sourceAnn,sourceAnn,BB,source_cross b S hS,sub_self,zero_smul]

theorem source_CC (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E)
    (hS : Symplectic S.toContinuousLinearMap) (f g : E) :
    sourceCre b S f*sourceCre b S g = sourceCre b S g*sourceCre b S f := by
  apply sub_eq_zero.mp
  rw [sourceCre,sourceCre,BstarBstar]
  have he := congrArg (starRingEnd ℂ) (source_cross b S hS f g)
  rw [inner_conj_symm,inner_conj_symm] at he
  rw [he,sub_self,zero_smul]

omit [CompleteSpace E] in
theorem source_adjoint (b : HilbertBasis ℤ ℂ E) (S : E ≃L[ℝ] E) (f : E) (v w : D) :
    inner ℂ v.1 ((sourceAnn b S f w).1) = inner ℂ ((sourceCre b S f v).1) w.1 :=
  B_adjoint (p b S f) (r b S f) v w

end QuantumNLS.Ext006SourceCCRR34a

#print axioms QuantumNLS.Ext006SourceCCRR34a.source_mixed
#print axioms QuantumNLS.Ext006SourceCCRR34a.source_cross
#print axioms QuantumNLS.Ext006SourceCCRR34a.source_AC
#print axioms QuantumNLS.Ext006SourceCCRR34a.source_AA
#print axioms QuantumNLS.Ext006SourceCCRR34a.source_CC
#print axioms QuantumNLS.Ext006SourceCCRR34a.source_adjoint

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006SourceCCRR34a." then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
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
  Lean.logInfo m!"Round34a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
