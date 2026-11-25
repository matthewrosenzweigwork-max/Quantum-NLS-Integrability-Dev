import QuantumNLS.Prop022StrongOperatorR125
import QuantumNLS.Prop022WeakEquationR120

/-! Strong Schrodinger equation for the actual R122 quadratic propagator.
Its physical generator and its time continuity are conclusions. -/
set_option Elab.async false
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace Topology ComplexConjugate
open ContinuousLinearMap Set Filter MeasureTheory
namespace QuantumNLS.Prop022StrongEquationR125
open BetheCoefficientTransform Ext025B3PhysicalSectors Ext005Moments
open Ext005FormScaleR109 Ext005FormCutoffR109 Ext005MomentEnergyR108
open Ext005PhysicalNumberFormR114 Ext005ComplexRieszR113 Ext005IntervalChainR111
open Prop022FactorialCoefficientsR115 Prop022ActualProfileR117
open Prop022StrongOperatorR125 Prop022FockPropagatorR122 Prop022DomainR122
variable {L : ℝ} [Fact (0 < L)]
local instance (n : ℕ) : NormedSpace ℝ (HN L n) := NormedSpace.restrictScalars ℝ ℂ (HN L n)
local instance : NormedSpace ℝ (Fock L) := NormedSpace.restrictScalars ℝ ℂ (Fock L)
local instance : InnerProductSpace ℝ (Fock L) := InnerProductSpace.rclikeToReal ℂ (Fock L)
variable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
  (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
  (u₀ : Prop001.Sphere (PhysicalTensor.L2T L))
local notation "V" => evolution B M A hM hA hB hs u₀
local notation "a" => fun t => numberCoefficient B (profile B M A hA hB hs u₀ t)
local notation "b" => fun t => pairCoefficient B (profile B M A hA hB hs u₀ t)
local notation "K" => fun t => formOperator (quadraticContinuous (a t) (b t))

/-- Physical Schrodinger force for the existing propagator, rather than a
new evolution chosen to satisfy a desired equation. -/
def strongForce (s : ℝ) (x : momentDomain (L := L) 4) (t : ℝ) : Fock L :=
  (-Complex.I) • strongCoordinates (a t) (b t) (rootLift 2 (V s t x.val))

lemma strongForce_continuous (s : ℝ) (x : momentDomain (L := L) 4) :
    Continuous (strongForce B M A hM hA hB hs u₀ s x) := by
  have hc := actual_coefficients_continuous B M A hA hB hs u₀
  exact ((strongCoordinates_continuous a b hc.1 hc.2).clm_apply
    (evolution_root_continuous B M A hM hA hB hs u₀ 2 s x)).const_smul (-Complex.I)

lemma strongForce_embedding (s : ℝ) (x : momentDomain (L := L) 4) (t : ℝ) :
    embedding 1 (strongForce B M A hM hA hB hs u₀ s x t) =
      (-Complex.I) • K t (rootLift 1 (V s t x.val)) := by
  have hx4 := (evolution_energy B M A hM hA hB hs u₀ 4 (by omega) s t x).1
  have hx2 := domain_mono (by omega : 2 ≤ 4) hx4
  have he : rootLift 1 (V s t x.val) = embedding 1 (rootLift 2 (V s t x.val)) :=
    (root_one_of_two (⟨V s t x.val,hx2⟩ : momentDomain (L := L) 2)).trans
      (congrArg (embedding 1) (rootLift_eq 2 _ hx2).symm)
  rw [strongForce, map_smul, strongCoordinates_embedding]
  exact congrArg (fun z : Fock L => (-Complex.I) • K t z) he.symm

/-- The previously proved physical weak equation, with its antidual force
now represented by a continuous Fock-space vector. -/
lemma embedded_weak (s : ℝ) (x : momentDomain (L := L) 4) (T : ℝ) (hT : 0 ≤ T) :
    WeakDerivativeOn (Ioo (s-T) (s+T)) (fun t => embedding 1 (V s t x.val))
      (fun t => embedding 1 (strongForce B M A hM hA hB hs u₀ s x t)) := by
  let x3 : momentDomain (L := L) 3 := ⟨x.val,domain_mono (by omega) x.property⟩
  have hw := Prop022WeakEquationR120.common_weak_equation B M A hM hA hB hs u₀ s x3 T hT
  have he : Prop022CutoffLimitR120.limit B M A hM hA hB hs u₀ s x3 =
      fun t => V s t x.val := funext (fun t => (evolution_on_domain B M A hM hA hB hs u₀ s t x3).symm)
  rw [he] at hw
  have hf : (fun t => embedding 1 (strongForce B M A hM hA hB hs u₀ s x t)) =
      fun t => (-Complex.I) • K t (rootLift 1 (V s t x.val)) :=
    funext (strongForce_embedding B M A hM hA hB hs u₀ s x)
  rw [hf]
  exact hw

/-- Signed-time Fock-space integral equation, obtained by injectivity of
the physical form-scale embedding. -/
theorem evolution_integral (s t : ℝ) (x : momentDomain (L := L) 4) :
    V s t x.val - x.val = ∫ r in s..t, strongForce B M A hM hA hB hs u₀ s x r := by
  let T := |t-s|+1
  have hT : 0 < T := by dsimp [T]; positivity
  have hc := strongForce_continuous B M A hM hA hB hs u₀ s x
  have hw := weak_to_integral_on (s-T) (s+T) (by linarith)
    (fun r => embedding 1 (V s r x.val))
    (fun r => embedding 1 (strongForce B M A hM hA hB hs u₀ s x r))
    (((embedding (L := L) 1).continuous.comp
      (evolution_continuous B M A hM hA hB hs u₀ s x.val)).continuousOn)
    (((embedding (L := L) 1).continuous.comp hc).continuousOn.integrableOn_compact isCompact_Icc)
    (embedded_weak B M A hM hA hB hs u₀ s x T hT.le) s t
    (by constructor <;> linarith)
    (by constructor <;> dsimp [T] <;> linarith [neg_abs_le (t-s), le_abs_self (t-s)])
  rw [evolution_self, (embedding (L := L) 1).intervalIntegral_comp_comm (hc.intervalIntegrable s t)] at hw
  apply embedding_injective 1
  simpa only [map_sub] using hw

/-- Strong differentiability of the actual R122 propagator on the common
moment domain, for every signed initial and final time. -/
theorem evolution_hasDerivAt (s t : ℝ) (x : momentDomain (L := L) 4) :
    HasDerivAt (fun r => V s r x.val) (strongForce B M A hM hA hB hs u₀ s x t) t := by
  have hc := strongForce_continuous B M A hM hA hB hs u₀ s x
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable s t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).add_const x.val
  have he : (fun r => V s r x.val) =
      fun r => (∫ v in s..r, strongForce B M A hM hA hB hs u₀ s x v)+x.val := by
    funext r
    exact sub_eq_iff_eq_add.mp (evolution_integral B M A hM hA hB hs u₀ s r x)
  rw [he]
  exact hd

/-- C1 regularity in physical Fock norm on the common moment domain. -/
theorem evolution_C1 (s : ℝ) (x : momentDomain (L := L) 4) :
    ContDiff ℝ 1 (fun r => V s r x.val) := by
  apply contDiff_one_iff_deriv.mpr
  constructor
  · intro t
    exact (evolution_hasDerivAt B M A hM hA hB hs u₀ s t x).differentiableAt
  · exact (strongForce_continuous B M A hM hA hB hs u₀ s x).congr
      (fun t => (evolution_hasDerivAt B M A hM hA hB hs u₀ s t x).deriv.symm)

/-- The literal strong quadratic Hamiltonian equation, without a supplied
strong equation, coefficient continuity, or propagated moment estimate. -/
theorem evolution_strong_quadratic (s t : ℝ) (x : momentDomain (L := L) 4) :
    let hx := domain_mono (by omega : 2 ≤ 4)
      (evolution_energy B M A hM hA hB hs u₀ 4 (by omega) s t x).1
    Complex.I • deriv (fun r => V s r x.val) t =
      quadraticAction (a t) (b t) ⟨V s t x.val,hx⟩ := by
  dsimp only
  have hd : deriv (fun r => V s r x.val) t = strongForce B M A hM hA hB hs u₀ s x t :=
    (evolution_hasDerivAt B M A hM hA hB hs u₀ s t x).deriv
  calc
    Complex.I • deriv (fun r => V s r x.val) t =
        Complex.I • strongForce B M A hM hA hB hs u₀ s x t :=
      congrArg (fun z : Fock L => Complex.I • z) hd
    _ = strongCoordinates (a t) (b t) (rootLift 2 (V s t x.val)) := by
      simp only [strongForce, smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
    _ = _ := congrArg (strongCoordinates (a t) (b t)) (rootLift_eq 2 _ _)

end QuantumNLS.Prop022StrongEquationR125
#print axioms QuantumNLS.Prop022StrongEquationR125.evolution_strong_quadratic
set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022StrongEquationR125." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022StrongEquationR125." then
      pending := pending.push n
  let roots := pending.size
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
  Lean.logInfo m!"R125 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
