import NlsGge.Schur.FreeDomainAbsoluteFourierSummability
import NlsGge.Schur.FreePhysicalCharacterDerivativeTrace

/-! NEW-F02.02: genuine continuous Fourier reconstruction has the source
endpoint parity trace. L2 identification and full weak-domain equivalence
are separate outstanding obligations, not presumed in this theorem. -/
set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace NlsGge.Schur

def freeDomainContinuousComponent (n : ℤ) (x : SectorSquare n)
    (upper : Bool) : C(SpectralCircle, ℂ) :=
  ∑' m : Sector n, x (upper,m) •
    fourier (T := (2 : ℝ)) (if upper then m.val else -m.val)

lemma freeDomainContinuousComponent_hasSum
    (n : ℤ) (x : SectorSquare n) (hx : x ∈ freeWeightedDomainPointwise n)
    (upper : Bool) :
    HasSum (fun m : Sector n => x (upper,m) •
      fourier (T := (2 : ℝ)) (if upper then m.val else -m.val))
      (freeDomainContinuousComponent n x upper) :=
  (freeDomain_component_continuous_fourier_summable n x hx upper).hasSum

lemma freeDomainContinuousComponent_hasSum_eval
    (n : ℤ) (x : SectorSquare n) (hx : x ∈ freeWeightedDomainPointwise n)
    (upper : Bool) (y : SpectralCircle) :
    HasSum (fun m : Sector n => x (upper,m) *
      fourier (T := (2 : ℝ)) (if upper then m.val else -m.val) y)
      (freeDomainContinuousComponent n x upper y) := by
  have h := (ContinuousMap.evalCLM ℂ y).hasSum
    (freeDomainContinuousComponent_hasSum n x hx upper)
  simpa only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply,
    smul_eq_mul] using h

lemma freeDomainContinuousComponent_endpoint_parity
    (n : ℤ) (x : SectorSquare n) (hx : x ∈ freeWeightedDomainPointwise n)
    (upper : Bool) :
    freeDomainContinuousComponent n x upper ((1 : ℝ) : SpectralCircle) =
      spectralSign n * freeDomainContinuousComponent n x upper ((0 : ℝ) : SpectralCircle) := by
  have h1 := freeDomainContinuousComponent_hasSum_eval n x hx upper
    ((1 : ℝ) : SpectralCircle)
  have h0 := (freeDomainContinuousComponent_hasSum_eval n x hx upper
    ((0 : ℝ) : SpectralCircle)).mul_left (spectralSign n)
  have hterm (m : Sector n) :
      x (upper,m) * fourier (T := (2 : ℝ))
        (if upper then m.val else -m.val) ((1 : ℝ) : SpectralCircle) =
      spectralSign n * (x (upper,m) * fourier (T := (2 : ℝ))
        (if upper then m.val else -m.val) ((0 : ℝ) : SpectralCircle)) := by
    cases upper
    · simp only [Bool.false_eq_true, if_false]
      rw [sourceLowerCharacter_endpoint_parity n m]
      ring
    · simp only [if_true]
      rw [sourceUpperCharacter_endpoint_parity n m]
      ring
  exact h1.unique (h0.congr_fun hterm)

end NlsGge.Schur
