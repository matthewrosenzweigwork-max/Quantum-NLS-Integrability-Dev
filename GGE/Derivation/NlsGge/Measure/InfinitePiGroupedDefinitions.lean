import NlsGge.Measure.InfinitePiReindex
import Mathlib.Probability.ProductMeasure

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace NlsGge.Measure.BoolSigmaProbe2

/-- The exact dependent Bool-indexed block type supplied by sumEquivSigmaBool. -/
abbrev BoolSumIndex (A : Set ℤ) :=
  Σ b : Bool, bif b then (Aᶜ : Set ℤ) else A

def sumToBoolSigma (A : Set ℤ) [DecidablePred (· ∈ A)] :
    A ⊕ (Aᶜ : Set ℤ) ≃ BoolSumIndex A :=
  Equiv.sumEquivSigmaBool A (Aᶜ : Set ℤ)

def actualSigmaGaussianFamily (c : ℕ → ℝ) (A : Set ℤ)
    [DecidablePred (· ∈ A)] : BoolSumIndex A → MeasureTheory.Measure ℂ :=
  fun p => complexGaussian (fullWeightRate c
    (Equiv.Set.sumCompl A ((sumToBoolSigma A).symm p)))

def actualSigmaPiReindex (A : Set ℤ) [DecidablePred (· ∈ A)] :
    ((u : A ⊕ (Aᶜ : Set ℤ)) → ℂ) ≃ᵐ ((p : BoolSumIndex A) → ℂ) :=
  MeasurableEquiv.piCongrLeft (fun _ : BoolSumIndex A => ℂ) (sumToBoolSigma A)

def actualSigmaPiCurry (A : Set ℤ) :
    ((p : BoolSumIndex A) → ℂ) ≃ᵐ
      ((b : Bool) → (j : bif b then (Aᶜ : Set ℤ) else A) → ℂ) :=
  MeasurableEquiv.piCurry (fun b (j : bif b then (Aᶜ : Set ℤ) else A) => ℂ)

def actualSigmaGroupedEquiv (A : Set ℤ) [DecidablePred (· ∈ A)] :
    ((u : A ⊕ (Aᶜ : Set ℤ)) → ℂ) ≃ᵐ
      ((b : Bool) → (j : bif b then (Aᶜ : Set ℤ) else A) → ℂ) :=
  (actualSigmaPiReindex A).trans (actualSigmaPiCurry A)

def actualSigmaGroupedLaw (c : ℕ → ℝ) (A : Set ℤ)
    [DecidablePred (· ∈ A)] :
    MeasureTheory.Measure
      ((b : Bool) → (j : bif b then (Aᶜ : Set ℤ) else A) → ℂ) :=
  Measure.infinitePi (fun b : Bool =>
    Measure.infinitePi (fun j : bif b then (Aᶜ : Set ℤ) else A =>
      complexGaussian (fullWeightRate c
        (Equiv.Set.sumCompl A ((sumToBoolSigma A).symm ⟨b, j⟩)))))

#check @Equiv.Set.sumCompl
#check @Equiv.sumEquivSigmaBool
#check @MeasurableEquiv.piCongrLeft
#check @MeasurableEquiv.piCurry
#check @Measure.infinitePi_map_piCongrLeft
#check @Measure.infinitePi_map_piCurry
#check @NlsGge.Measure.BoolSigmaProbe2.actualSigmaGaussianFamily
#check @NlsGge.Measure.BoolSigmaProbe2.actualSigmaPiReindex
#check @NlsGge.Measure.BoolSigmaProbe2.actualSigmaPiCurry
#check @NlsGge.Measure.BoolSigmaProbe2.actualSigmaGroupedEquiv
#check @NlsGge.Measure.BoolSigmaProbe2.actualSigmaGroupedLaw

end NlsGge.Measure.BoolSigmaProbe2
