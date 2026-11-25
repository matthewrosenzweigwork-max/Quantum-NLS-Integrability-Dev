import NlsGge.Measure.InfinitePiHeadTailProduct

set_option autoImplicit false
set_option pp.maxSteps 10000000
noncomputable section

namespace NlsGge.Measure.BoolHeadTailEquivCoordinatePrerequisiteV1

/-- First coordinate of the actual Bool-indexed block equivalence is its false
(A-head) block. This isolates the finite Bool/Fin-2 bridge from the raw source
reindexing. -/
lemma boolToHeadTailEquiv_fst_apply (A : Set ℤ)
    (f : (b : Bool) → (j : bif b then (Aᶜ : Set ℤ) else A) → ℂ)
    (a : A) :
    (BoolToHeadTailProductAfterEqPiV1.boolToHeadTailEquiv A f).1 a = f false a := by
  change
    (MeasurableEquiv.piFinTwo
      (fun i : Fin 2 =>
        (j : bif (finTwoEquiv i) then (Aᶜ : Set ℤ) else A) → ℂ)
      ((MeasurableEquiv.piCongrLeft
        (fun b : Bool => (j : bif b then (Aᶜ : Set ℤ) else A) → ℂ)
        finTwoEquiv).symm f)).1 a = f false a
  rfl

/-- Second coordinate of the actual Bool-indexed block equivalence is its true
(set-complement) block. -/
lemma boolToHeadTailEquiv_snd_apply (A : Set ℤ)
    (f : (b : Bool) → (j : bif b then (Aᶜ : Set ℤ) else A) → ℂ)
    (i : (Aᶜ : Set ℤ)) :
    (BoolToHeadTailProductAfterEqPiV1.boolToHeadTailEquiv A f).2 i = f true i := by
  change
    (MeasurableEquiv.piFinTwo
      (fun j : Fin 2 =>
        (k : bif (finTwoEquiv j) then (Aᶜ : Set ℤ) else A) → ℂ)
      ((MeasurableEquiv.piCongrLeft
        (fun b : Bool => (j : bif b then (Aᶜ : Set ℤ) else A) → ℂ)
        finTwoEquiv).symm f)).2 i = f true i
  rfl

#check @boolToHeadTailEquiv_fst_apply
#check @boolToHeadTailEquiv_snd_apply

end NlsGge.Measure.BoolHeadTailEquivCoordinatePrerequisiteV1
