import Mathlib
import NlsGge.Atomic.T.T011
import NlsGge.Atomic.T.T018
import NlsGge.Atomic.T.T019
import NlsGge.Atomic.T.T020
import NlsGge.Atomic.T.T021
import NlsGge.Atomic.T.T022
import NlsGge.Birkhoff.SignedMoments38g
import NlsGge.ThirdConsultation.T.TDefs2Host
import NlsGge.ThirdConsultation.I.ActualEnsembleBridge
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing

/- T-023 PRODUCTION05 (proof development, author draft; not compiled or reviewed).
   Target: NlsGge/Atomic/T/T023.lean, namespace NlsGge.ThirdConsultation.T.
   Reindexes the finite signed/even products and specializes the concrete
   signedMoments_38 producer. The source head is unchanged. -/

set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators ContDiff
open scoped BoundedContinuousFunction
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Sobolev38
open NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core
open NlsGge.ThirdConsultation.Common

namespace NlsGge.ThirdConsultation.T
noncomputable section

theorem fullFourier_signedCharge_moments_tendsto
    (lo up : ℝ) (c : BoundedCoefficients lo up)
    (signedIndices evenIndices : Finset ℕ)
    (powersSigned powersEven : ℕ → ℕ) :
    (∀ N : ℕ, Integrable
      (signedChargeMonomial signedIndices evenIndices powersSigned powersEven)
      (fullFourierLaw c N)) ∧
    Integrable (signedChargeMonomial signedIndices evenIndices powersSigned powersEven)
      (muW c) ∧
    Tendsto (fun N : ℕ => ∫ u,
      signedChargeMonomial signedIndices evenIndices powersSigned powersEven u
        ∂fullFourierLaw c N) atTop
      (𝓝 (∫ u, signedChargeMonomial signedIndices evenIndices powersSigned powersEven u
        ∂muW c)) := by
  classical
  let r : ℕ := mixedProductOrder signedIndices evenIndices
  let m : ℕ := r + 1
  have hr : 1 ≤ r := by
    dsimp [r, mixedProductOrder]
    exact Nat.le_max_left 1 _
  have hm : 2 ≤ m := by
    dsimp [m]
    omega
  let signedSlot : Type := {j : ℕ // j ∈ signedIndices}
  let evenSlot : Type := {j : ℕ // j ∈ evenIndices}
  let n : ℕ := Fintype.card (signedSlot ⊕ evenSlot)
  let e : Fin n ≃ (signedSlot ⊕ evenSlot) :=
    (Fintype.equivFin (signedSlot ⊕ evenSlot)).symm
  let kk : Fin n → ℕ := fun i =>
    match e i with
    | Sum.inl j => 2 * j.1 + 1
    | Sum.inr j => 2 * j.1
  let p : Fin n → ℕ := fun i =>
    match e i with
    | Sum.inl j => powersSigned j.1
    | Sum.inr j => powersEven j.1
  have hkk : ∀ i, kk i ≤ 2 * m - 2 := by
    intro i
    cases hcase : e i with
    | inl j =>
      have hsup : j.1 + 1 ≤ signedIndices.sup (fun j : ℕ => j + 1) :=
        Finset.le_sup (f := fun j : ℕ => j + 1) j.2
      have horder : j.1 + 1 ≤ r := by
        calc
          j.1 + 1 ≤ signedIndices.sup (fun j : ℕ => j + 1) := hsup
          _ ≤ r := by
            dsimp [r, mixedProductOrder]
            exact (Nat.le_max_right _ _).trans (Nat.le_max_right 1 _)
      rw [show kk i = 2 * j.1 + 1 by simp [kk, hcase]]
      calc
        2 * j.1 + 1 ≤ 2 * r := by omega
        _ = 2 * m - 2 := by dsimp [m]; omega
    | inr j =>
      have hsup : j.1 ≤ evenIndices.sup id :=
        Finset.le_sup (f := id) j.2
      have horder : j.1 ≤ r := by
        calc
          j.1 ≤ evenIndices.sup id := hsup
          _ ≤ r := by
            dsimp [r, mixedProductOrder]
            exact (Nat.le_max_left _ _).trans (Nat.le_max_right 1 _)
      rw [show kk i = 2 * j.1 by simp [kk, hcase]]
      calc
        2 * j.1 ≤ 2 * r := by omega
        _ = 2 * m - 2 := by dsimp [m]; omega
  have hprod (u : PhysicalL2) :
      (∏ j ∈ signedIndices, (oddChargeFn38 m j u) ^ powersSigned j) *
        ∏ j ∈ evenIndices, (chargeFn38 m j u) ^ powersEven j =
      ∏ i : Fin n, signedChargeFn38 m (kk i) u ^ p i := by
    let f : signedSlot ⊕ evenSlot → ℝ := fun x =>
      match x with
      | Sum.inl j => oddChargeFn38 m j.1 u ^ powersSigned j.1
      | Sum.inr j => chargeFn38 m j.1 u ^ powersEven j.1
    let g : Fin n → ℝ := fun i => signedChargeFn38 m (kk i) u ^ p i
    have hS :
        (∏ j ∈ signedIndices, (oddChargeFn38 m j u) ^ powersSigned j) =
          ∏ j : signedSlot, f (Sum.inl j) := by
      exact (Finset.prod_coe_sort signedIndices
        (fun j : ℕ => oddChargeFn38 m j u ^ powersSigned j)).symm
    have hE :
        (∏ j ∈ evenIndices, (chargeFn38 m j u) ^ powersEven j) =
          ∏ j : evenSlot, f (Sum.inr j) := by
      exact (Finset.prod_coe_sort evenIndices
        (fun j : ℕ => chargeFn38 m j u ^ powersEven j)).symm
    have hsum :
        (∏ x : signedSlot ⊕ evenSlot, f x) = ∏ i : Fin n, g i := by
      exact Fintype.prod_equiv e.symm f g (by
        intro x
        cases x with
        | inl j => simp [f, g, kk, p, signedChargeFn38_odd]
        | inr j => simp [f, g, kk, p, signedChargeFn38_even])
    calc
      _ = (∏ j : signedSlot, f (Sum.inl j)) *
          ∏ j : evenSlot, f (Sum.inr j) := by rw [hS, hE]
      _ = ∏ x : signedSlot ⊕ evenSlot, f x :=
        (Fintype.prod_sum_type f).symm
      _ = ∏ i : Fin n, g i := hsum
  have hmonomial :
      signedChargeMonomial signedIndices evenIndices powersSigned powersEven =
        (fun u : PhysicalL2 =>
          ∏ i : Fin n, signedChargeFn38 m (kk i) u ^ p i) := by
    funext u
    change
      (∏ j ∈ signedIndices, (oddChargeFn38 (r + 1) j u) ^ powersSigned j) *
        ∏ j ∈ evenIndices, (chargeFn38 (r + 1) j u) ^ powersEven j =
      ∏ i : Fin n, signedChargeFn38 m (kk i) u ^ p i
    exact hprod u
  have hmuW :
      NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38.muW38 c.val = muW c := by
    change NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38.toBirkhoffTop38.muW38 c.val =
      NlsGge.ThirdConsultation.I.physicalLaw (weight c.val)
    rw [NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38_top]
    change NlsGge.ThirdConsultation.PDE.actualMuW c.val =
      NlsGge.ThirdConsultation.I.physicalLaw (weight c.val)
    exact (NlsGge.ThirdConsultation.I.actual_ensemble_eq_I lo up c).2.2.1
  have hMoments :=
    NlsGge.Birkhoff.BirkhoffInput38.signedMoments_38
      NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38
      NlsGge.ThirdConsultation.PDE.actualOneSmoothingInput38
      c m hm n kk hkk p
  refine ⟨?_, ?_, ?_⟩
  · intro N
    simpa only [fullFourierLaw, ← hmonomial] using hMoments.1 N
  · simpa only [← hmonomial, ← hmuW] using hMoments.2.1
  · simpa only [fullFourierLaw, ← hmonomial, ← hmuW] using hMoments.2.2

end
end NlsGge.ThirdConsultation.T
