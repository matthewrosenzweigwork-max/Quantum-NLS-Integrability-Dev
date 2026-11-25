import Mathlib
import NlsGge.Birkhoff.F11Claim38f
import NlsGge.ThirdConsultation.T.TDefs2Host
import NlsGge.ThirdConsultation.I.ActualEnsembleBridge
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing

/- T-020 PRODUCTION01 (proof development, AUTHOR; not compiled or reviewed).
   Target: NlsGge/Atomic/T/T020.lean, namespace NlsGge.ThirdConsultation.T.
   Reindexes the finite Finset product as a Fin product and specializes the
   landed F11_moments38 theorem to the concrete PDE Birkhoff and smoothing
   inputs. The target head is unchanged. -/

set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators ContDiff
open scoped BoundedContinuousFunction
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Sobolev38
open NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core
open NlsGge.ThirdConsultation.Common

namespace NlsGge.ThirdConsultation.T
noncomputable section

theorem fullFourier_fixedCharge_moments_tendsto
    (lo up : ℝ) (c : BoundedCoefficients lo up)
    (indices : Finset ℕ) (powers : ℕ → ℕ) :
    (∀ N : ℕ, Integrable (chargeMonomial indices powers) (fullFourierLaw c N)) ∧
    Integrable (chargeMonomial indices powers) (muW c) ∧
    Tendsto (fun N : ℕ => ∫ u, chargeMonomial indices powers u
      ∂fullFourierLaw c N) atTop
      (𝓝 (∫ u, chargeMonomial indices powers u ∂muW c)) := by
  classical
  let m : ℕ := evenProductOrder indices + 1
  have hmJ : 1 ≤ evenProductOrder indices := by
    unfold evenProductOrder
    exact Nat.le_max_left 1 _
  have hm : 2 ≤ m := by
    dsimp [m]
    omega
  let n : ℕ := indices.card
  let e : Fin n ≃ {j // j ∈ indices} := (Finset.equivFin indices).symm
  let jj : Fin n → ℕ := fun i => (e i).val
  let p : Fin n → ℕ := fun i => powers (jj i)
  have hjj : ∀ i : Fin n, jj i ≤ m - 1 := by
    intro i
    have hsup : (e i).val ≤ indices.sup id :=
      Finset.le_sup (f := id) (e i).property
    have horder : (e i).val ≤ evenProductOrder indices := by
      unfold evenProductOrder
      exact hsup.trans (Nat.le_max_right 1 _)
    simpa [m, jj] using horder
  have hmonomial : chargeMonomial indices powers =
      (fun u : PhysicalL2 => ∏ i : Fin n, chargeFn38 m (jj i) u ^ p i) := by
    funext u
    change (∏ j ∈ indices, (chargeFn38 m j u) ^ powers j) =
      ∏ i : Fin n, chargeFn38 m (jj i) u ^ p i
    calc
      (∏ j ∈ indices, (chargeFn38 m j u) ^ powers j) =
          ∏ j : {j // j ∈ indices}, (chargeFn38 m j.1 u) ^ powers j.1 := by
            symm
            exact Finset.prod_coe_sort indices
              (fun j : ℕ => (chargeFn38 m j u) ^ powers j)
      _ = ∏ i : Fin n, chargeFn38 m (jj i) u ^ p i := by
            exact Fintype.prod_equiv e.symm
              (fun j : {j // j ∈ indices} => (chargeFn38 m j.1 u) ^ powers j.1)
              (fun i : Fin n => chargeFn38 m (jj i) u ^ p i)
              (by intro j; simp [jj, p])
  have hmuW : NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38.muW38 c.val = muW c := by
    change NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38.toBirkhoffTop38.muW38 c.val =
      NlsGge.ThirdConsultation.I.physicalLaw (weight c.val)
    rw [NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38_top]
    change NlsGge.ThirdConsultation.PDE.actualMuW c.val =
      NlsGge.ThirdConsultation.I.physicalLaw (weight c.val)
    exact (NlsGge.ThirdConsultation.I.actual_ensemble_eq_I lo up c).2.2.1
  have hMoments :=
    NlsGge.Birkhoff.BirkhoffInput38.F11_moments38
      NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38
      NlsGge.ThirdConsultation.PDE.actualOneSmoothingInput38
      c m hm n jj hjj p
  refine ⟨?_, ?_, ?_⟩
  · intro N
    simpa only [fullFourierLaw, ← hmonomial] using hMoments.1 N
  · simpa only [← hmonomial, ← hmuW] using hMoments.2.1
  · simpa only [fullFourierLaw, ← hmonomial, ← hmuW] using hMoments.2.2

end
end NlsGge.ThirdConsultation.T
