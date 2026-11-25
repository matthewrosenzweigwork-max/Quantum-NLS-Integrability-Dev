import NlsGge.Hierarchy.A01Spectral38
import NlsGge.Hierarchy.RiccatiLocalRemainderPaperForm38
import NlsGge.Hierarchy.RiccatiSmoothDenseSobolev38
import NlsGge.Hierarchy.RiccatiRemainderIntegralForm38
import Mathlib.Tactic

/-! Batch 38, F03 (`B:lem:local`) with the paper's spectral charges.
`E_m(u) = Σ_{j≤m} β_j Q_{2j}(u)` with `Q_{2j}` the trace-normalized charge
(A:eq:trace), and the smooth-field identity of the realized local remainder:
`V(x) = E_m(u) - Σ_n a_{m,n}|û(n)|²` (B:eq:Vm). -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Pilot NlsGge.Sobolev38
open scoped ContDiff

/-- `E_m(U) = Σ_{j≤m} β_j Q_{2j}(U)` with spectral charges. -/
def spectralEnergy38 (M : ℕ) (β : ℕ → ℝ) (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
    (hper : Function.Periodic U 1) : ℝ :=
  ∑ j ∈ Finset.range (M + 1), β j * spectralCharge38 U hU hper j

theorem localEnergy38_eq_spectralEnergy38 (M : ℕ) (β : ℕ → ℝ) (U : ℝ → ℂ)
    (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1) :
    localEnergy38 M β U = spectralEnergy38 M β U hU hper := by
  unfold localEnergy38 spectralEnergy38
  apply Finset.sum_congr rfl
  intro j _
  rw [localCharge_eq_spectralCharge38]

/-- F03 smooth identity with spectral charges: for `M ≥ 2`, the realized
continuous remainder on `H^{M-1}` equals `E_M(u) - Σ_n a_{M,n}|û(n)|²` on the
Sobolev element of every smooth period-one field. -/
theorem localRemainderSobolev38_smooth_spectral (M : ℕ) (hM : 2 ≤ M) (β : ℕ → ℝ)
    (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1)
    (x : SobolevHilbert ((M - 1 : ℕ) : ℝ))
    (hsource : ∀ n : ℤ,
      (show WeightedHilbert (sobolevModeWeight ((M - 1 : ℕ) : ℝ)) from x) n =
        smoothFourier38 u hu hper n) :
    Summable (fun n : ℤ => finiteHierarchyRate38 M β n * ‖smoothFourier38 u hu hper n‖ ^ 2) ∧
      localRemainderSobolev38 M β (toCarrier38 _ x) =
        spectralEnergy38 M β u hu hper -
          ∑' n : ℤ, finiteHierarchyRate38 M β n * ‖smoothFourier38 u hu hper n‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := localRemainderSobolev38_smooth_paperForm M hM β u hu hper x hsource
  exact ⟨h1, by rw [h2, localEnergy38_eq_spectralEnergy38 M β u hu hper]⟩

/-- Uniqueness of the continuous extension, spectral form: any continuous `F` on
`H^{M-1}` equal to `E_M(u) - Σ_n a_{M,n}|û(n)|²` on the Sobolev elements of
smooth period-one fields is the realized remainder. -/
theorem localRemainderSobolev38_unique_spectral (M : ℕ) (hM : 2 ≤ M) (β : ℕ → ℝ)
    (F : SobolevHilbert ((M - 1 : ℕ) : ℝ) → ℝ) (hF : Continuous F)
    (hagree : ∀ (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1)
      (x : SobolevHilbert ((M - 1 : ℕ) : ℝ)),
      (∀ n : ℤ, (show WeightedHilbert (sobolevModeWeight ((M - 1 : ℕ) : ℝ)) from x) n =
        smoothFourier38 u hu hper n) →
      F x = spectralEnergy38 M β u hu hper -
        ∑' n : ℤ, finiteHierarchyRate38 M β n * ‖smoothFourier38 u hu hper n‖ ^ 2) :
    ∀ x : SobolevHilbert ((M - 1 : ℕ) : ℝ), F x = localRemainderSobolev38 M β (toCarrier38 _ x) := by
  refine localRemainderSobolev38_unique M hM β F hF ?_
  intro u hu hper x hx
  rw [hagree u hu hper x hx, ← localEnergy38_eq_spectralEnergy38 M β u hu hper]
  exact (remainderV38_integral_form M β u hu hper).2

/-- "Bounded on bounded subsets" (B:lem:local) on the Sobolev space itself. -/
theorem localRemainderSobolev38_isBounded_image_sobolev (M : ℕ) (β : ℕ → ℝ)
    (S : Set (SobolevHilbert ((M - 1 : ℕ) : ℝ))) (hS : Bornology.IsBounded S) :
    Bornology.IsBounded ((fun x => localRemainderSobolev38 M β (toCarrier38 _ x)) '' S) := by
  obtain ⟨C, hC0, hC⟩ := localRemainderSobolev38_bound M β
  obtain ⟨R, _hR, hnorm⟩ := hS.exists_pos_norm_le
  apply isBounded_iff_forall_norm_le.2
  refine ⟨C * (1 + R ^ (2 * M + 2)), ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [Real.norm_eq_abs]
  refine (hC _).trans (mul_le_mul_of_nonneg_left ?_ hC0)
  rw [norm_toCarrier38]
  gcongr
  exact hnorm y hy

end NlsGge.HierarchyRiccati.Core

end
