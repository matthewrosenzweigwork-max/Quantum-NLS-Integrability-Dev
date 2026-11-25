import Mathlib
import NlsGge.Atomic.DM.DM001
import NlsGge.Atomic.DM.DM002
import NlsGge.Atomic.DM.DM003
import NlsGge.Atomic.DM.DM014
import NlsGge.Atomic.DM.DM019
import NlsGge.Atomic.DM.DM049
import NlsGge.Atomic.KST.KST021
import NlsGge.Atomic.KSTPath
import NlsGge.Atomic.KST.KST007

/- DM-004 PRODUCTION01 (proof development landing kit; HELD). Source proof development/DM004_PROOF01.lean (author proof development; review proof development/REVIEW_DM004_01.md), identical except this line and an added `import Mathlib`. Target NlsGge/Atomic/DM/DM004.lean. -/
/- DM-004 PROOF01 (proof development, AUTHOR; not self-reviewed).
   Statement from STATEMENTS/DM.md DM-004 with TWO REFERENCE REPAIRS ruled by coordinator H1
   (owner auto-approval, audit-logged):
   (a) `NlsGge.ThirdConsultation.KST.Potential` := Pro's abbrev (DEFINITIONS/KST.lean.md:30),
       `abbrev Potential := PhysicalPairLp` with `open NlsGge.Atomic.KST002` (PhysicalPairLp home).
   (b) `NlsGge.Atomic.KST004.majorantCoeff` := `NlsGge.Atomic.KST007.majorantCoeff` (KST007.lean:32).
   dmKstPotential copied verbatim from DEFINITIONS/DM.lean.md:185-186.
   Proof uses KST007.majorant_odd_eq_zero (KST007.lean:50), KSTPath.pathArgument and
   vertexIndex_eq_mk (KSTPath.lean), and the unfolding of pathProduct (KST021.lean:518). -/

set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace NlsGge.ThirdConsultation.KST
open NlsGge.Atomic.KST002
abbrev Potential := PhysicalPairLp
end NlsGge.ThirdConsultation.KST

open NlsGge.Atomic.DM001 NlsGge.Atomic.DM002 NlsGge.Atomic.DM019
open NlsGge.Atomic.DM046 NlsGge.Atomic.DM047 NlsGge.Atomic.DM048
open NlsGge.Atomic.DM049 NlsGge.Atomic.KST001
open NlsGge.ThirdConsultation.KST
namespace NlsGge.ThirdConsultation.DM
noncomputable section

def dmKstPotential (v : PiPairL2) : NlsGge.ThirdConsultation.KST.Potential :=
  WithLp.toLp 2 (fun b => unitPhysical (scaledPotential v b))

/-- Slot 0 of the path argument. -/
theorem dm004_arg_zero {k : ℕ} (hk : 0 < k) (n : ℤ) (ℓ : NlsGge.Atomic.KSTPath.Path k) :
    NlsGge.Atomic.KSTPath.pathArgument hk n ℓ ⟨0, by omega⟩ =
      n + ℓ ⟨0, by omega⟩ := by
  unfold NlsGge.Atomic.KSTPath.pathArgument
  simp only [if_true]
  rw [NlsGge.Atomic.KSTPath.vertexIndex_eq_mk hk (by omega : 0 < 2 * k)]

/-- Interior slot `m+1` is the sum of consecutive path labels. -/
theorem dm004_arg_succ {k : ℕ} (hk : 0 < k) (n : ℤ) (ℓ : NlsGge.Atomic.KSTPath.Path k)
    (m : ℕ) (hm : m + 1 < 2 * k) :
    NlsGge.Atomic.KSTPath.pathArgument hk n ℓ ⟨m + 1, by omega⟩ =
      ℓ ⟨m, by omega⟩ + ℓ ⟨m + 1, hm⟩ := by
  unfold NlsGge.Atomic.KSTPath.pathArgument
  have h1 : ¬ (m + 1 = 0) := by omega
  simp only [h1, if_false, hm, if_true, Nat.add_sub_cancel]
  rw [NlsGge.Atomic.KSTPath.vertexIndex_eq_mk hk (by omega : m < 2 * k),
    NlsGge.Atomic.KSTPath.vertexIndex_eq_mk hk hm]

theorem reduced_paths_parity (v : PiPairL2) (n : ℤ)
    {k : ℕ} (hk : 0 < k) (ell : NlsGge.Atomic.KSTPath.Path k)
    (hterm : NlsGge.ThirdConsultation.KST.pathProduct hk
      (NlsGge.Atomic.KST007.majorantCoeff (dmKstPotential v)) n ell ≠ 0) :
  (∀ i : Fin (2*k), Even ((ell i) - n)) ∧
  (∀ j : Fin (2*k+1),
    Even (NlsGge.Atomic.KSTPath.pathArgument hk n ell j)) := by
  -- the product of majorant factors is nonzero, since pathProduct divides by a product
  have hnum : (∏ j : Fin (2*k+1),
      NlsGge.Atomic.KST007.majorantCoeff (dmKstPotential v)
        (NlsGge.Atomic.KSTPath.pathArgument hk n ell j)) ≠ 0 := by
    intro h0
    apply hterm
    unfold NlsGge.ThirdConsultation.KST.pathProduct
    rw [h0, zero_div]
  -- every slot is even, since the majorant vanishes at odd arguments
  have hev : ∀ j : Fin (2*k+1), Even (NlsGge.Atomic.KSTPath.pathArgument hk n ell j) := by
    intro j
    by_contra hne
    have hodd : NlsGge.Atomic.KSTPath.pathArgument hk n ell j % 2 ≠ 0 :=
      fun h => hne (Int.even_iff.mpr h)
    have hz : NlsGge.Atomic.KST007.majorantCoeff (dmKstPotential v)
        (NlsGge.Atomic.KSTPath.pathArgument hk n ell j) = 0 :=
      NlsGge.Atomic.KST007.majorant_odd_eq_zero (dmKstPotential v) _ hodd
    exact (Finset.prod_ne_zero_iff.mp hnum j (Finset.mem_univ j)) hz
  refine ⟨?_, fun j => hev j⟩
  -- consecutive slot sums force every label to have the parity of n
  have key : ∀ m : ℕ, ∀ h : m < 2 * k, Even (ell ⟨m, h⟩ - n) := by
    intro m
    induction m with
    | zero =>
      intro h
      have h0 := hev ⟨0, by omega⟩
      rw [dm004_arg_zero hk n ell] at h0
      rw [Int.even_iff] at h0 ⊢
      omega
    | succ m ih =>
      intro h
      have ih' := ih (by omega)
      have hs := hev ⟨m + 1, by omega⟩
      rw [dm004_arg_succ hk n ell m h] at hs
      rw [Int.even_iff] at hs ih' ⊢
      omega
  intro i
  exact key i.val i.isLt

end
end NlsGge.ThirdConsultation.DM
