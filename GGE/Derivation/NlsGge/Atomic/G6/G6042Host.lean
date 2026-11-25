import Mathlib
import NlsGge.Birkhoff.BirkhoffAPI38

/- G6042 HOST PRODUCTION01 (proof development, AUTHOR; not reviewed). Proposed target NlsGge/Atomic/G6/G6042Host.lean,
   namespace NlsGge.GKDefinitionDesign. Hosts ONCE the G6 design names used by the G6-042 head:
   coordinateDirection_mem, coordinateDirection, coordinateHamiltonianField, coordinatePoisson, coordinateAction
   (followup13 DEFINITIONS/G6.lean.md l.313-336, bodies verbatim). grep NlsGge/ (2026-11-02): none of these names exists.
   LEXICAL/ELABORATION REPAIR (root lexical repair 20, uniform ((1 : ℕ) : ℝ) carrier index, as in landed G6-034/G6035Host):
   - coordinateDirection body: `carrierMk38 1 (Pi.single n a) (coordinateDirection_mem n a)` ->
     `carrierMk38 ((1 : ℕ) : ℝ) (Pi.single n a) (by rw [Nat.cast_one]; exact coordinateDirection_mem n a)`
     (declared type SobolevCarrier38 ((1 : ℕ) : ℝ) is Pro's; `(1 : ℝ)` and `((1 : ℕ) : ℝ)` are not definitionally equal);
   - coordinateAction body: `carrierCoe38 1 z n` -> `carrierCoe38 ((1 : ℕ) : ℝ) z n`.
   coordinateDirection_mem (statement verbatim) is a theorem without a printed proof; proved here (finite support). -/
set_option autoImplicit false
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem coordinateDirection_mem (n : ℤ) (a : ℂ) :
  Pi.single n a ∈ seqSobolev38 (1 : ℝ) := by
  rw [mem_seqSobolev38_iff]
  unfold SobolevSquareSummable
  refine summable_of_ne_finset_zero (s := {n}) (fun m hm => ?_)
  rw [Finset.mem_singleton] at hm
  simp [Pi.single_apply, hm]

def coordinateDirection (n : ℤ) (a : ℂ) : SobolevCarrier38 ((1 : ℕ) : ℝ) :=
  carrierMk38 ((1 : ℕ) : ℝ) (Pi.single n a) (by rw [Nat.cast_one]; exact coordinateDirection_mem n a)

/-- Coordinate of the Hamiltonian vector field; it need not assemble to h^1. -/
def coordinateHamiltonianField (H : SobolevCarrier38 ((1 : ℕ) : ℝ) → ℝ)
    (z : SobolevCarrier38 ((1 : ℕ) : ℝ)) (n : ℤ) : ℂ :=
  -(Complex.I / 2) *
    ((fderiv ℝ H z (coordinateDirection n 1) : ℝ) +
      Complex.I * (fderiv ℝ H z (coordinateDirection n Complex.I) : ℝ))

def coordinatePoisson (n : ℤ) (f g : SobolevCarrier38 ((1 : ℕ) : ℝ) → ℝ)
    (z : SobolevCarrier38 ((1 : ℕ) : ℝ)) : ℝ :=
  (1 / 2 : ℝ) *
    (fderiv ℝ f z (coordinateDirection n 1) *
      fderiv ℝ g z (coordinateDirection n Complex.I) -
     fderiv ℝ f z (coordinateDirection n Complex.I) *
      fderiv ℝ g z (coordinateDirection n 1))

def coordinateAction (n : ℤ) (z : SobolevCarrier38 ((1 : ℕ) : ℝ)) : ℝ :=
  ‖carrierCoe38 ((1 : ℕ) : ℝ) z n‖^2

end
end NlsGge.GKDefinitionDesign
