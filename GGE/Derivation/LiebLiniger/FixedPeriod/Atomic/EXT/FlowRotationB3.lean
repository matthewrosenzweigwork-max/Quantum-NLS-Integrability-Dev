import LiebLiniger.FixedPeriod.Atomic.EXT.FlowRotationB2

/-! # Explicit real lines in finite complex coordinate planes

Writing each coordinate with complex multiplication avoids identifying the
real Pi scalar action during derivative elaboration. This helper is for the
actual finite-gap Hamiltonian transport proof; that assembly remains open.
-/

set_option autoImplicit false
noncomputable section
namespace LiebLiniger.FixedPeriod.EXT

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38
local notation "B0" =>
  NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38.toBirkhoffTop38
local notation "B" => NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38
local notation "H1" => SobolevCarrier38 ((1 : ℕ) : ℝ)

/-- A real line in a finite complex plane has the prescribed strong real
velocity. Coordinates are written with complex multiplication explicitly. -/
theorem finitePlane_line_hasDerivAt38 (Λ : Finset ℤ) (z η : Λ → ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => fun i : Λ => z i + (s : ℂ) * η i) η t := by
  apply hasDerivAt_pi.2
  intro i
  have hs : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_id t)
  simpa only [one_mul] using (hs.mul_const (η i)).const_add (z i)

end LiebLiniger.FixedPeriod.EXT
