import NlsGge.Schur.ResonantIndices
import NlsGge.Spectral.ImaginaryResolventSignedTsumBoundV5

set_option autoImplicit false
noncomputable section

namespace NlsGge.Pilot.ImaginaryResolventSectorKernelBoundV2

open NlsGge.Pilot.ImaginaryResolventKernelAPIProbeV2
open NlsGge.Pilot.ImaginaryResolventSignedTsumBoundV5

/-- Restrict the full signed resolvent kernel to one actual parity sector. -/
def sectorKernel (n : ℤ) (y : ℝ) (m : NlsGge.Schur.Sector n) : ℝ :=
  signedKernel y m.val

/-- A parity restriction cannot increase the nonnegative full signed-lattice
resolvent sum. This retains every sector mode, including zero when it belongs
to the parity class. -/
theorem sectorKernel_tsum_le (n : ℤ) {y : ℝ} (hy : 1 ≤ y) :
    ∑' m : NlsGge.Schur.Sector n, sectorKernel n y m ≤ 2 / y := by
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hfull : Summable (signedKernel y) := signedKernel_summable hypos
  have hsector : Summable (fun m : NlsGge.Schur.Sector n => signedKernel y m.val) :=
    hfull.subtype (fun k : ℤ => k % 2 = n % 2)
  calc
    ∑' m : NlsGge.Schur.Sector n, sectorKernel n y m
        ≤ ∑' k : ℤ, signedKernel y k :=
          hsector.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
            (fun k _ => scalarKernel_nonneg hypos) (fun _ => le_rfl) hfull
    _ ≤ 2 / y := signedKernel_tsum_le hy

end NlsGge.Pilot.ImaginaryResolventSectorKernelBoundV2

end
