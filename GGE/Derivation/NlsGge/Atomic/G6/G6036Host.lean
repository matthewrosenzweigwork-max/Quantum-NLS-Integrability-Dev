import Mathlib
import NlsGge.Atomic.G6.G6034Host
import NlsGge.Atomic.G6.G6033Host
import NlsGge.Atomic.LIB.LIB003

/- G6036 HOST PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G6/G6036Host.lean.
   Hosts ONCE the G6-036 design names (R14_AUDIT_B row G6-036: "HOSTABLE ... through diagonalHamiltonian;
   diagonalSequence_mem obligation"), from followup13 DEFINITIONS/G6.lean.md:212 (RealDiagonalSpace) and 256-269,
   namespace NlsGge.GKDefinitionDesign: RealDiagonalSpace, diagonalPhase, the constructor obligation
   diagonalSequence_mem (proved here: ‖diagonalPhase‖ = 1 and ⟨n⟩²·(x_n/⟨n⟩)² = x_n², then LIB-003 weighted membership),
   diagonalToSobolev, diagonalHamiltonian.  actionWeight is the landed G6034Host one; transformedNLSHamiltonian is the
   landed G6033Host one.
   LEXICAL/ELABORATION REPAIR (root lexical repair 20, uniform ((1 : ℕ) : ℝ) carrier index; same as G6035Host's
   positiveActionRoot): diagonalToSobolev body `carrierMk38 1 f (diagonalSequence_mem x)` ->
   `carrierMk38 ((1 : ℕ) : ℝ) f (by rw [Nat.cast_one]; exact diagonalSequence_mem x)`; the obligation head keeps
   `seqSobolev38 1`.  grep NlsGge/ (2026-11-02): none of these names exists. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

abbrev RealDiagonalSpace := lp (fun _ : ℤ => ℝ) 2

/-- x=y in the real Cartesian coordinates corresponds to this physical phase. -/
def diagonalPhase : ℂ := (1 - Complex.I) / (Real.sqrt 2 : ℂ)

theorem diagonalSequence_mem (x : RealDiagonalSpace) :
  (fun n : ℤ => diagonalPhase * ((x n / Real.sqrt (actionWeight n) : ℝ) : ℂ)) ∈
    seqSobolev38 1 := by
  apply NlsGge.Atomic.LIB003.weightedSequence_mem_seqSobolev38
  have hph : ‖diagonalPhase‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, diagonalPhase, map_div₀, Complex.normSq_ofReal,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Complex.normSq_apply]
    simp
  have he : (fun n : ℤ => sobolevModeWeight 1 n *
      ‖diagonalPhase * ((x n / Real.sqrt (actionWeight n) : ℝ) : ℂ)‖ ^ 2) = fun n => x n ^ 2 := by
    funext n
    have hw : 0 < actionWeight n := sobolevModeWeight_pos 1 n
    have e : sobolevModeWeight 1 n = actionWeight n := rfl
    rw [norm_mul, mul_pow, hph, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow,
      Real.sq_sqrt hw.le, e]
    field_simp
  rw [he]
  have h := (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using h

def diagonalToSobolev (x : RealDiagonalSpace) : SobolevCarrier38 ((1 : ℕ) : ℝ) :=
  carrierMk38 ((1 : ℕ) : ℝ)
    (fun n => diagonalPhase * ((x n / Real.sqrt (actionWeight n) : ℝ) : ℂ))
    (by rw [Nat.cast_one]; exact diagonalSequence_mem x)

def diagonalHamiltonian (x : RealDiagonalSpace) : ℝ :=
  transformedNLSHamiltonian (diagonalToSobolev x)

end
end NlsGge.GKDefinitionDesign
