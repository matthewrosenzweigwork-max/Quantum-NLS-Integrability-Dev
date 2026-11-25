import NlsGge.Spectral.ActualGapsActionsE02_38
import NlsGge.Spectral.ActualOriginalPhysicalUnitTraceSourceCorrespondenceV4
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis TransportBridgeV4

/-! # Floquet link and opposite-parity exclusion (campaign 38, for the Schur thread)

Existing link (`actualReflectedPhysicalL2UnitTrace_iff_source_eigenvector` and
`actualPhysicalL2ZsUnitTrace_neg_potential`): `z` is an eigenvalue of the sector-`m` source
operator `actualSourcePerturbedDiracPMapAfterAE m u (star u)` iff
`Δh u (-z) = spectralSign m`. Note the REFLECTED argument `-z`. -/

theorem spectralSign_eq_cos_E02_38 (m : ℤ) :
    spectralSign m = (Real.cos ((m:ℝ)*Real.pi) : ℂ) := by
  rw [Real.cos_int_mul_pi]
  rcases Int.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · have h : m % 2 = 0 := by omega
    simp [spectralSign, h, hk, ← two_mul, zpow_mul]
  · have h : m % 2 ≠ 0 := by omega
    simp [spectralSign, h, hk, zpow_add₀, zpow_mul]

/-- Floquet link in half-trace form: sector-`m` eigenvalue `z` ⟺ `Δh u (-z) = spectralSign m`. -/
theorem actualSourceEigenvalue_iff_halfTrace_E02_38 (m : ℤ) (u : PhysicalL2) (z : ℂ) :
    (∃ X : recoveredActualSourceFreeWeightedDomain m, X.val ≠ 0 ∧
      actualSourcePerturbedDiracPMapAfterAE m u (star u) X = z • X.val) ↔
    actualPhysicalUnitHalfTrace32 u (-z) = spectralSign m := by
  rw [← actualReflectedPhysicalL2UnitTrace_iff_source_eigenvector m u z,
    actualPhysicalL2ZsUnitTrace_neg_potential u (-z) 1 (by norm_num)]
  unfold actualPhysicalUnitHalfTrace32
  constructor
  · intro h; rw [h]; ring
  · intro h
    rw [← h]; ring

/-- Opposite-parity exclusion: under the box hypothesis at `-n` (reflected window), the
sector-`(n+1)` operator has no eigenvalue `z` with `|Re z - nπ| ≤ 1`. -/
theorem no_oppositeParity_eigenvalue_E02_38 (u : PhysicalL2) (n : ℤ) (δ : ℝ)
    (hδ : δ ≤ 1/1000) (hbox : ActualHalfTraceBoxE02_38 u (-n) δ) (z : ℂ)
    (hz : |z.re - (n:ℝ)*Real.pi| ≤ 1) :
    ¬ ∃ X : recoveredActualSourceFreeWeightedDomain (n+1), X.val ≠ 0 ∧
      actualSourcePerturbedDiracPMapAfterAE (n+1) u (star u) X = z • X.val := by
  rintro ⟨X, hX, heig⟩
  have him : z.im = 0 := actualSourcePerturbedDirac_eigenvalue_im_eq_zero (n+1) u z X hX heig
  have htr := (actualSourceEigenvalue_iff_halfTrace_E02_38 (n+1) u z).mp ⟨X, hX, heig⟩
  have hcos1 : Real.cos (((n+1:ℤ):ℝ)*Real.pi) = -Real.cos ((n:ℝ)*Real.pi) := by
    push_cast; rw [add_mul, one_mul, Real.cos_add_pi]
  have hs : spectralSign (n+1) = ((-Real.cos ((n:ℝ)*Real.pi) : ℝ) : ℂ) := by
    rw [spectralSign_eq_cos_E02_38, hcos1]
  rw [hs] at htr
  have hb := hbox (-z) (by
      simp only [Complex.neg_re, Int.cast_neg, neg_mul]
      rw [show -z.re - -((n:ℝ)*Real.pi) = -(z.re - n*Real.pi) by ring, abs_neg]; exact hz)
    (by simp [him])
  rw [htr] at hb
  have hw : -z = ((-z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him]
  rw [hw, ← Complex.ofReal_cos, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] at hb
  set c := Real.cos ((n:ℝ)*Real.pi)
  have hc2 : c^2 = 1 := real_cos_int_mul_pi_sq_E02_38 n
  -- c * cos(-z.re) = cos(z.re - nπ) ≥ cos 1 ≥ 1/2
  have hprod : c * Real.cos (-z.re) = Real.cos (z.re - (n:ℝ)*Real.pi) := by
    rw [Real.cos_neg, Real.cos_sub, Real.sin_int_mul_pi]; ring
  have hge : 1/2 ≤ Real.cos (z.re - (n:ℝ)*Real.pi) := by
    have := Real.one_sub_sq_div_two_le_cos (x := z.re - (n:ℝ)*Real.pi)
    have h2 : (z.re - (n:ℝ)*Real.pi)^2 ≤ 1 := by
      have := sq_abs (z.re - (n:ℝ)*Real.pi)
      nlinarith [abs_nonneg (z.re - (n:ℝ)*Real.pi)]
    linarith
  have habs := abs_le.mp hb
  -- multiply (-c - cos(-z.re)) by c: -1 - c cos(-z.re)
  have hmul : |c * (-c - Real.cos (-z.re))| ≤ δ := by
    rw [abs_mul]
    have : |c| = 1 := by
      have h := sq_abs c; rw [hc2] at h
      nlinarith [abs_nonneg c, sq_nonneg (|c| - 1)]
    rw [this, one_mul]; exact hb
  have hexp : c * (-c - Real.cos (-z.re)) = -1 - Real.cos (z.re - (n:ℝ)*Real.pi) := by
    rw [← hprod]; nlinarith [hc2]
  rw [hexp] at hmul
  have := (abs_le.mp hmul).1
  linarith

end NlsGge.SpectralFoundations
end
