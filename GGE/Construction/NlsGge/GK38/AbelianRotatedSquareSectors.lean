import NlsGge.GK38.AbelianSmoothSquareSector

/-! SOURCE ONLY: actual quarter turns, earned box geometry and exact connectors.
Literal endpoint equalities will yield integral cancellations only AFTER
actual curve/pullback integrabilities and parameter identities are proved.
Exact targets+English preceded proofs. UNCOMPILED, outside four-leaf scope. -/
set_option autoImplicit false
open Set
namespace NlsGge.GK38
noncomputable section

def p6RotatedSquareSector38 (c : ℂ) (r : ℝ) (k : ℕ) (t y : ℝ) : ℂ :=
  c+Complex.I^k*p6SquareSector38 0 r t y

theorem p6RotatedSquareSector_geometry38 (c : ℂ) (r : ℝ) (k : ℕ) (t y : ℝ)
    (hr : 0 ≤ r) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hy : |y| ≤ 1) :
    r ≤ ‖p6RotatedSquareSector38 c r k t y-c‖ ∧
    |(p6RotatedSquareSector38 c r k t y).re-c.re| ≤ r ∧
    |(p6RotatedSquareSector38 c r k t y).im-c.im| ≤ r := by
  let z0 : ℂ := p6SquareSector38 0 r t y
  have hg : r ≤ ‖z0‖ ∧ |z0.re| ≤ r ∧ |z0.im| ≤ r := by
    simpa [z0] using p6SquareSector_geometry38 0 r t y hr ht hy
  have hbox : ∀ j : ℕ, |(Complex.I^j*z0).re| ≤ r ∧ |(Complex.I^j*z0).im| ≤ r := by
    intro j
    induction j with
    | zero => simpa using ⟨hg.2.1,hg.2.2⟩
    | succ j ih =>
        have he : Complex.I^(j+1)*z0 = Complex.I*(Complex.I^j*z0) := by
          rw [pow_succ]
          ring
        rw [he]
        constructor
        · simpa only [Complex.I_mul_re,abs_neg] using ih.2
        · simpa only [Complex.I_mul_im] using ih.1
  have hnorm : ‖p6RotatedSquareSector38 c r k t y-c‖ = ‖z0‖ := by
    simp [p6RotatedSquareSector38,z0,norm_pow]
  refine ⟨hnorm.symm ▸ hg.1, ?_, ?_⟩
  · simpa [p6RotatedSquareSector38,z0] using (hbox k).1
  · simpa [p6RotatedSquareSector38,z0] using (hbox k).2

theorem p6RotatedSquareSector_contDiff38 (c : ℂ) (r : ℝ) (k : ℕ) :
    ContDiff ℝ 2 (fun p : ℝ × ℝ => p6RotatedSquareSector38 c r k p.1 p.2) := by
  exact contDiff_const.add (contDiff_const.mul (p6SquareSector_contDiff38 0 r))

theorem p6RotatedSquareSector_connector38 (c : ℂ) (r t : ℝ) (k : ℕ) :
    p6RotatedSquareSector38 c r k t 1 = p6RotatedSquareSector38 c r (k+1) t (-1) := by
  have hconn : p6SquareSector38 0 r t 1 = Complex.I*p6SquareSector38 0 r t (-1) := by
    simpa using p6SquareSector_endpoint_rotation38 0 r t
  simp only [p6RotatedSquareSector38,pow_succ,hconn]
  ring

theorem p6RotatedSquareSector_period_four38 (c : ℂ) (r t y : ℝ) (k : ℕ) :
    p6RotatedSquareSector38 c r (k+4) t y = p6RotatedSquareSector38 c r k t y := by
  simp [p6RotatedSquareSector38,pow_add]

end
end NlsGge.GK38
