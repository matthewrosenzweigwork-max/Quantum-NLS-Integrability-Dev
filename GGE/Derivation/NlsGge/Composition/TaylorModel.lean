import NlsGge.Composition.TaylorDecay
import NlsGge.Composition.Model

/-!
# W03.07: the Taylor coefficients `B_k = D^kF(p(θ))/k!` lie in `A_w(L^k(X;Y))`

Source: `paper/v2.tex`, lines 1466-1473:
`‖B_k‖_{A_w(L^k(X;Y))} ≤ D_η M ρ^{-k}` with `D_η² = ∑ w_n² e^{-η|n|}` independent of `k`.
Here (real route, see STATUS.md): `awNorm w B_k ≤ 2 M (2/ρ)^k D` with
`D² = ∑ w_n² e^{-2π s |n|}`, `s > 0` depending on the trigonometric polynomial only.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace NlsGge.Composition

open AddCircle

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
variable {w : ℤ → ℝ}

/-- `B_k(θ) = D^kF(γ(θ))/k!` along the trigonometric curve `γ(θ) = ∑_{m∈S} e_m(θ) v_m`. -/
def taylorFun (F : X → Y) (S : Finset ℤ) (v : ℤ → X) (k : ℕ) (θ : AddCircle (1 : ℝ)) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => X) Y :=
  (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k F (∑ m ∈ S, fourier m θ • v m)

theorem taylorFun_memAw (hw : AdmissibleWeight w) {F : X → Y} {K : Set X} {δ ρ M : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hM : 0 ≤ M)
    (hdata : ∀ y ∈ Metric.thickening δ K, ∃ p : FormalMultilinearSeries ℝ X Y,
        HasFPowerSeriesOnBall F p y (ENNReal.ofReal ρ) ∧ ∀ n, ‖p n‖ ≤ M * ρ⁻¹ ^ n)
    (S : Finset ℤ) (v : ℤ → X)
    (hγ : ∀ θ : AddCircle (1 : ℝ), (∑ n ∈ S, fourier n θ • v n) ∈ Metric.thickening δ K) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ k : ℕ, MemAw w (taylorFun F S v k) ∧
      awNorm w (taylorFun F S v k) ≤ 2 * M * (2 / ρ) ^ k * D := by
  obtain ⟨s, hs, hdec⟩ := taylorCoeff_fourier_decay hδ hρ hM hdata S v hγ
  have hc : 0 < 2 * Real.pi * s := by positivity
  have hsum := hw.exp_decay (2 * Real.pi * s) hc
  set D : ℝ := Real.sqrt (∑' n : ℤ, w n ^ 2 * Real.exp (-(2 * Real.pi * s) * |(n : ℝ)|)) with hD
  refine ⟨D, Real.sqrt_nonneg _, fun k => ?_⟩
  set c : ℝ := 2 * M * (2 / ρ) ^ k with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hpt : ∀ n : ℤ, (w n * ‖fourierCoeff (taylorFun F S v k) n‖) ^ 2 ≤
      c ^ 2 * (w n ^ 2 * Real.exp (-(2 * Real.pi * s) * |(n : ℝ)|)) := by
    intro n
    have h1 := hdec k n
    have hwn := (hw.pos n).le
    have h2 : w n * ‖fourierCoeff (taylorFun F S v k) n‖ ≤
        w n * (c * Real.exp (-(Real.pi * s) * |(n : ℝ)|)) := by
      gcongr; exact h1
    have h0 : 0 ≤ w n * ‖fourierCoeff (taylorFun F S v k) n‖ := by positivity
    calc (w n * ‖fourierCoeff (taylorFun F S v k) n‖) ^ 2
        ≤ (w n * (c * Real.exp (-(Real.pi * s) * |(n : ℝ)|))) ^ 2 := by gcongr
      _ = c ^ 2 * (w n ^ 2 * Real.exp (-(2 * Real.pi * s) * |(n : ℝ)|)) := by
          rw [mul_pow, mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
  have hS : Summable fun n : ℤ => (w n * ‖fourierCoeff (taylorFun F S v k) n‖) ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hpt (hsum.mul_left _)
  refine ⟨⟨taylorCoeff_continuous hdata S v hγ k, hS⟩, ?_⟩
  unfold awNorm
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  calc ∑' n, (w n * ‖fourierCoeff (taylorFun F S v k) n‖) ^ 2
      ≤ ∑' n : ℤ, c ^ 2 * (w n ^ 2 * Real.exp (-(2 * Real.pi * s) * |(n : ℝ)|)) :=
        hS.tsum_le_tsum hpt (hsum.mul_left _)
    _ = (c * D) ^ 2 := by
        rw [tsum_mul_left, mul_pow (c) D, hD, Real.sq_sqrt (tsum_nonneg fun n => by positivity)]

end NlsGge.Composition
