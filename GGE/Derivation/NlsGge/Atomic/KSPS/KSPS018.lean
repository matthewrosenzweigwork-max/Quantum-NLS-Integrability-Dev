import Mathlib
import NlsGge.Atomic.KSPS.KSPS006
import NlsGge.ThirdConsultation.KSPS.KSPS018Host
import NlsGge.ThirdConsultation.KSPS.KSPS018Support

/- KSPS-018 PRODUCTION01 (proof development, AUTHOR; not reviewed; target NlsGge/Atomic/KSPS/KSPS018.lean).
   Head: STATEMENTS/KSPS.md "KSPS-018 -- rough spectral derivatives on a fixed strip" (followup9; same text since round 1;
   no Pro round 5-11 response touches KSPS-018), VERBATIM as `spectral_derivative_rough`: C and Lambda are chosen after
   (j, B, LambdaIm) and BEFORE phi and lam, as printed. The head object `KSPSWKB.supMatrixDerivativeError` has no Pro body;
   its PROPOSED body is in KSPS018Host (see the comment there).
   Totalization: the derivative bound is a statement about genuinely differentiable functions. lam -> M(x,lam) and lam -> E(x,lam) are
   analytic on all of C (KSPS018Support.analyticOnNhd_fundamental via the G1-004 series), so `iteratedDeriv` is the true
   derivative, and the family over x is bounded, so the real iSup is the true supremum (`spectral_derivative_rough_complete`).
   Route (differs from the source's variation of constants; see KSPS018_ROUTE.md): j = 0 bound on a complex disc from KSPS-005
   plus the H1 integration by parts, then Cauchy estimates (radius 1/2, twice) for j = 1, 2. -/
set_option autoImplicit false

open scoped Matrix.Norms.L2Operator

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem spectral_derivative_rough (j : Fin 3) :
  ∀ B LambdaIm : ℝ, 0 ≤ B → 0 ≤ LambdaIm →
    ∃ C Lambda : ℝ, 0 ≤ C ∧ 0 < Lambda ∧
    ∀ φ : SobolevC 1, sobolevNorm 1 φ ≤ B →
    ∀ lam : ℂ, Lambda ≤ ‖lam‖ → |lam.im| ≤ LambdaIm →
      NlsGge.ThirdConsultation.KSPSWKB.supMatrixDerivativeError
        j φ lam ≤ C/‖lam‖ := by
  intro B LambdaIm hB hΛ
  obtain ⟨C, Lam, hC, hLam, h⟩ :=
    NlsGge.ThirdConsultation.KSPS018Support.spectral_derivative_rough_pointwise j B LambdaIm hB hΛ
  refine ⟨C, Lam, hC, hLam, fun φ hφ lam hlam him => ?_⟩
  haveI : Nonempty (Set.Icc (0 : ℝ) 1) := ⟨⟨0, le_rfl, zero_le_one⟩⟩
  exact ciSup_le fun x => h φ hφ lam hlam him x x.2

/-- The error of each fixed `x` lies below the supremum once the family is bounded (the real `iSup` is totalized). -/
theorem le_supMatrixDerivativeError (j : Fin 3) (φ : SobolevC 1) (lam : ℂ) {K : ℝ}
    (hK : ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
      ‖iteratedDeriv (j : ℕ) (fun l : ℂ => NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ x l) lam -
        iteratedDeriv (j : ℕ) (fun l : ℂ => freePropagator x l) lam‖ ≤ K)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ‖iteratedDeriv (j : ℕ) (fun l : ℂ => NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ x l) lam -
        iteratedDeriv (j : ℕ) (fun l : ℂ => freePropagator x l) lam‖ ≤
      NlsGge.ThirdConsultation.KSPSWKB.supMatrixDerivativeError j φ lam :=
  le_ciSup (f := fun y : Set.Icc (0 : ℝ) 1 =>
    ‖iteratedDeriv (j : ℕ) (fun l : ℂ => NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ (y : ℝ) l) lam -
      iteratedDeriv (j : ℕ) (fun l : ℂ => freePropagator (y : ℝ) l) lam‖)
    ⟨K, by rintro _ ⟨y, rfl⟩; exact hK y y.2⟩ ⟨x, hx⟩

/-- Non-vacuity companion: the same constants, together with analyticity (hence genuine differentiability) in `lam`
of `M(x, .)` and `E(x, .)` on all of `C`, boundedness of the family over `x`, and the sup bound. -/
theorem spectral_derivative_rough_complete (j : Fin 3) (B LambdaIm : ℝ) (hB : 0 ≤ B) (hΛ : 0 ≤ LambdaIm) :
    ∃ C Lambda : ℝ, 0 ≤ C ∧ 0 < Lambda ∧
    ∀ φ : SobolevC 1, sobolevNorm 1 φ ≤ B →
    ∀ lam : ℂ, Lambda ≤ ‖lam‖ → |lam.im| ≤ LambdaIm →
      (∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
        AnalyticOnNhd ℂ (fun l : ℂ => NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ x l) Set.univ ∧
        AnalyticOnNhd ℂ (fun l : ℂ => freePropagator x l) Set.univ) ∧
      (∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
        ‖iteratedDeriv (j : ℕ) (fun l : ℂ => NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ x l) lam -
          iteratedDeriv (j : ℕ) (fun l : ℂ => freePropagator x l) lam‖ ≤
        NlsGge.ThirdConsultation.KSPSWKB.supMatrixDerivativeError j φ lam) ∧
      NlsGge.ThirdConsultation.KSPSWKB.supMatrixDerivativeError j φ lam ≤ C / ‖lam‖ := by
  obtain ⟨C, Lam, hC, hLam, h⟩ :=
    NlsGge.ThirdConsultation.KSPS018Support.spectral_derivative_rough_pointwise j B LambdaIm hB hΛ
  refine ⟨C, Lam, hC, hLam, fun φ hφ lam hlam him => ⟨fun x hx => ⟨
    NlsGge.ThirdConsultation.KSPS018Support.analyticOnNhd_fundamental φ hx.1,
    NlsGge.ThirdConsultation.KSPS018Support.analyticOnNhd_freePropagator x⟩,
    fun x hx => le_supMatrixDerivativeError j φ lam (K := C / ‖lam‖)
      (fun y hy => h φ hφ lam hlam him y hy) hx,
    ?_⟩⟩
  haveI : Nonempty (Set.Icc (0 : ℝ) 1) := ⟨⟨0, le_rfl, zero_le_one⟩⟩
  exact ciSup_le fun x => h φ hφ lam hlam him x x.2

end
end NlsGge.ThirdConsultation.KSPS
