import NlsGge.NLS38.NonlinCarrier38
import NlsGge.NLS38.PhaseGroup38
import NlsGge.Birkhoff.F01Determinant38
import NlsGge.Birkhoff.S01Equivariance38

/-! # GWP piece A4 (file a): solution notions and the interaction-picture field

Plan: `campaign/GWP_PLAN.md` §6.1 and §7 Part A, piece A4.  This file holds the definitions
`cutoff`, `IsNLSSolM`, `IsCutSolM`, the interaction-picture fields `Gc` (with cutoff) and `Gn`
(cutoff-free), their joint continuity, and the coordinate formula for the field.  The equivalence
theorems are in `SolutionNotion38` (the entry point).

Conventions (§6.0): every Sobolev index is a real cast of a natural number.  `IsNLSSolM m`,
`IsCutSolM m R` are meaningful for `1 ≤ m` only (`conv` is totalised); every theorem about the
interaction-picture field carries `hm : 1 ≤ m`.

Equation: `i u_t = -u_xx + 2|u|² u` on `ℝ/ℤ` (v2 `eq:nls`), coefficientwise
`u_n' = -i((2πn)² u_n + N(u)_n)`, `N(u) = 2((u*u)*ũ)`.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.NLS38

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open scoped ComplexConjugate NNReal

/-! ## Definitions (§6.1) -/

/-- The cutoff `χ_R(r) = max 0 (min 1 (2 - r/R))`: `1` for `r ≤ R`, `0` for `r ≥ 2R` (`R > 0`). -/
def cutoff (R r : ℝ) : ℝ := max 0 (min 1 (2 - r / R))

/-- `h^m`-valued solution of `i uₜ = -uₓₓ + 2|u|²u`, coefficientwise (`m = 1`: the basic notion).
Meaningful for `1 ≤ m` only (`conv` is totalised and junk off `ℓ¹`). -/
structure IsNLSSolM (m : ℕ) (u : ℝ → ℤ → ℂ) : Prop where
  mem   : ∀ t, u t ∈ seqSobolev38 (m : ℝ)
  cont  : Continuous fun t => carrierMk38 (m : ℝ) (u t) (mem t)
  deriv : ∀ t n, HasDerivAt (fun s => u s n)
            (-Complex.I * (((disp n : ℝ) : ℂ) * u t n + nonlin (u t) n)) t

/-- The basic notion: `h¹`-valued solutions. -/
abbrev IsNLSSol := IsNLSSolM 1

/-- Same, with the nonlinearity multiplied by `cutoff R ‖u t‖_{h¹}` (the cutoff always uses the
`h¹` norm; `hn 1` is total).  Meaningful for `1 ≤ m` only. -/
structure IsCutSolM (m : ℕ) (R : ℝ) (u : ℝ → ℤ → ℂ) : Prop where
  mem   : ∀ t, u t ∈ seqSobolev38 (m : ℝ)
  cont  : Continuous fun t => carrierMk38 (m : ℝ) (u t) (mem t)
  deriv : ∀ t n, HasDerivAt (fun s => u s n)
            (-Complex.I * (((disp n : ℝ) : ℂ) * u t n +
              ((cutoff R (hn 1 (u t)) : ℝ) : ℂ) * nonlin (u t) n)) t

abbrev IsCutSol := IsCutSolM 1

theorem cutoff_continuous (R : ℝ) : Continuous (cutoff R) := by
  unfold cutoff
  fun_prop

theorem cutoff_eq_one {R r : ℝ} (hR : 0 < R) (hr : r ≤ R) : cutoff R r = 1 := by
  unfold cutoff
  have h : 1 ≤ 2 - r / R := by
    have : r / R ≤ 1 := (div_le_one hR).2 hr
    linarith
  rw [min_eq_left h, max_eq_right zero_le_one]

/-! ## The interaction-picture field -/

/-- The inclusion `h^m → h^1` used for the cutoff argument. -/
abbrev inclOne38 (m : ℕ) (hm : 1 ≤ m) : SobolevCarrier38 (m : ℝ) →L[ℝ] SobolevCarrier38 ((1 : ℕ) : ℝ) :=
  carrierIncl38 (Nat.cast_le.2 hm)

/-- The interaction-picture field with a general radial profile `χ`:
`v ↦ e^{itΛ}(-i χ(‖v‖_{h¹}) N(e^{-itΛ} v))`, in the notation `phaseC r t = e^{-itΛ}`:
`phaseC (-t) (-J (χ ‖v‖_{h¹} • N (phaseC t v)))`. -/
def Gchi (m : ℕ) (hm : 1 ≤ m) (χ : ℝ → ℝ) (t : ℝ) :
    SobolevCarrier38 (m : ℝ) → SobolevCarrier38 (m : ℝ) :=
  fun v => phaseC (m : ℝ) (-t)
    (-(J38 (m : ℝ) (χ ‖inclOne38 m hm v‖ • nonlinC m hm (phaseC (m : ℝ) t v))))

/-- Interaction-picture vector field with cutoff, on the carrier `h^m` (`m ≥ 1`; the cutoff always
uses the `h¹` norm).  `-(J38 m (·))` is `-(J38 m) (·)` of the plan (`ContinuousLinearMap.neg_apply`). -/
def Gc (m : ℕ) (hm : 1 ≤ m) (R t : ℝ) : SobolevCarrier38 (m : ℝ) → SobolevCarrier38 (m : ℝ) :=
  fun v => phaseC (m : ℝ) (-t)
    (-(J38 (m : ℝ) (cutoff R ‖carrierIncl38 (Nat.cast_le.2 hm : ((1 : ℕ) : ℝ) ≤ (m : ℝ)) v‖ •
      nonlinC m hm (phaseC (m : ℝ) t v))))

/-- Cutoff-free interaction-picture vector field. -/
def Gn (m : ℕ) (hm : 1 ≤ m) (t : ℝ) : SobolevCarrier38 (m : ℝ) → SobolevCarrier38 (m : ℝ) :=
  fun v => phaseC (m : ℝ) (-t) (-(J38 (m : ℝ) (nonlinC m hm (phaseC (m : ℝ) t v))))

theorem Gc_eq_Gchi (m : ℕ) (hm : 1 ≤ m) (R t : ℝ) : Gc m hm R t = Gchi m hm (cutoff R) t := rfl

theorem Gn_eq_Gchi (m : ℕ) (hm : 1 ≤ m) (t : ℝ) : Gn m hm t = Gchi m hm (fun _ => 1) t := by
  funext v
  simp [Gn, Gchi]

/-- Coordinates of the interaction-picture field. -/
theorem carrierCoe38_Gchi (m : ℕ) (hm : 1 ≤ m) (χ : ℝ → ℝ) (t : ℝ) (v : SobolevCarrier38 (m : ℝ))
    (n : ℤ) :
    carrierCoe38 (m : ℝ) (Gchi m hm χ t v) n =
      Complex.exp (-(Complex.I * ((-t * disp n : ℝ) : ℂ))) *
        (-(Complex.I * ((χ ‖inclOne38 m hm v‖ : ℝ) : ℂ) *
          nonlin (phase t (carrierCoe38 (m : ℝ) v)) n)) := by
  have e : carrierCoe38 (m : ℝ) (-(J38 (m : ℝ) (χ ‖inclOne38 m hm v‖ •
      nonlinC m hm (phaseC (m : ℝ) t v)))) n =
      -(Complex.I * (((χ ‖inclOne38 m hm v‖ : ℝ) : ℂ) *
        nonlin (phase t (carrierCoe38 (m : ℝ) v)) n)) := rfl
  rw [Gchi, carrierCoe38_phaseC_apply, e]
  ring

/-- Joint continuity of the field `(t, v) ↦ G_χ(t, v)` for a continuous profile. -/
theorem continuous_Gchi_uncurry (m : ℕ) (hm : 1 ≤ m) {χ : ℝ → ℝ} (hχ : Continuous χ) :
    Continuous fun p : ℝ × SobolevCarrier38 (m : ℝ) => Gchi m hm χ p.1 p.2 := by
  have hph := continuous_phaseC (m : ℝ)
  have h1 : Continuous fun p : ℝ × SobolevCarrier38 (m : ℝ) => phaseC (m : ℝ) p.1 p.2 := hph
  have h3 : Continuous fun p : ℝ × SobolevCarrier38 (m : ℝ) =>
      χ ‖inclOne38 m hm p.2‖ • nonlinC m hm (phaseC (m : ℝ) p.1 p.2) :=
    (hχ.comp ((inclOne38 m hm).continuous.comp continuous_snd).norm).smul
      ((continuous_nonlinC m hm).comp h1)
  have h4 : Continuous fun p : ℝ × SobolevCarrier38 (m : ℝ) =>
      -(J38 (m : ℝ) (χ ‖inclOne38 m hm p.2‖ • nonlinC m hm (phaseC (m : ℝ) p.1 p.2))) :=
    ((J38 (m : ℝ)).continuous.comp h3).neg
  have hneg : Continuous fun p : ℝ × SobolevCarrier38 (m : ℝ) => -p.1 :=
    continuous_fst.neg
  have h5 := Continuous.prodMk hneg h4
  exact hph.comp h5

theorem continuous_Gc_uncurry (m : ℕ) (hm : 1 ≤ m) (R : ℝ) :
    Continuous fun p : ℝ × SobolevCarrier38 (m : ℝ) => Gc m hm R p.1 p.2 :=
  continuous_Gchi_uncurry m hm (cutoff_continuous R)

theorem continuous_Gn_uncurry (m : ℕ) (hm : 1 ≤ m) :
    Continuous fun p : ℝ × SobolevCarrier38 (m : ℝ) => Gn m hm p.1 p.2 := by
  have := continuous_Gchi_uncurry m hm (χ := fun _ => (1 : ℝ)) continuous_const
  simpa only [Gn_eq_Gchi] using this

end NlsGge.NLS38
