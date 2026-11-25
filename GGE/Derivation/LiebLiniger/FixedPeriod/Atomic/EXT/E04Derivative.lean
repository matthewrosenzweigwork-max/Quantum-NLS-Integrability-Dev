import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.BirkhoffAPI38

/-! # E04.05: compatible derivatives of the actual one-smoothing maps

Differentiate the commuting inclusion square and use uniqueness of the real
Fréchet derivative, as in `fderiv_compat38`. Higher-level compatibility follows
from the injective inclusion into `h^0` and the same underlying derivative.
-/

set_option autoImplicit false
noncomputable section

open NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.ThirdConsultation.PDE

namespace LiebLiniger.FixedPeriod.EXT

/-- E04.05 for the actual forward and inverse smoothing differences. The natural
number `r` and proof `hr : 1 ≤ r` select any positive integer Sobolev level.
`K m hm` and `J m hm` are explicitly the actual `T - Id` and `Tinv - Id` maps
from `h^m` into `h^(m+1)`, using the membership proofs of
`actualOneSmoothingInput38`; `hm` certifies `1 ≤ m`.

The first conclusion quantifies over every point `x` and real tangent vector `v`
in `h^r`: inclusion of each smoothing derivative into `h^0` equals the derivative
of the same actual map on `h^0`, evaluated at the included point and vector,
minus the included vector. The second conclusion quantifies over every natural
level `s ≥ r` (proof `hrs`) and every `x, v : h^s`: including the stronger output
derivative from `h^(s+1)` into `h^(r+1)` equals the level-`r` smoothing derivative
on the included point and vector. Both conclusions hold for both directions.
All derivatives are over `ℝ`; all inclusions are the coordinate-preserving
continuous real-linear Sobolev inclusions. No additional premise is assumed. -/
theorem actual_one_smoothing_fderiv_compat (r : ℕ) (hr : 1 ≤ r) :
    let K : (m : ℕ) → 1 ≤ m →
        SobolevCarrier38 (m : ℝ) → SobolevCarrier38 ((m + 1 : ℕ) : ℝ) :=
      fun m hm => carrierMap38 (m : ℝ) ((m + 1 : ℕ) : ℝ)
        (fun y => actualBirkhoffInput38.T y - y)
        (actualOneSmoothingInput38.smooth_T m hm)
    let J : (m : ℕ) → 1 ≤ m →
        SobolevCarrier38 (m : ℝ) → SobolevCarrier38 ((m + 1 : ℕ) : ℝ) :=
      fun m hm => carrierMap38 (m : ℝ) ((m + 1 : ℕ) : ℝ)
        (fun y => actualBirkhoffInput38.Tinv y - y)
        (actualOneSmoothingInput38.smooth_Tinv m hm)
    (∀ x v : SobolevCarrier38 (r : ℝ),
      carrierIncl38 (Nat.cast_le.2 (Nat.zero_le (r + 1))) (fderiv ℝ (K r hr) x v) =
        fderiv ℝ (actualBirkhoffInput38.TC 0)
          (carrierIncl38 (Nat.cast_le.2 (Nat.zero_le r)) x) (carrierIncl38 (Nat.cast_le.2 (Nat.zero_le r)) v) -
            carrierIncl38 (Nat.cast_le.2 (Nat.zero_le r)) v ∧
      carrierIncl38 (Nat.cast_le.2 (Nat.zero_le (r + 1))) (fderiv ℝ (J r hr) x v) =
        fderiv ℝ (actualBirkhoffInput38.TinvC 0)
          (carrierIncl38 (Nat.cast_le.2 (Nat.zero_le r)) x) (carrierIncl38 (Nat.cast_le.2 (Nat.zero_le r)) v) -
            carrierIncl38 (Nat.cast_le.2 (Nat.zero_le r)) v) ∧
    (∀ (s : ℕ) (hrs : r ≤ s) (x v : SobolevCarrier38 (s : ℝ)),
      carrierIncl38 (Nat.cast_le.2 (Nat.add_le_add_right hrs 1))
          (fderiv ℝ (K s (hr.trans hrs)) x v) =
        fderiv ℝ (K r hr) (carrierIncl38 (Nat.cast_le.2 hrs) x)
          (carrierIncl38 (Nat.cast_le.2 hrs) v) ∧
      carrierIncl38 (Nat.cast_le.2 (Nat.add_le_add_right hrs 1))
          (fderiv ℝ (J s (hr.trans hrs)) x v) =
        fderiv ℝ (J r hr) (carrierIncl38 (Nat.cast_le.2 hrs) x)
          (carrierIncl38 (Nat.cast_le.2 hrs) v)) := by
  intro K J
  have hbase (m : ℕ)
      (F : SobolevCarrier38 ((0 : ℕ) : ℝ) → SobolevCarrier38 ((0 : ℕ) : ℝ))
      (G : SobolevCarrier38 (m : ℝ) → SobolevCarrier38 ((m + 1 : ℕ) : ℝ))
      (hF : ∀ y, DifferentiableAt ℝ F y) (hG : ∀ y, DifferentiableAt ℝ G y)
      (heq : ∀ y, carrierIncl38 (Nat.cast_le.2 (Nat.zero_le (m + 1))) (G y) =
        F (carrierIncl38 (Nat.cast_le.2 (Nat.zero_le m)) y) - carrierIncl38 (Nat.cast_le.2 (Nat.zero_le m)) y)
      (x v : SobolevCarrier38 (m : ℝ)) :
      carrierIncl38 (Nat.cast_le.2 (Nat.zero_le (m + 1))) (fderiv ℝ G x v) =
        fderiv ℝ F (carrierIncl38 (Nat.cast_le.2 (Nat.zero_le m)) x)
          (carrierIncl38 (Nat.cast_le.2 (Nat.zero_le m)) v) - carrierIncl38 (Nat.cast_le.2 (Nat.zero_le m)) v := by
    let i := carrierIncl38 (Nat.cast_le.2 (Nat.zero_le m))
    let j := carrierIncl38 (Nat.cast_le.2 (Nat.zero_le (m + 1)))
    have hf : j ∘ G = fun y => F (i y) - i y := funext heq
    have h₁ : HasFDerivAt (j ∘ G) (j.comp (fderiv ℝ G x)) x :=
      j.hasFDerivAt.comp x (hG x).hasFDerivAt
    have h₂ : HasFDerivAt (fun y => F (i y) - i y)
        (((fderiv ℝ F (i x)).comp i) - i) x :=
      ((hF (i x)).hasFDerivAt.comp x i.hasFDerivAt).sub i.hasFDerivAt
    rw [hf] at h₁
    have h := congrArg (fun L => L v) (h₁.unique h₂)
    exact h
  have hb : ∀ (m : ℕ) (hm : 1 ≤ m) (x v : SobolevCarrier38 (m : ℝ)),
      carrierIncl38 (Nat.cast_le.2 (Nat.zero_le (m + 1))) (fderiv ℝ (K m hm) x v) =
        fderiv ℝ (actualBirkhoffInput38.TC 0)
          (carrierIncl38 (Nat.cast_le.2 (Nat.zero_le m)) x) (carrierIncl38 (Nat.cast_le.2 (Nat.zero_le m)) v) -
            carrierIncl38 (Nat.cast_le.2 (Nat.zero_le m)) v ∧
      carrierIncl38 (Nat.cast_le.2 (Nat.zero_le (m + 1))) (fderiv ℝ (J m hm) x v) =
        fderiv ℝ (actualBirkhoffInput38.TinvC 0)
          (carrierIncl38 (Nat.cast_le.2 (Nat.zero_le m)) x) (carrierIncl38 (Nat.cast_le.2 (Nat.zero_le m)) v) -
            carrierIncl38 (Nat.cast_le.2 (Nat.zero_le m)) v := by
    intro m hm x v
    constructor
    · apply hbase m (actualBirkhoffInput38.TC 0) (K m hm)
        (fun y => (actualBirkhoffInput38.analyticOnNhd_TC 0 y (Set.mem_univ y)).differentiableAt)
        (fun y => (actualOneSmoothingInput38.analytic_smooth_T m hm y
          (Set.mem_univ y)).differentiableAt) _ x v
      intro y
      apply carrierExt38
      rw [carrierCoe38_incl38]
      change actualBirkhoffInput38.T (carrierCoe38 (m : ℝ) y) - carrierCoe38 (m : ℝ) y =
        actualBirkhoffInput38.T (carrierCoe38 ((0 : ℕ) : ℝ) (carrierIncl38 (Nat.cast_le.2 (Nat.zero_le m)) y)) -
          carrierCoe38 ((0 : ℕ) : ℝ) (carrierIncl38 (Nat.cast_le.2 (Nat.zero_le m)) y)
      rw [carrierCoe38_incl38]
    · apply hbase m (actualBirkhoffInput38.TinvC 0) (J m hm)
        (fun y => (actualBirkhoffInput38.analyticOnNhd_TinvC 0 y (Set.mem_univ y)).differentiableAt)
        (fun y => (actualOneSmoothingInput38.analytic_smooth_Tinv m hm y
          (Set.mem_univ y)).differentiableAt) _ x v
      intro y
      apply carrierExt38
      rw [carrierCoe38_incl38]
      change actualBirkhoffInput38.Tinv (carrierCoe38 (m : ℝ) y) - carrierCoe38 (m : ℝ) y =
        actualBirkhoffInput38.Tinv (carrierCoe38 ((0 : ℕ) : ℝ) (carrierIncl38 (Nat.cast_le.2 (Nat.zero_le m)) y)) -
          carrierCoe38 ((0 : ℕ) : ℝ) (carrierIncl38 (Nat.cast_le.2 (Nat.zero_le m)) y)
      rw [carrierCoe38_incl38]
  refine ⟨hb r hr, ?_⟩
  intro s hrs x v
  have hx : carrierIncl38 (Nat.cast_le.2 (Nat.zero_le r)) (carrierIncl38 (Nat.cast_le.2 hrs) x) =
      carrierIncl38 (Nat.cast_le.2 (Nat.zero_le s)) x := by
    apply carrierExt38
    simp only [carrierCoe38_incl38]
  have hv : carrierIncl38 (Nat.cast_le.2 (Nat.zero_le r)) (carrierIncl38 (Nat.cast_le.2 hrs) v) =
      carrierIncl38 (Nat.cast_le.2 (Nat.zero_le s)) v := by
    apply carrierExt38
    simp only [carrierCoe38_incl38]
  have hl := hb r hr (carrierIncl38 (Nat.cast_le.2 hrs) x)
    (carrierIncl38 (Nat.cast_le.2 hrs) v)
  rw [hx, hv] at hl
  have hh := hb s (hr.trans hrs) x v
  constructor
  · apply carrierExt38
    have h := congrArg (carrierCoe38 ((0 : ℕ) : ℝ)) (hh.1.trans hl.1.symm)
    simpa only [carrierCoe38_incl38] using h
  · apply carrierExt38
    have h := congrArg (carrierCoe38 ((0 : ℕ) : ℝ)) (hh.2.trans hl.2.symm)
    simpa only [carrierCoe38_incl38] using h

end LiebLiniger.FixedPeriod.EXT
