import LiebLiniger.FixedPeriod.Atomic.ALLS.TransA5Gen
import LiebLiniger.FixedPeriod.Atomic.ALLS.TransA2Translate

/-! # Track A, step A6: every integer base gives every real exponent `s ≥ 0`

Author: Claude Opus 5.5 (track A).  Not self-reviewed, not accepted.  Helper lemmas only: the
final approved-statement theorems (A-SEQ, A-PHYS, A-MEM, A-COMPAT) are NOT stated here.

* `restriction_all_real`: a sequence map preserving every integer level `h^N`, real analytic on
  each, and commuting with every rotation on `h⁰`, preserves `h^s` and is real analytic on it for
  every real `s ≥ 0` (integer `s`: the hypothesis itself; `s = N + σ`, `0 < σ < 1`: A-GEN over the
  base `N = ⌊s⌋`);
* `actualT_realExponent`, `actualTinv_realExponent`: the same for the actual maps
  `actualBirkhoffTop38.T = actualT38` and `actualBirkhoffTop38.Tinv = actualTinv38`, using the
  existing integer-level providers `actualT38_analytic`/`actualTinv38_analytic` (G6027 and level
  zero) and the S01 rotation equivariance. -/

set_option autoImplicit false
noncomputable section

open Set NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.ThirdConsultation.PDE

namespace NlsGge.ALLS.TransA

/-- Every real `s ≥ 0` is `N + σ` with `N : ℕ` and `0 ≤ σ < 1`. -/
theorem exists_nat_add_frac (s : ℝ) (hs : 0 ≤ s) :
    ∃ (N : ℕ) (σ : ℝ), 0 ≤ σ ∧ σ < 1 ∧ s = (N : ℝ) + σ :=
  ⟨⌊s⌋₊, s - ⌊s⌋₊, sub_nonneg.2 (Nat.floor_le hs), by
    have := Nat.lt_floor_add_one s; linarith, by ring⟩

/-- **A6 (generic)**: integer-level analytic, rotation-equivariant maps restrict analytically to
every real level. -/
theorem restriction_all_real (f : (ℤ → ℂ) → (ℤ → ℂ))
    (hfN : ∀ N : ℕ, ∀ x ∈ seqSobolev38 (N : ℝ), f x ∈ seqSobolev38 (N : ℝ))
    (hanN : ∀ N : ℕ, AnalyticOnNhd ℝ (carrierMap38 (N : ℝ) (N : ℝ) f (hfN N)) Set.univ)
    (heq : ∀ θ : ℝ, ∀ x ∈ seqSobolev38 0, f (rotSeq38 θ x) = rotSeq38 θ (f x))
    (s : ℝ) (hs : 0 ≤ s) :
    ∃ hfs : (∀ x ∈ seqSobolev38 s, f x ∈ seqSobolev38 s),
      AnalyticOnNhd ℝ (carrierMap38 s s f hfs) Set.univ := by
  obtain ⟨N, σ, hσ0, hσ1, rfl⟩ := exists_nat_add_frac s hs
  rcases hσ0.eq_or_lt with h0 | hpos
  · subst h0
    rw [add_zero]
    exact ⟨hfN N, hanN N⟩
  · exact analytic_restriction_of_rot_equivariant N σ hpos hσ1 f (hfN N) (hanN N)
      (fun θ x hx => heq θ x (seqSobolev38_natCast_mono hx))

/-- **A6, actual forward map**: `T` preserves `h^s` and is real analytic there, every real `s ≥ 0`. -/
theorem actualT_realExponent (s : ℝ) (hs : 0 ≤ s) :
    ∃ hT : (∀ x ∈ seqSobolev38 s, actualBirkhoffTop38.T x ∈ seqSobolev38 s),
      AnalyticOnNhd ℝ (carrierMap38 s s actualBirkhoffTop38.T hT) Set.univ :=
  restriction_all_real actualBirkhoffTop38.T actualT38_mapsTo actualT38_analytic
    (fun θ x hx => actualT_rotSeq x hx θ) s hs

/-- **A6, actual inverse map**: `Tinv` preserves `h^s` and is real analytic there, every real
`s ≥ 0`. -/
theorem actualTinv_realExponent (s : ℝ) (hs : 0 ≤ s) :
    ∃ hTinv : (∀ z ∈ seqSobolev38 s, actualBirkhoffTop38.Tinv z ∈ seqSobolev38 s),
      AnalyticOnNhd ℝ (carrierMap38 s s actualBirkhoffTop38.Tinv hTinv) Set.univ :=
  restriction_all_real actualBirkhoffTop38.Tinv actualTinv38_mapsTo actualTinv38_analytic
    (fun θ z hz => actualTinv_rotSeq z hz θ) s hs

end NlsGge.ALLS.TransA
