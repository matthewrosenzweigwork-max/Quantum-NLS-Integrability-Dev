/-
Prop-valued provider contract for LLFP-EXT-BIRKHOFF (support-only, not rooted, no node credit, no ledger
credit).  Nothing here proves or discharges the provider node: it stays OPEN, and downstream results that
take `LLFPExtBirkhoffContract` as a hypothesis are CONDITIONAL.  Nothing about the Birkhoff map itself is
proved in this file.

Frozen source: `handoff/llfp/source/lieb_liniger_fixed_period_consolidated_20261012T215332Z.tex`
(SHA-256 25a48388...fd561); atomic record `LLFP-EXT-BIRKHOFF` (source lines 214-219, reflection 99-103).
Literature cited by the source (l.219): Grebert-Kappeler-Poschel (GKP, arXiv:0907.3938), Grebert-Kappeler
(GK, EMS 2014), Molnar (arXiv:1403.1369); integer Sobolev levels: Kappeler-Schaad-Topalov (arXiv:1505.04455,
Thm 2.1 (B1), (B2), (B4)).  See `BirkhoffContract.NOTES.md` for the per-field provenance and for what is
NOT claimed.

DESIGN.
* Unit period only.  The source (l.412) and `LLFP-F0-006` derive the period-`L` map
  `Phi_L(u) = L^(-1/2) Phi_1(L u(L .))` from the unit-period one; this file therefore states the
  contract at period one over the very carriers the repo already uses at period one
  (`NlsGge.Pilot.PhysicalL2 = Lp C 2 spatialMeasure`, `spatialMeasure` = normalized Haar measure of
  `AddCircle 1`, and the complex `lp (fun _ : Z => C) 2`).
* `Phi` is a PARAMETER (like `Hop` in `LLFPExtBetheOpenContract`), given as an equivalence
  `PhysicalL2 ≃ lp`: bijectivity is data, its inverse is `Phi.symm`.  The contract does NOT identify
  `Phi`: composing a valid `Phi` with `z_0 ↦ exp(i c |z_0|^2) z_0` gives another map with every field
  below (CONSULT-0016, section 7), so "the" Birkhoff map is a pinned construction, not a property list.
  Every consumer theorem must therefore hold for EVERY `Phi` satisfying the contract and must use ONE
  `Phi` in all its spectral, torus and Gibbs statements (source: "same map").
* The fields are those of the atomic record and of source l.214-219.  Neither BK3b nor BK6 is an extra:
  BK3b (`{z_j, z_k} = 0`) completes the word "canonical" (l.214, l.245: the flow of `I_n` rotates `z_n` and
  fixes every other coordinate, which needs `{z_j, z_n} = 0`; GKP Thm 18.8), and BK6 (`|Phi(u)_n|² = I_n(u)`)
  is the termwise reading of the source's use of the same map (l.99-103, l.245, l.1088, l.1146-1160), of
  which l.216-217 display only the sums.  No Molnar polynomial bound, no one-smoothing (E04), no
  translation equivariance (none of them occurs in the source's statement of the inputs).
* The Sobolev part BK5 is a separate third field `sobolev` of `LLFPExtBirkhoffContract` (not a part of
  `LLFPBirkhoffCanonicalMap`), so that "the contract without BK5" is a type: `LLFPBirkhoffCanonicalMap`
  is BK1-BK4, and a consumer that does not touch BK5 can say so in its hypotheses.

STATUS OF THE FIELDS.  See `BirkhoffContract.NOTES.md`: BK1-BK4, BK6 are in the book form of GKP (L^2
level); BK5 (integer Sobolev levels) is KST (B2) only and is NOT proved in the GK book.
-/
import LiebLiniger.FixedPeriod.Quantum.Q4001FirstContractionReal
import NlsGge.Birkhoff.BirkhoffInput38

set_option autoImplicit false
noncomputable section
namespace LiebLiniger.FixedPeriod.Conditional

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.SpectralFoundations
open LiebLiniger.FixedPeriod.Quantum
open scoped ENNReal

/-- The complex Hilbert space `ell^2(Z; C)` of Birkhoff coordinates `z = (z_n)_{n in Z}` (source l.215-217). -/
abbrev LLFPBirkhoffCoordinates : Type := lp (fun _ : ℤ => ℂ) 2

open Classical in
/-- The Birkhoff map seen on sequences, `T = Phi ∘ F⁻¹` with `F = reflectedFourierL2` the minus-reflected
orthonormal Fourier isometry `(F u)_n = -hat u(-n)`.  Values off `ell^2` are junk (`0`) and are never used:
every field below only evaluates `T` on `ell^2` sequences.  This is the sequence-side convention of
`NlsGge.Birkhoff.BirkhoffTop38.T` (`T = Phi ∘ F⁻¹`), restated for a map `Phi` that is honestly typed. -/
def LLFPBirkhoffSeq (Φ : PhysicalL2 ≃ LLFPBirkhoffCoordinates) : (ℤ → ℂ) → (ℤ → ℂ) :=
  fun x => if h : Memℓp x 2 then ((Φ (reflectedFourierL2.symm ⟨x, h⟩) : LLFPBirkhoffCoordinates) : ℤ → ℂ)
    else 0

open Classical in
/-- The inverse `T⁻¹ = F ∘ Phi⁻¹` on sequences (same junk convention). -/
def LLFPBirkhoffSeqInv (Φ : PhysicalL2 ≃ LLFPBirkhoffCoordinates) : (ℤ → ℂ) → (ℤ → ℂ) :=
  fun z => if h : Memℓp z 2 then ((reflectedFourierL2 (Φ.symm ⟨z, h⟩) : LLFPBirkhoffCoordinates) : ℤ → ℂ)
    else 0

/-- **BK5, integer Sobolev restrictions** (source l.219 "its Sobolev restrictions"; l.128 "by the corresponding
Birkhoff regularity"; consumer statement of `LLFP-EXT-BIRKHOFF`: "compatible Sobolev restrictions and inverse
restrictions ... integer Sobolev restrictions suffice").  The physical Sobolev space `H^m` is identified with
`h^m = seqSobolev38 m` (weight `<n>^(2m)`) through the reflected Fourier isometry, as in
`NlsGge.Birkhoff.BirkhoffInput38`.  For every integer `m >= 1` (the case `m = 0` is `analytic`/`analytic_symm`
of the contract): `T = Phi ∘ F⁻¹` and `T⁻¹ = F ∘ Phi⁻¹` map `h^m` into itself, and the restrictions are real
analytic on the Hilbert carriers `SobolevCarrier38 m`.  Compatibility of the restrictions with each other and
with `Phi` is automatic: they are restrictions of the single map `Phi`. -/
structure LLFPBirkhoffSobolev (Φ : PhysicalL2 ≃ LLFPBirkhoffCoordinates) : Prop where
  mapsTo : ∀ m : ℕ, 1 ≤ m → ∀ x ∈ seqSobolev38 (m : ℝ), LLFPBirkhoffSeq Φ x ∈ seqSobolev38 (m : ℝ)
  mapsTo_inv : ∀ m : ℕ, 1 ≤ m → ∀ z ∈ seqSobolev38 (m : ℝ),
    LLFPBirkhoffSeqInv Φ z ∈ seqSobolev38 (m : ℝ)
  analytic : ∀ (m : ℕ) (hm : 1 ≤ m),
    AnalyticOnNhd ℝ (carrierMap38 (m : ℝ) (m : ℝ) (LLFPBirkhoffSeq Φ) (mapsTo m hm)) Set.univ
  analytic_inv : ∀ (m : ℕ) (hm : 1 ≤ m),
    AnalyticOnNhd ℝ (carrierMap38 (m : ℝ) (m : ℝ) (LLFPBirkhoffSeqInv Φ) (mapsTo_inv m hm)) Set.univ

/-- **The canonical-map part of EXT-BIRKHOFF (BK1-BK4)**: everything the source states about the Birkhoff
map `Phi_1` at the `L^2` level that does not mention the spectral actions or the Sobolev levels.  Split off
from the action link (BK6) and the Sobolev restrictions (BK5) so that its consistency can be tested on the
linearization `F` (see `BirkhoffContractNonVacuity.lean`); consumers should assume `LLFPExtBirkhoffContract`,
not this structure.

* `analytic`, `analytic_symm` (BK1; source l.215 "global real-analytic ... on `L^2`, its inverse"): `Phi` and
  `Phi⁻¹` are real-analytic on all of `L^2(T)` resp. `ell^2` (the real Banach structure of the complex
  Hilbert spaces; this is the real-form analyticity of GKP, not a statement about independent complex pairs).
  Bijectivity is the data `Phi : PhysicalL2 ≃ lp`.
* `mass` (BK2; l.216-217 `‖u‖² = Σ|Phi(u)_n|²`): `‖Phi u‖_{ell^2} = ‖u‖_{L^2}`, the `ell^2` norm being
  `(Σ|z_n|²)^(1/2)` (`lp.hasSum_norm`, see `LLFPExtBirkhoffContract.hasSum_sq`).  At period one the repo's
  `L^2` norm is the Lebesgue one on `[0,1)` (`periodOne_volume_eq_haar`).
* `bracket_conj` (BK3a; l.219 `{z_j, conj z_k} = -i δ_jk`), `bracket_zz` (BK3b, the companion `{z_j, z_k} = 0`
  of the word "canonical" in l.214/l.215; GKP Thm 18.8, book Thm 18.8: `{x_m,y_n}=δ` with all other
  coordinate brackets zero; needed by `F0-015` where the flow of `|z_n|²` is computed): the coordinate
  functions `u ↦ Phi(u)_j` have the stated brackets at EVERY point `u`, for the repo's physical canonical
  bracket `q4001CanonicalRealPoisson` (one-mode check: `{z, conj z} = -i`, docstring of that definition).
  Because `fderiv` is totalized, the brackets are only meaningful with differentiable coordinates; that is
  `analytic`.
* `fderiv_zero` (BK4; l.103 "the retained linearization `z_n = -hat u(-n) + nonlinear terms`"; consumer statement
  "derivative at zero equal to the reflected negative orthonormal Fourier transform"): `D Phi(0) = F`.
  (`Phi(0) = 0` follows from `mass`.)  This is a normalization and fixes only the global phase pattern at
  `0`, never the nonlinear phases. -/
structure LLFPBirkhoffCanonicalMap (Φ : PhysicalL2 ≃ LLFPBirkhoffCoordinates) : Prop where
  analytic : AnalyticOnNhd ℝ (⇑Φ) Set.univ
  analytic_symm : AnalyticOnNhd ℝ (⇑Φ.symm) Set.univ
  mass : ∀ u : PhysicalL2, ‖Φ u‖ = ‖u‖
  bracket_conj : ∀ (u : PhysicalL2) (j k : ℤ),
    q4001CanonicalRealPoisson spatialMeasure (fun v : PhysicalL2 => (Φ v : ℤ → ℂ) j)
        (fun v : PhysicalL2 => starRingEnd ℂ ((Φ v : ℤ → ℂ) k)) u =
      if j = k then -Complex.I else 0
  bracket_zz : ∀ (u : PhysicalL2) (j k : ℤ),
    q4001CanonicalRealPoisson spatialMeasure (fun v : PhysicalL2 => (Φ v : ℤ → ℂ) j)
        (fun v : PhysicalL2 => (Φ v : ℤ → ℂ) k) u = 0
  fderiv_zero : ∀ h : PhysicalL2, fderiv ℝ (⇑Φ) 0 h = reflectedFourierL2 h

/-- **LLFP-EXT-BIRKHOFF, the OPEN contract** (unit period; atomic record `LLFP-EXT-BIRKHOFF`, source lines
214-219): the only provider hypothesis for downstream Birkhoff nodes.  `toCanonicalMap` is BK1-BK4,
`sobolev` is BK5 (KST (B2) only; touched by Q3-009 and S2-001), `action` is BK6.

`action` (BK6, "the SAME map", source l.99-103, l.216-217, l.1146-1160 and the record's "The same map must be
used in all spectral actions, tori, and the classical Gibbs input"): for every `u in L^2` and every `n`,
`|Phi(u)_n|² = I_n(u)` with `I_n = actualGapActionAllE02_38`, the repo's actual labelled gap action
`(2/pi) ∫_{g_n} v` of the Zakharov-Shabat operator `L_u` (equal to the `1/pi` contour integral of
`LLFP_EXT_CONTOUR`, `unitPeriod_action_contour`).  There is NO index reflection here (CONSULT-0016, section 3):
the reflection `|z_{-m}|² = E_m` of l.101-103 is the relabelling `E_m = I_{-m}` used later by consumers.
The source l.217 literally records only the equality of the two SUMS; the termwise identity is what l.1146-1160
use (`z_n(s) = sqrt(I_n^E + s ℓ_n) e^{iθ_n}` has `I_n` equal to the squared modulus) and is the content of
"same map"; the sum identity `Σ I_n = ‖u‖²` for all `L^2` fields follows from `action` and `mass` (the repo
proves it only for `H^1`: `actualGapAction_hasSum_E02_38`). -/
structure LLFPExtBirkhoffContract (Φ : PhysicalL2 ≃ LLFPBirkhoffCoordinates) : Prop where
  toCanonicalMap : LLFPBirkhoffCanonicalMap Φ
  sobolev : LLFPBirkhoffSobolev Φ
  action : ∀ (u : PhysicalL2) (n : ℤ), ‖(Φ u : ℤ → ℂ) n‖ ^ 2 = actualGapActionAllE02_38 u n

namespace LLFPExtBirkhoffContract

variable {Φ : PhysicalL2 ≃ LLFPBirkhoffCoordinates}

/-- `Σ_n |Phi(u)_n|² = ‖u‖²` as a `HasSum` (source l.217, right equality). -/
theorem hasSum_sq (h : LLFPExtBirkhoffContract Φ) (u : PhysicalL2) :
    HasSum (fun n : ℤ => ‖(Φ u : ℤ → ℂ) n‖ ^ 2) (‖u‖ ^ 2) := by
  have h2 := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (Φ u)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h2
  rwa [h.toCanonicalMap.mass u] at h2

/-- `Σ_n I_n(u) = ‖u‖²` for every `u in L^2` (source l.217, both equalities), from `action` and `mass`. -/
theorem hasSum_action (h : LLFPExtBirkhoffContract Φ) (u : PhysicalL2) :
    HasSum (fun n : ℤ => actualGapActionAllE02_38 u n) (‖u‖ ^ 2) := by
  simpa only [h.action u] using h.hasSum_sq u

/-- `Phi(0) = 0` (from `mass`). -/
theorem apply_zero (h : LLFPExtBirkhoffContract Φ) : Φ 0 = 0 := by
  have := h.toCanonicalMap.mass 0
  rw [norm_zero] at this
  exact norm_eq_zero.mp this

end LLFPExtBirkhoffContract

end LiebLiniger.FixedPeriod.Conditional
