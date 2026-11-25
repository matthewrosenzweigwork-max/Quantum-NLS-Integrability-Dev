import NlsGge.Sobolev38.SobolevCarrier38
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38
import NlsGge.Sobolev.PeriodicBridge

/-! # Birkhoff conditional layer: input structures (user decision D1, 2026-10-12)

Design: `campaign/BIRKHOFF_LAYER_DESIGN.md`.

This file contains ONLY definitions of the conditional inputs and trivial projections.
It proves nothing about E01/E04 or any dependent claim. E01 and E04 remain OPEN.
A theorem taking `B : BirkhoffInput38` / `O : OneSmoothingInput38 B` as hypotheses is
at most `conditional_proved`.

Conventions (v2 l.104-118, l.177-184):
* `T = Φ ∘ 𝓕⁻¹` on sequences, where `𝓕 = reflectedFourierL2` is the actual minus-reflected
  Fourier isometry `(𝓕 u)_n = -û(-n)` (KST normal-form convention, `d₀Φ = 𝓕`).
* `h^r` is `seqSobolev38 r = weightedSubmodule (sobolevModeWeight r)`, weight `⟨n⟩^{2r}`;
  its coherent real Hilbert carrier is `SobolevCarrier38 r`.
* All fields constrain `T`, `Tinv` only on `h⁰` (or `h^m ⊆ h⁰`); values off `h⁰` are junk and
  are never used.
* The action field uses the project's actual Zakharov–Shabat gap action
  `actualGapActionAllE02_38` (v2 A:eq:trace), restricted to physical `H¹`.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Birkhoff

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.SpectralFoundations

/-- The sequence Sobolev space `h^r` as a set of complex sequences (weight `⟨n⟩^{2r}`). -/
def seqSobolev38 (r : ℝ) : Set (ℤ → ℂ) := {x | x ∈ weightedSubmodule (sobolevModeWeight r)}

/-- Underlying sequence of a carrier element. -/
def carrierCoe38 (r : ℝ) (x : SobolevCarrier38 r) : ℤ → ℂ :=
  ((show weightedSubmodule (sobolevModeWeight r) from x) : ℤ → ℂ)

theorem carrierCoe38_mem (r : ℝ) (x : SobolevCarrier38 r) : carrierCoe38 r x ∈ seqSobolev38 r :=
  (show weightedSubmodule (sobolevModeWeight r) from x).2

/-- A sequence in `h^r`, viewed in the real Hilbert carrier. -/
def carrierMk38 (r : ℝ) (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 r) : SobolevCarrier38 r :=
  (show SobolevCarrier38 r from (⟨x, hx⟩ : weightedSubmodule (sobolevModeWeight r)))

@[simp] theorem carrierCoe38_mk (r : ℝ) (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 r) :
    carrierCoe38 r (carrierMk38 r x hx) = x := rfl

/-- The map `h^r → h^{r'}` induced by a sequence map that sends `h^r` into `h^{r'}`. -/
def carrierMap38 (r r' : ℝ) (f : (ℤ → ℂ) → (ℤ → ℂ)) (hf : ∀ x ∈ seqSobolev38 r, f x ∈ seqSobolev38 r') :
    SobolevCarrier38 r → SobolevCarrier38 r' :=
  fun x => carrierMk38 r' (f (carrierCoe38 r x)) (hf _ (carrierCoe38_mem r x))

@[simp] theorem carrierMap38_coe (r r' : ℝ) (f : (ℤ → ℂ) → (ℤ → ℂ))
    (hf : ∀ x ∈ seqSobolev38 r, f x ∈ seqSobolev38 r') (x : SobolevCarrier38 r) :
    carrierCoe38 r' (carrierMap38 r r' f hf x) = f (carrierCoe38 r x) := rfl

/-- The actual linearized Birkhoff map `𝓕 u = (-û(-n))_n`, as a sequence. -/
def fourierSeq38 (u : PhysicalL2) : ℤ → ℂ := (reflectedFourierL2 u : ℤ → ℂ)

/-- Standard constant symplectic form on `h⁰`, `ω(ξ,η) = Σ Im(conj ξ_n · η_n)`.
(Absolutely summable for `ξ, η ∈ h⁰`; used only on such arguments.) -/
def stdSymplectic38 (ξ η : ℤ → ℂ) : ℝ := ∑' n : ℤ, (starRingEnd ℂ (ξ n) * η n).im

/-- **Topological part of the E01 input** (interface split E01-D5, `campaign/E01_PLAN.md` §5.2).
`T = Φ ∘ 𝓕⁻¹` is a bijection of the Sobolev scale `h^m`, `m ∈ ℕ`, continuous on each carrier,
with actual Zakharov–Shabat gap actions on ALL of `L²` (`action_L2`). No analyticity, no
canonicity, no Molnár bound: those are separate structures below. -/
structure BirkhoffTop38 where
  /-- `T = Φ ∘ 𝓕⁻¹` (meaningful on `h⁰`). -/
  T : (ℤ → ℂ) → (ℤ → ℂ)
  /-- `T⁻¹ = 𝓕 ∘ Φ⁻¹` (meaningful on `h⁰`). -/
  Tinv : (ℤ → ℂ) → (ℤ → ℂ)
  mapsTo_T : ∀ m : ℕ, ∀ x ∈ seqSobolev38 (m : ℝ), T x ∈ seqSobolev38 (m : ℝ)
  mapsTo_Tinv : ∀ m : ℕ, ∀ z ∈ seqSobolev38 (m : ℝ), Tinv z ∈ seqSobolev38 (m : ℝ)
  left_inv : ∀ x ∈ seqSobolev38 0, Tinv (T x) = x
  right_inv : ∀ z ∈ seqSobolev38 0, T (Tinv z) = z
  /-- Continuity of `T` on every integer Sobolev space `h^m`, `m ≥ 0`. -/
  continuous_T : ∀ m : ℕ, Continuous (carrierMap38 (m : ℝ) (m : ℝ) T (mapsTo_T m))
  /-- Continuity of `T⁻¹` on every integer Sobolev space `h^m`, `m ≥ 0`. -/
  continuous_Tinv : ∀ m : ℕ, Continuous (carrierMap38 (m : ℝ) (m : ℝ) Tinv (mapsTo_Tinv m))
  /-- `|Φ_n(u)|² = I_n(u)` (v2 A:eq:action) with the actual gap action, for ALL `u ∈ L²`
  (the former interface asked this only for physical `H¹`). -/
  action_L2 : ∀ (u : PhysicalL2) (n : ℤ),
    ‖T (fourierSeq38 u) n‖ ^ 2 = actualGapActionAllE02_38 u n

namespace BirkhoffTop38

variable (B : BirkhoffTop38)

/-- The Birkhoff map on physical fields, `Φ = T ∘ 𝓕`. -/
def Φ (u : PhysicalL2) : ℤ → ℂ := B.T (fourierSeq38 u)

theorem Φ_def (u : PhysicalL2) : B.Φ u = B.T (fourierSeq38 u) := rfl

/-- `T` as a map of the real Hilbert carrier `h^m`. -/
def TC (m : ℕ) : SobolevCarrier38 (m : ℝ) → SobolevCarrier38 (m : ℝ) :=
  carrierMap38 (m : ℝ) (m : ℝ) B.T (B.mapsTo_T m)

/-- `T⁻¹` as a map of the real Hilbert carrier `h^m`. -/
def TinvC (m : ℕ) : SobolevCarrier38 (m : ℝ) → SobolevCarrier38 (m : ℝ) :=
  carrierMap38 (m : ℝ) (m : ℝ) B.Tinv (B.mapsTo_Tinv m)

theorem TC_coe (m : ℕ) (x : SobolevCarrier38 (m : ℝ)) :
    carrierCoe38 (m : ℝ) (B.TC m x) = B.T (carrierCoe38 (m : ℝ) x) := rfl

theorem TinvC_coe (m : ℕ) (z : SobolevCarrier38 (m : ℝ)) :
    carrierCoe38 (m : ℝ) (B.TinvC m z) = B.Tinv (carrierCoe38 (m : ℝ) z) := rfl

theorem continuous_TC (m : ℕ) : Continuous (B.TC m) := B.continuous_T m

theorem continuous_TinvC (m : ℕ) : Continuous (B.TinvC m) := B.continuous_Tinv m

/-- The old interface (action stated for physical `H¹`, with `T (fourierSeq38 u)` unfolded, so
that existing `rw [← B.action ..]` consumers are unchanged), now a consequence of `action_L2`. -/
theorem action (u : PhysicalL2) (_hu : SobolevSquareSummable 1 (physicalFourier u)) (n : ℤ) :
    ‖B.T (fourierSeq38 u) n‖ ^ 2 = actualGapActionAllE02_38 u n := B.action_L2 u n

theorem sq_norm_Φ_eq_action (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u))
    (n : ℤ) : ‖B.Φ u n‖ ^ 2 = actualGapActionAllE02_38 u n := B.action u hu n

theorem sq_norm_Φ_eq_action_L2 (u : PhysicalL2) (n : ℤ) :
    ‖B.Φ u n‖ ^ 2 = actualGapActionAllE02_38 u n := B.action_L2 u n

end BirkhoffTop38

/-- Real analyticity of `T` and `T⁻¹` on the integer Sobolev levels `m ∈ M` (the B-only
consumers need `M = {0,1}`; the E01 claim-level closure needs `M = univ`). -/
structure BirkhoffAnalytic38 (B : BirkhoffTop38) (M : Set ℕ) : Prop where
  analytic_T : ∀ m ∈ M,
    AnalyticOnNhd ℝ (carrierMap38 (m : ℝ) (m : ℝ) B.T (B.mapsTo_T m)) Set.univ
  analytic_Tinv : ∀ m ∈ M,
    AnalyticOnNhd ℝ (carrierMap38 (m : ℝ) (m : ℝ) B.Tinv (B.mapsTo_Tinv m)) Set.univ

/-- Canonicity of `T` on `h⁰` and the normalization `d₀T = Id` (`d₀Φ = 𝓕`, KST (B4)). -/
structure BirkhoffCanonical38 (B : BirkhoffTop38) : Prop where
  /-- Canonicity on `h⁰`: `DT(x)` preserves the standard symplectic form. -/
  canonical : ∀ x ξ η : SobolevCarrier38 ((0 : ℕ) : ℝ),
    stdSymplectic38 (carrierCoe38 _ (fderiv ℝ (B.TC 0) x ξ))
        (carrierCoe38 _ (fderiv ℝ (B.TC 0) x η)) =
      stdSymplectic38 (carrierCoe38 _ ξ) (carrierCoe38 _ η)
  /-- `d₀T = Id`, i.e. `d₀Φ = 𝓕` (KST (B4)); needed for E04.01. -/
  fderiv_zero : fderiv ℝ (B.TC 0) 0 = ContinuousLinearMap.id ℝ _

/-- Polynomial inverse Sobolev bound (Molnár Thm 1(ii), one-variable weakening). -/
structure BirkhoffMolnar38 (B : BirkhoffTop38) : Prop where
  inverse_polynomial : ∀ m : ℕ, 1 ≤ m → ∃ (C : ℝ) (d : ℕ), ∀ z : SobolevCarrier38 (m : ℝ),
    ‖B.TinvC m z‖ ≤ C * (1 + ‖z‖) ^ d

/-- **E01 input** (Grébert–Kappeler; KST arXiv:1505.04455 Thm 2.1 (B1),(B2),(B4);
Molnár IMRN 2015 Thm 1(ii)). Stated for `T = Φ ∘ 𝓕⁻¹` over the actual objects.
The full input: `BirkhoffTop38` plus analyticity at every level, canonicity, `d₀T = Id`
and the Molnár bound (all field names of the pre-split structure are unchanged, except that
`action` is now the projection theorem `BirkhoffTop38.action` from `action_L2`). -/
structure BirkhoffInput38 extends BirkhoffTop38 where
  /-- Real analyticity of `T` on every integer Sobolev space `h^m`, `m ≥ 0`. -/
  analytic_T : ∀ m : ℕ,
    AnalyticOnNhd ℝ (carrierMap38 (m : ℝ) (m : ℝ) T (mapsTo_T m)) Set.univ
  /-- Real analyticity of `T⁻¹` on every integer Sobolev space `h^m`, `m ≥ 0`. -/
  analytic_Tinv : ∀ m : ℕ,
    AnalyticOnNhd ℝ (carrierMap38 (m : ℝ) (m : ℝ) Tinv (mapsTo_Tinv m)) Set.univ
  /-- Canonicity on `h⁰`: `DT(x)` preserves the standard symplectic form. -/
  canonical : ∀ x ξ η : SobolevCarrier38 ((0 : ℕ) : ℝ),
    stdSymplectic38
        (carrierCoe38 _ (fderiv ℝ (carrierMap38 _ _ T (mapsTo_T 0)) x ξ))
        (carrierCoe38 _ (fderiv ℝ (carrierMap38 _ _ T (mapsTo_T 0)) x η)) =
      stdSymplectic38 (carrierCoe38 _ ξ) (carrierCoe38 _ η)
  /-- `d₀T = Id`, i.e. `d₀Φ = 𝓕` (KST (B4)). -/
  fderiv_zero : fderiv ℝ (carrierMap38 _ _ T (mapsTo_T 0) :
      SobolevCarrier38 ((0 : ℕ) : ℝ) → SobolevCarrier38 ((0 : ℕ) : ℝ)) 0 =
    ContinuousLinearMap.id ℝ _
  /-- Polynomial inverse Sobolev bound (Molnár Thm 1(ii), one-variable weakening). -/
  inverse_polynomial : ∀ m : ℕ, 1 ≤ m → ∃ (C : ℝ) (d : ℕ), ∀ z : SobolevCarrier38 (m : ℝ),
    ‖carrierMap38 (m : ℝ) (m : ℝ) Tinv (mapsTo_Tinv m) z‖ ≤ C * (1 + ‖z‖) ^ d

namespace BirkhoffInput38

variable (B : BirkhoffInput38)

theorem analyticOnNhd_TC (m : ℕ) : AnalyticOnNhd ℝ (B.TC m) Set.univ := B.analytic_T m

theorem analyticOnNhd_TinvC (m : ℕ) : AnalyticOnNhd ℝ (B.TinvC m) Set.univ := B.analytic_Tinv m

/-- The analytic part of the full input, at every level. -/
theorem toAnalytic : BirkhoffAnalytic38 B.toBirkhoffTop38 Set.univ :=
  ⟨fun m _ => B.analytic_T m, fun m _ => B.analytic_Tinv m⟩

/-- The canonical part of the full input. -/
theorem toCanonical : BirkhoffCanonical38 B.toBirkhoffTop38 :=
  ⟨B.canonical, B.fderiv_zero⟩

/-- The Molnár part of the full input. -/
theorem toMolnar : BirkhoffMolnar38 B.toBirkhoffTop38 :=
  ⟨B.inverse_polynomial⟩

end BirkhoffInput38



namespace BirkhoffAnalytic38

variable {B : BirkhoffTop38} {M : Set ℕ}

theorem analyticOnNhd_TC (hA : BirkhoffAnalytic38 B M) {m : ℕ} (hm : m ∈ M) :
    AnalyticOnNhd ℝ (B.TC m) Set.univ :=
  hA.analytic_T m hm

theorem analyticOnNhd_TinvC (hA : BirkhoffAnalytic38 B M) {m : ℕ} (hm : m ∈ M) :
    AnalyticOnNhd ℝ (B.TinvC m) Set.univ :=
  hA.analytic_Tinv m hm

/-- Analyticity at the levels of `M` restricts to any `M' ⊆ M`. -/
theorem mono (hA : BirkhoffAnalytic38 B M) {M' : Set ℕ} (h : M' ⊆ M) : BirkhoffAnalytic38 B M' :=
  ⟨fun m hm => hA.analytic_T m (h hm), fun m hm => hA.analytic_Tinv m (h hm)⟩

end BirkhoffAnalytic38

/-- Assembling the full input from its parts (analyticity at ALL levels). -/
def BirkhoffInput38.ofParts (B : BirkhoffTop38) (hA : BirkhoffAnalytic38 B Set.univ)
    (hC : BirkhoffCanonical38 B) (hM : BirkhoffMolnar38 B) : BirkhoffInput38 where
  toBirkhoffTop38 := B
  analytic_T := fun m => hA.analytic_T m trivial
  analytic_Tinv := fun m => hA.analytic_Tinv m trivial
  canonical := hC.canonical
  fderiv_zero := hC.fderiv_zero
  inverse_polynomial := hM.inverse_polynomial

/-! ### Regression probes for the split (E01-D5) -/

/-- Probe: the parent of an assembled input is the input it was assembled from. -/
theorem BirkhoffInput38.toBirkhoffTop38_ofParts (B : BirkhoffTop38)
    (hA : BirkhoffAnalytic38 B Set.univ) (hC : BirkhoffCanonical38 B) (hM : BirkhoffMolnar38 B) :
    (BirkhoffInput38.ofParts B hA hC hM).toBirkhoffTop38 = B := rfl

/-- Probe: the old `H¹` action interface for a full input is `action_L2` through the parent. -/
theorem BirkhoffInput38.probe_action (B : BirkhoffInput38) (u : PhysicalL2)
    (_hu : SobolevSquareSummable 1 (physicalFourier u)) (n : ℤ) :
    ‖B.Φ u n‖ ^ 2 = actualGapActionAllE02_38 u n := B.action_L2 u n

/-- Probe: the old flat-field `canonical` and the new `fderiv_zero` are exposed by the parts. -/
theorem BirkhoffInput38.probe_parts (B : BirkhoffInput38) :
    BirkhoffAnalytic38 B.toBirkhoffTop38 {0, 1} ∧ BirkhoffCanonical38 B.toBirkhoffTop38 ∧
      BirkhoffMolnar38 B.toBirkhoffTop38 :=
  ⟨B.toAnalytic.mono (Set.subset_univ _), B.toCanonical, B.toMolnar⟩

/-- **E04 input** (KST arXiv:1505.04455 Thm 1.1 and Cor 1.1(i)): one-smoothing of
`K = T - Id` and `T⁻¹ - Id` from `h^r` to `h^{r+1}`, `r ∈ ℤ≥1`, real analytically. -/
structure OneSmoothingInput38 (B : BirkhoffInput38) : Prop where
  smooth_T : ∀ r : ℕ, 1 ≤ r → ∀ x ∈ seqSobolev38 (r : ℝ),
    B.T x - x ∈ seqSobolev38 ((r + 1 : ℕ) : ℝ)
  smooth_Tinv : ∀ r : ℕ, 1 ≤ r → ∀ z ∈ seqSobolev38 (r : ℝ),
    B.Tinv z - z ∈ seqSobolev38 ((r + 1 : ℕ) : ℝ)
  analytic_smooth_T : ∀ (r : ℕ) (hr : 1 ≤ r),
    AnalyticOnNhd ℝ
      (carrierMap38 (r : ℝ) ((r + 1 : ℕ) : ℝ) (fun x => B.T x - x) (smooth_T r hr)) Set.univ
  analytic_smooth_Tinv : ∀ (r : ℕ) (hr : 1 ≤ r),
    AnalyticOnNhd ℝ
      (carrierMap38 (r : ℝ) ((r + 1 : ℕ) : ℝ) (fun z => B.Tinv z - z) (smooth_Tinv r hr)) Set.univ

/-- **E01.08 flow input**, finite-gap part only: under the solution map `S`, Birkhoff
coordinates of finite-gap fields rotate with frequencies depending only on the actions
(KST Thm 2.1 (B3); GK). `S` is a PARAMETER: it must be instantiated with the actual
global NLS solution map of the D4 well-posedness workstream, never with an arbitrary map
in a declaration presented as S04. -/
structure BirkhoffNLSFlowInput38 (B : BirkhoffTop38) (S : ℝ → PhysicalL2 → PhysicalL2) :
    Prop where
  rotation : ∃ Ω : ℤ → (ℤ → ℝ) → ℝ, (∀ n, Measurable (Ω n)) ∧
    ∀ u : PhysicalL2, {n : ℤ | B.Φ u n ≠ 0}.Finite → ∀ (t : ℝ) (n : ℤ),
      B.Φ (S t u) n =
        Complex.exp (-(((t * Ω n (fun k => ‖B.Φ u k‖ ^ 2) : ℝ) : ℂ) * Complex.I)) * B.Φ u n

end NlsGge.Birkhoff
