import NlsGge.Birkhoff.W10Localized38
import NlsGge.Birkhoff.W07Probability38e
import NlsGge.Birkhoff.W09Approx38b

/-! # W10a, file 2 (W10.01, W10.03 input): the ball `U_N` in the Cameron-Martin head and the finite map

Source: `paper/v2.tex` l.1644-1655. Conditional on `B : BirkhoffInput38`, `O : OneSmoothingInput38 B`.

Transfers W08 (`D:lem:localinject`, stated on `P_N h⁰` with `h⁰`-coordinates) to the finite head
`V_N = P_N H` (`actualCMHead c N`, the Cameron-Martin head used by the Gaussian `γ_W` and by E05):

* `hn2V38`: the `h²`-norm `‖v‖_{h²}` of a head point (via the inclusion `V_N ↪ E_s ↪ h²`);
* `ballU38 N R'`: the open `h²` ball `{v ∈ V_N : ‖v‖_{h²} < R'}`;
* `headEquiv_TNfin38`: the coordinate identification `V_N ≃ P_N h⁰` intertwines `T_N = P_N T|_{P_N h⁰}`
  with the finite Ramer map `φ_N(v) = v + P_N K(P_N v)` (`TNfin38`);
* `det_fderiv_TNfin_eq_detTN38`: `det Dφ_N(v) = det DT_N(headEquiv v)`;
* `eventually_injOn_ballU38`, `eventually_det_ballU38`: injectivity of `φ_N` on `U_N`, and
  `det Dφ_N ≠ 0`, `|det Dφ_N|⁻¹ ≤ 2` on `U_N`, for all large `N` (W08).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.Ramer Filter Topology
open scoped ENNReal Real

section Ball

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (N : ℕ)

/-- `‖v‖_{h²}` of a head point `v ∈ V_N = P_N H` (coordinates of `v` read in `h²`). -/
def hn2V38 (v : actualCMHead c N) : ℝ :=
  ‖eToSob38 c s (((1 + 1 : ℕ)) : ℝ) (headToE c s N v)‖

theorem continuous_hn2V38 : Continuous (hn2V38 c s N) :=
  (continuous_norm.comp ((continuous_eToSob38 c s _).comp (headToE c s N).continuous))

/-- The open `h²` ball `U_N(R') = {v ∈ V_N : ‖v‖_{h²} < R'}` of the finite head. -/
def ballU38 (R' : ℝ) : Set (actualCMHead c N) := {v | hn2V38 c s N v < R'}

theorem isOpen_ballU38 (R' : ℝ) : IsOpen (ballU38 c s N R') :=
  isOpen_lt (continuous_hn2V38 c s N) continuous_const

theorem measurableSet_ballU38 (R' : ℝ) : MeasurableSet (ballU38 c s N R') :=
  (isOpen_ballU38 c s N R').measurableSet

theorem headEquiv_mem_ballV38 (R' : ℝ) {v : actualCMHead c N} (hv : v ∈ ballU38 c s N R') :
    (headEquiv c s N v) ∈ ballV38 N R' := by
  refine ⟨eToSob38 c s (((1 + 1 : ℕ)) : ℝ) (headToE c s N v), le_of_lt hv, ?_⟩
  apply carrierExt38
  funext n
  rw [carrierCoe38_i20]
  exact (congrFun (carrierCoe_eToSob38 c s _ (headToE c s N v)) n).trans
    (headEquiv_coord c s N v n).symm

end Ball

namespace BirkhoffInput38

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {lower upper : ℝ}
  (c : BoundedCoefficients lower upper) {s : ℝ}

/-- The coordinate identification `V_N ≃ P_N h⁰` intertwines `φ_N` and `T_N = P_N T|_{P_N h⁰}`. -/
theorem headEquiv_TNfin38 (hs1 : s ≤ 1) (N : ℕ) (v : actualCMHead c N) :
    headEquiv c s N (B.TNfin38 O c hs1 N v) = B.TN N (headEquiv c s N v) := by
  apply Subtype.ext
  apply carrierExt38
  funext n
  rw [headEquiv_coord, B.TN_coe, carrierCoe38_projC38]
  have hseq : carrierCoe38 ((0 : ℕ) : ℝ) ((headEquiv c s N v : (cp38 N).V) :
      SobolevCarrier38 ((0 : ℕ) : ℝ)) = eCoe38 c s (headToE c s N v) := by
    funext m
    rw [headEquiv_coord]; rfl
  have hT : carrierCoe38 ((0 : ℕ) : ℝ) (B.TC 0 ((headEquiv c s N v : (cp38 N).V) :
      SobolevCarrier38 ((0 : ℕ) : ℝ))) n = B.T (eCoe38 c s (headToE c s N v)) n := by
    show B.T (carrierCoe38 ((0 : ℕ) : ℝ) _) n = _
    rw [hseq]
  rw [hT]
  have e1 : cmCoord ((B.TNfin38 O c hs1 N v : actualCMHead c N) : ActualCM c) n =
      cmCoord (v : ActualCM c) n +
        cmCoord ((cmTrunc c N (B.KW06_38 O c hs1 (headToE c s N v)) : actualCMHead c N) :
          ActualCM c) n := rfl
  have hK : cmCoord (B.KW06_38 O c hs1 (headToE c s N v)) n =
      B.T (eCoe38 c s (headToE c s N v)) n - eCoe38 c s (headToE c s N v) n :=
    B.cmCoord_KW06_38 O c hs1 (headToE c s N v) n
  have hv : cmCoord (v : ActualCM c) n = eCoe38 c s (headToE c s N v) n := rfl
  rw [e1, cmCoord_cmTrunc]
  by_cases hn : n ∈ symmetricModes N
  · simp only [hn, ↓reduceIte]
    rw [hK, hv]; ring
  · simp only [hn, ↓reduceIte]
    rw [v.2 n hn]; simp

/-- `det Dφ_N(v) = det DT_N(headEquiv v)` (conjugation by the coordinate identification). -/
theorem det_fderiv_TNfin_eq_detTN38 (hs1 : s ≤ 1) (N : ℕ) (v : actualCMHead c N) :
    (fderiv ℝ (B.TNfin38 O c hs1 N) v).det = B.detTN N (headEquiv c s N v) := by
  have h3 : B.detTN N (headEquiv c s N v) =
      LinearMap.det ((B.DTN N (headEquiv c s N v) : (cp38 N).V →L[ℝ] (cp38 N).V) :
        (cp38 N).V →ₗ[ℝ] (cp38 N).V) := by
    unfold detTN
    rw [B.fderiv_TN]
  have h4 := LinearMap.det_conj
    ((fderiv ℝ (B.TNfin38 O c hs1 N) v : actualCMHead c N →L[ℝ] actualCMHead c N) :
      actualCMHead c N →ₗ[ℝ] actualCMHead c N) (headEquiv c s N)
  rw [← B.DTN_eq_conj_W07 O c hs1 N v] at h4
  rw [h3, h4]

/-- **W10.01 (injectivity part).** For every `R'` and all `N ≥ N₀(R')`, the finite Ramer map
`φ_N = (v ↦ v + P_N K(P_N v))` is injective on the open `h²` ball `U_N(R')`. -/
theorem eventually_injOn_ballU38 (hs1 : s ≤ 1) (R' : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, Set.InjOn (B.TNfin38 O c hs1 N) (ballU38 c s N R') := by
  obtain ⟨N₀, hN₀⟩ := B.injOn_TN_ballV38 O R'
  refine ⟨N₀, fun N hN v hv w hw hvw => ?_⟩
  have h1 : B.TN N (headEquiv c s N v) = B.TN N (headEquiv c s N w) := by
    rw [← B.headEquiv_TNfin38 O c hs1, ← B.headEquiv_TNfin38 O c hs1, hvw]
  exact (headEquiv c s N).injective
    (hN₀ N hN (headEquiv_mem_ballV38 c s N R' hv) (headEquiv_mem_ballV38 c s N R' hw) h1)

/-- **W10.03 (Jacobian input).** For every `R'`, eventually in `N`: on `U_N(R')`, `det Dφ_N ≠ 0`,
`|det Dφ_N|⁻¹ ≤ 2` (W08), and `|det Dφ_N| → 1` uniformly. -/
theorem eventually_det_ballU38 (hs1 : s ≤ 1) (R' : ℝ) :
    (∀ᶠ N : ℕ in atTop, ∀ v ∈ ballU38 c s N R',
      (fderiv ℝ (B.TNfin38 O c hs1 N) v).det ≠ 0 ∧
        |(fderiv ℝ (B.TNfin38 O c hs1 N) v).det|⁻¹ ≤ 2) ∧
    (∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ v ∈ ballU38 c s N R',
      abs (|(fderiv ℝ (B.TNfin38 O c hs1 N) v).det| - 1) < ε) := by
  refine ⟨?_, fun ε hε => ?_⟩
  · filter_upwards [B.eventually_inv_abs_detTN_le_two O R'] with N hN v hv
    rw [B.det_fderiv_TNfin_eq_detTN38 O c hs1]
    exact hN _ (headEquiv_mem_ballV38 c s N R' hv)
  · filter_upwards [B.eventually_abs_detTN_sub_one_lt O R' ε hε] with N hN v hv
    rw [B.det_fderiv_TNfin_eq_detTN38 O c hs1]
    exact hN _ (headEquiv_mem_ballV38 c s N R' hv)

end BirkhoffInput38

end NlsGge.Birkhoff
end
