import Mathlib
import QuantumNLS.Local023Scale
import QuantumNLS.Local021RHeadline
import QuantumNLS.ResetNormalizationUniquenessLOCAL022

/-!
# LOCAL-023 `thm:reset-open-transform` (`local_transform.tex:10`): the canonical transform on one full `L²` ball

Printed statement (`local_transform.tex:10-62`).  Fix `L, κ > 0`.  There is `d_L > 0`, independent of Fourier labels and support, such that with `δ = d_L/√κ` the procedure defines a real-analytic diffeomorphism
`Φ_κ : B_δ(L²(𝕋_L;ℂ)) → B_δ(ℓ²(ℤ;ℂ))`, built from the quantum-derived spatial matrix, the indexed masses, exact occupations, and the general analytic operations proved above;
for all inputs in the ball: `|Φ_κ(u)_n|² = I_n^{(κ)}(u)`, `‖Φ_κ(u)‖² = ‖u‖²`, `DΦ_κ(0) = 𝓕`, `2 Im⟨DΦ_κ(u)h, DΦ_κ(u)k⟩ = 2 Im⟨h,k⟩`;
the differentials are bounded and invertible and `‖DΦ_κ(u) − 𝓕‖ + ‖DΦ_κ⁻¹(Φ_κ(u)) − 𝓕⁻¹‖ ≤ C_L κ ‖u‖²`; constants depend on `L` only (not on support cardinality, largest label, smallest positive action),
the radius on `L, κ`; the origin, all zero-action strata and arbitrary infinite support belong to the theorem; Fourier covariances (common phase, translations, integral boosts, conjugation, reflection);
`Φ_κ` equals the Fourier transform on every Fourier plane; uniqueness among canonical exact-modulus charts on a common ball by `DΦ(0) = 𝓕` and `Φ(conj u(−·)) = conj Φ(u)`;
`Φ_κ(su) = sΦ_{κs²}(u)`; the full `C¹` Fourier limit as `κ ↓ 0` on every fixed bounded `L²` ball.

**Fidelity notes** (see also the module docstrings of `Local023Premise`, `Local023Phi`, `Local023Scale`).
* No "full analytic diffeomorphism" hypothesis: the theorem has only `[Fact (0 < L)]`.  The image of the exact-modulus map is derived inside the proof from LOCAL-018 (`Local023Premise.fullDiffeoPremise`).
* The contour radius of the Riesz projection is fixed internally to `π/L` (as in the accepted LOCAL-008); `d` and `CL` are chosen once from `L`, before `κ` (the printed "radius `d_L/√κ`" and "constants depend on `L`").
* `Φ κ` is the printed procedure: for every LOCAL-020 family `Fam020` at coupling `κ` the clause (procedure) provides the constructed LOCAL-021 `Setting` (LOCAL-017 outputs `S`, `S⁻¹` = the time-one flow of `Y_t = Ycov(t(Ω−ω), β⁰)` with the radial and Haar primitive; `Φ = S⁻¹ ∘ ζ`,
  `Setting.Phi`), all printed per-setting properties `SettingProps`, and `Setting.Phi = Φ κ` on the common domain; `Φ κ` itself is the printed scaling `Φ̂_κ(u) = κ^{-1/2} Φ_1(√κ u)` of the unit-coupling construction.
* `masses hκ u` is the literal physical indexed mass `I_n^{(κ)}(u)` (R-950BFB30).  `omega h k = 2 Im⟨h,k⟩`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric MeasureTheory BoundedContinuousFunction

namespace QuantumNLS.Local023

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.ResetMoser QuantumNLS.ResetMoserClamp
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Fourier (fourierL2 modeLp)
open QuantumNLS.Local021 QuantumNLS.Local021R
open QuantumNLS.LocalSpectral (pm)
open QuantumNLS.RootIndexedMasses (masses)
open QuantumNLS.ResetNormalizationUniqueness (IsStronglySymplecticOn Cphys)

theorem dom_lt {κ d t : ℝ} (hκ : 0 < κ) (ht : t < d / Real.sqrt κ) : Real.sqrt κ * t < d := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  rw [mul_comm]; exact (lt_div_iff₀ hs).1 ht

theorem lt_dom {κ d t : ℝ} (hκ : 0 < κ) (ht : Real.sqrt κ * t < d) : t < d / Real.sqrt κ := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  rw [lt_div_iff₀ hs, mul_comm]; exact ht

/-- **LOCAL-023 `thm:reset-open-transform`.**  Only `L > 0`; no diffeomorphism hypothesis. -/
theorem reset_open_transform (L : ℝ) [Fact (0 < L)] :
    ∃ d CL : ℝ, 0 < d ∧ 0 ≤ CL ∧
    ∃ (Φ : ℝ → L2T L → K) (Ψ : ℝ → K → L2T L),
      (∀ (κ : ℝ) (hκ : 0 < κ),
        -- (a) `Φ_κ : B_δ(L²) → B_δ(ℓ²)` is a real-analytic diffeomorphism, `δ = d/√κ`
        AnalyticOnNhd ℝ (Φ κ) (ball (0 : L2T L) (d / Real.sqrt κ)) ∧
        AnalyticOnNhd ℝ (Ψ κ) (ball (0 : K) (d / Real.sqrt κ)) ∧
        MapsTo (Φ κ) (ball (0 : L2T L) (d / Real.sqrt κ)) (ball (0 : K) (d / Real.sqrt κ)) ∧
        MapsTo (Ψ κ) (ball (0 : K) (d / Real.sqrt κ)) (ball (0 : L2T L) (d / Real.sqrt κ)) ∧
        (∀ u ∈ ball (0 : L2T L) (d / Real.sqrt κ), Ψ κ (Φ κ u) = u) ∧
        (∀ y ∈ ball (0 : K) (d / Real.sqrt κ), Φ κ (Ψ κ y) = y) ∧
        -- (b) the procedure: the LOCAL-020 families exist at coupling `κ`; on each of them the constructed LOCAL-017/LOCAL-021 data have all printed
        --     properties and `Φ = S⁻¹ ∘ ζ` of the procedure equals `Φ_κ` on the common domain
        (∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧
          ∃ (a : ℤ → L2T L → ℝ) (b : ℤ → L2T L → ℂ) (rr : L2T L → (ℤ →ᵇ ℝ)),
            Fam020 L κ (Real.pi / L) ρ C hκ a b rr) ∧
        (∀ (ρ C : ℝ) (a : ℤ → L2T L → ℝ) (b : ℤ → L2T L → ℂ) (rr : L2T L → (ℤ →ᵇ ℝ)),
          0 < ρ → 0 ≤ C → Fam020 L κ (Real.pi / L) ρ C hκ a b rr →
          ∃ S : Setting L κ (Real.pi / L) hκ, S.ρ = ρ ∧ S.C = C ∧ S.a = a ∧ S.b = b ∧ S.rr = rr ∧
            SettingProps S ∧
            ∀ u : L2T L, ‖u‖ < S.rM → Real.sqrt κ * ‖u‖ < d → S.Phi u = Φ κ u) ∧
        -- (c) `|Φ_κ(u)_n|² = I_n^{(κ)}(u)`
        (∀ u ∈ ball (0 : L2T L) (d / Real.sqrt κ), ∀ n : ℤ, ‖Φ κ u n‖ ^ 2 = (masses hκ u).1 n) ∧
        -- (d) `‖Φ_κ(u)‖² = ‖u‖²`
        (∀ u ∈ ball (0 : L2T L) (d / Real.sqrt κ), ‖Φ κ u‖ ^ 2 = ‖u‖ ^ 2) ∧
        -- (e) `DΦ_κ(0) = 𝓕`
        (∀ h : L2T L, fderiv ℝ (Φ κ) 0 h = fourierL2 L h) ∧
        -- (f) `2 Im ⟨DΦ_κ(u)h, DΦ_κ(u)k⟩ = 2 Im ⟨h, k⟩`
        (∀ u ∈ ball (0 : L2T L) (d / Real.sqrt κ), ∀ h k : L2T L,
          2 * (inner ℂ (fderiv ℝ (Φ κ) u h) (fderiv ℝ (Φ κ) u k)).im = 2 * (inner ℂ h k).im) ∧
        -- (g) bounded invertible differentials, with `D(Φ_κ⁻¹)(Φ_κ(u))` the inverse, and the printed quadratic bound
        (∀ u ∈ ball (0 : L2T L) (d / Real.sqrt κ), ∃ e : L2T L ≃L[ℝ] K,
          ⇑e = ⇑(fderiv ℝ (Φ κ) u) ∧ HasFDerivAt (Ψ κ) (e.symm : K →L[ℝ] L2T L) (Φ κ u) ∧
          ‖fderiv ℝ (Φ κ) u - Setting.Fcl L‖ +
            ‖(e.symm : K →L[ℝ] L2T L) - ((Setting.Fcle L).symm : K →L[ℝ] L2T L)‖ ≤ CL * κ * ‖u‖ ^ 2) ∧
        -- (h) Fourier covariances: translations, integral boosts, reflection, conjugation, common phase, conjugation-reflection
        (∀ u ∈ ball (0 : L2T L) (d / Real.sqrt κ), ∀ n : ℤ,
          (∀ y : ℝ, Φ κ (QuantumNLS.BornTranslation.trans y u) n =
            Complex.exp (Complex.I * ((pm L n : ℝ) : ℂ) * (y : ℂ)) * Φ κ u n) ∧
          (∀ k : ℤ, Φ κ (QuantumNLS.RootMassBoostSymbol.boost k u) n = Φ κ u (n - k)) ∧
          Φ κ (QuantumNLS.ResetNormalizationUniqueness.reflectR L u) n = Φ κ u (-n) ∧
          Φ κ (star u) n = conj (Φ κ u (-n)) ∧
          (∀ φ : ℝ, Φ κ (Complex.exp ((φ : ℂ) * Complex.I) • u) n =
            Complex.exp ((φ : ℂ) * Complex.I) * Φ κ u n) ∧
          Φ κ (Cphys L u) n = conj (Φ κ u n)) ∧
        -- (i) `Φ_κ` is the ordinary Fourier transform on every Fourier plane
        (∀ (k : ℤ) (c : ℂ), ‖c‖ < d / Real.sqrt κ →
          Φ κ (c • modeLp L k) = fourierL2 L (c • modeLp L k)) ∧
        -- (j) uniqueness among canonical exact-modulus charts on a common ball, by `DΦ(0) = 𝓕` and `Φ(conj u(−·)) = conj Φ(u)`
        (∀ r0 : ℝ, 0 < r0 → r0 ≤ d / Real.sqrt κ → ∀ Ψ' : L2T L → K,
          IsStronglySymplecticOn (ball (0 : L2T L) r0) (ball (0 : K) r0) Ψ' →
          AnalyticOnNhd ℝ Ψ' (ball (0 : L2T L) r0) →
          (∀ u ∈ ball (0 : L2T L) r0, ∀ n : ℤ, ‖Ψ' u n‖ ^ 2 = (masses hκ u).1 n) →
          (∀ h : L2T L, fderiv ℝ Ψ' 0 h = fourierL2 L h) →
          (∀ u ∈ ball (0 : L2T L) r0, Ψ' (Cphys L u) = star (Ψ' u)) →
          ∀ u ∈ ball (0 : L2T L) r0, Ψ' u = Φ κ u)) ∧
      -- (k) scaling `Φ_κ(su) = sΦ_{κs²}(u)`
      (∀ (κ : ℝ), 0 < κ → ∀ s : ℝ, 0 < s → ∀ u : L2T L, ‖u‖ < d / Real.sqrt (κ * s ^ 2) →
        Φ κ (s • u) = s • Φ (κ * s ^ 2) u) ∧
      -- (l) the full `C¹` Fourier limit as `κ ↓ 0` on every fixed bounded `L²` ball
      (∀ ρ0 : ℝ, 0 < ρ0 → ∀ ε : ℝ, 0 < ε → ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ < κ0 →
        ∀ u : L2T L, ‖u‖ < ρ0 → ‖u‖ < d / Real.sqrt κ ∧
          ‖Φ κ u - Setting.Fcl L u‖ ≤ ε ∧ ‖fderiv ℝ (Φ κ) u - Setting.Fcl L‖ ≤ ε) := by
  have hL : 0 < L := Fact.out
  have hr : 0 < Real.pi / L := div_pos Real.pi_pos hL
  have hr2 : Real.pi / L < 2 * Real.pi / L := div_lt_div_of_pos_right (by linarith [Real.pi_pos]) hL
  obtain ⟨ρ0, hρ0, C1, hC1, a1, b1, rr1, F1⟩ := fam020_exists (L := L) (κ := 1) (r := Real.pi / L) one_pos hr hr2
  obtain ⟨Ch, c1, c2, c3, c4, c5⟩ :=
    QuantumNLS.Local021Repair.unit_chart_of_family (fullDiffeoPremise (L := L)) hρ0 hC1 F1
  obtain ⟨S, g1, g2, g3, g4, g5⟩ := Ch.exists_setting
  have hc : Corr S := corr S hr hr2
  obtain ⟨C0, δ0, hC0, hδ0, hδ0M, hq⟩ := fderiv_Phi_quad S
  set d : ℝ := min δ0 (1 / (2 * (C0 + 1))) with hd
  have hdpos : 0 < d := lt_min hδ0 (by positivity)
  have hdδ : d ≤ δ0 := min_le_left _ _
  have hdM : d ≤ S.rM := hdδ.trans hδ0M
  have hd2 : d ≤ 1 / (2 * (C0 + 1)) := min_le_right _ _
  have hdsmall : C0 * d ^ 2 ≤ 1 / 2 := by
    have h1 : d * (2 * (C0 + 1)) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hd2
    have h2 : C0 * d ≤ 1 / 2 := by nlinarith [mul_nonneg hC0 hdpos.le]
    have h3 : d ≤ 1 / 2 := by nlinarith [mul_nonneg hC0 hdpos.le]
    nlinarith [mul_le_mul_of_nonneg_left h3 (mul_nonneg hC0 hdpos.le)]
  refine ⟨d, 3 * C0, hdpos, by positivity, fun κ => PhiHat S κ, fun κ => PsiHat S κ, ?_, ?_, ?_⟩
  · -- the per-coupling clauses
    intro κ hκ
    have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
    -- every point of the ball is in the unit domain after scaling
    have hdom : ∀ {t : ℝ}, t < d / Real.sqrt κ → Real.sqrt κ * t < S.rM := fun ht =>
      lt_of_lt_of_le (dom_lt hκ ht) hdM
    have hdomδ : ∀ {t : ℝ}, t < d / Real.sqrt κ → Real.sqrt κ * t < δ0 := fun ht =>
      (dom_lt hκ ht).trans_le hdδ
    have hfd : ∀ {u : L2T L}, ‖u‖ < d / Real.sqrt κ →
        fderiv ℝ (PhiHat S κ) u = fderiv ℝ S.Phi (Real.sqrt κ • u) := fun {u} hu =>
      (hasFDerivAt_PhiHat S hs (hdom hu)).fderiv
    have hsymp : ∀ {u : L2T L}, ‖u‖ < d / Real.sqrt κ → ∀ h k : L2T L,
        omega (fderiv ℝ (PhiHat S κ) u h) (fderiv ℝ (PhiHat S κ) u k) = omega h k := by
      intro u hu h k
      have hv := smul_norm_lt S hκ (hdom hu)
      rw [hfd hu]
      exact omega_DPhi S hc hv h k
    have hDhat : ∀ h : L2T L, fderiv ℝ (PhiHat S κ) 0 h = fourierL2 L h := by
      intro h
      have h0 : ‖(0 : L2T L)‖ < d / Real.sqrt κ := by rw [norm_zero]; exact div_pos hdpos hs
      have hF0 : fderiv ℝ S.Phi 0 = Setting.Fcl L := (settingProps hr hr2 S).2.2.2.2.2
      rw [hfd h0, smul_zero, hF0]
      exact Setting.Fcl_apply h
    have hmass : ∀ {u : L2T L}, ‖u‖ < d / Real.sqrt κ → ∀ n : ℤ,
        ‖PhiHat S κ u n‖ ^ 2 = (masses hκ u).1 n := fun {u} hu n =>
      norm_PhiHat_apply S hc hκ (hdom hu) n
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu
      exact analyticAt_PhiHat S hc hκ (hdom (mem_ball_zero_iff.1 hu))
    · intro y hy
      exact analyticAt_PsiHat S hc hκ (hdom (mem_ball_zero_iff.1 hy))
    · intro u hu
      have := hdom (mem_ball_zero_iff.1 hu)
      rw [mem_ball_zero_iff, norm_PhiHat S hκ this]; exact mem_ball_zero_iff.1 hu
    · intro y hy
      have := hdom (mem_ball_zero_iff.1 hy)
      rw [mem_ball_zero_iff, norm_PsiHat S hc hκ this]; exact mem_ball_zero_iff.1 hy
    · intro u hu
      exact PsiHat_PhiHat S hc hκ (hdom (mem_ball_zero_iff.1 hu))
    · intro y hy
      exact PhiHat_PsiHat S hc hκ (hdom (mem_ball_zero_iff.1 hy))
    · exact fam020_exists hκ hr hr2
    · intro ρ C a b rr hρ hC F
      obtain ⟨S', h1, h2, h3, h4, h5⟩ := (Chart.atCoupling Ch hκ hρ hC F).exists_setting
      refine ⟨S', h1, h2, h3, h4, h5, settingProps hr hr2 S', fun u hu hsu => ?_⟩
      exact PhiHat_eq S S' hu (lt_of_lt_of_le hsu hdM)
    · intro u hu n
      exact hmass (mem_ball_zero_iff.1 hu) n
    · intro u hu
      rw [norm_PhiHat S hκ (hdom (mem_ball_zero_iff.1 hu))]
    · exact hDhat
    · intro u hu h k
      exact hsymp (mem_ball_zero_iff.1 hu) h k
    · intro u hu
      have hu0 := mem_ball_zero_iff.1 hu
      obtain ⟨e, he1, he2, he3⟩ := exists_equiv_hat S hc hκ (hdom hu0)
      have hfd' : fderiv ℝ (PhiHat S κ) u = (e : L2T L →L[ℝ] K) := he2.fderiv
      refine ⟨e, by rw [hfd']; rfl, he3, ?_⟩
      obtain ⟨-, hb⟩ := PhiHat_deriv_bound S hδ0M hq hκ (hdomδ hu0)
      rw [hfd']
      rw [← he1] at hb
      have hε : C0 * κ * ‖u‖ ^ 2 ≤ 1 / 2 := by
        have e2 : C0 * κ * ‖u‖ ^ 2 = C0 * (Real.sqrt κ * ‖u‖) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hκ.le]; ring
        rw [e2]
        have hlt := dom_lt hκ hu0
        have : (Real.sqrt κ * ‖u‖) ^ 2 ≤ d ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg hs.le (norm_nonneg _)) hlt.le 2
        calc C0 * (Real.sqrt κ * ‖u‖) ^ 2 ≤ C0 * d ^ 2 := mul_le_mul_of_nonneg_left this hC0
          _ ≤ 1 / 2 := hdsmall
      have hε0 : 0 ≤ C0 * κ * ‖u‖ ^ 2 := by positivity
      have hA' : (e.symm : K →L[ℝ] L2T L).comp (e : L2T L →L[ℝ] K) = ContinuousLinearMap.id ℝ (L2T L) :=
        ContinuousLinearMap.ext fun h => e.symm_apply_apply h
      have hinv := inv_diff_bound hA' hε0 hb hε
      calc ‖(e : L2T L →L[ℝ] K) - Setting.Fcl L‖ +
            ‖(e.symm : K →L[ℝ] L2T L) - ((Setting.Fcle L).symm : K →L[ℝ] L2T L)‖
          ≤ C0 * κ * ‖u‖ ^ 2 + 2 * (C0 * κ * ‖u‖ ^ 2) := add_le_add hb hinv
        _ = 3 * C0 * κ * ‖u‖ ^ 2 := by ring
    · intro u hu n
      exact PhiHat_cov_index S hκ (hdom (mem_ball_zero_iff.1 hu)) n
    · intro k c hc'
      exact PhiHat_plane S hκ k c (hdom hc')
    · -- uniqueness (LOCAL-022)
      intro r0 hr0 hr0d Ψ' hΨ' han hm hD hsym
      have hb0 : ∀ u : L2T L, u ∈ ball (0 : L2T L) r0 → ‖u‖ < d / Real.sqrt κ := fun u hu =>
        lt_of_lt_of_le (mem_ball_zero_iff.1 hu) hr0d
      have hb0' : ∀ y : K, y ∈ ball (0 : K) r0 → ‖y‖ < d / Real.sqrt κ := fun y hy =>
        lt_of_lt_of_le (mem_ball_zero_iff.1 hy) hr0d
      have hΦ : IsStronglySymplecticOn (ball (0 : L2T L) r0) (ball (0 : K) r0) (PhiHat S κ) := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro u hu
          rw [mem_ball_zero_iff, norm_PhiHat S hκ (hdom (hb0 u hu))]; exact mem_ball_zero_iff.1 hu
        · refine ⟨PsiHat S κ, ?_, ?_, ?_, ?_⟩
          · intro y hy
            rw [mem_ball_zero_iff, norm_PsiHat S hc hκ (hdom (hb0' y hy))]; exact mem_ball_zero_iff.1 hy
          · intro u hu
            exact PsiHat_PhiHat S hc hκ (hdom (hb0 u hu))
          · intro y hy
            exact PhiHat_PsiHat S hc hκ (hdom (hb0' y hy))
          · intro y hy
            exact (analyticAt_PsiHat S hc hκ (hdom (hb0' y hy))).differentiableAt
        · intro u hu
          exact (analyticAt_PhiHat S hc hκ (hdom (hb0 u hu))).differentiableAt
        · intro u hu
          obtain ⟨e, he1, he2, he3⟩ := exists_equiv_hat S hc hκ (hdom (hb0 u hu))
          refine ⟨e, ?_⟩
          have hh := congrArg (fun T : L2T L →L[ℝ] K => (⇑T : L2T L → K)) he2.fderiv
          exact hh.symm
        · intro u hu h k
          exact hsymp (hb0 u hu) h k
      have hq0 : ∀ n : ℤ, (masses hκ (0 : L2T L)).1 n = 0 := by
        intro n
        have h0 : ‖(0 : L2T L)‖ < d / Real.sqrt κ := by rw [norm_zero]; exact div_pos hdpos hs
        have h1 := hmass h0 n
        have hz : PhiHat S κ 0 = 0 := by
          show (Real.sqrt κ)⁻¹ • S.Phi (Real.sqrt κ • (0 : L2T L)) = 0
          rw [smul_zero, Phi_zero S, smul_zero]
        rw [hz] at h1
        simpa using h1.symm
      have hanΦ : AnalyticOnNhd ℝ (PhiHat S κ) (ball (0 : L2T L) r0) := fun u hu =>
        analyticAt_PhiHat S hc hκ (hdom (hb0 u hu))
      have hmΦ : ∀ u ∈ ball (0 : L2T L) r0, ∀ n : ℤ, ‖PhiHat S κ u n‖ ^ 2 = (masses hκ u).1 n :=
        fun u hu n => hmass (hb0 u hu) n
      have hsymΦ : ∀ u ∈ ball (0 : L2T L) r0, PhiHat S κ (Cphys L u) = star (PhiHat S κ u) :=
        fun u hu => PhiHat_Cphys S hκ (hdom (hb0 u hu))
      intro u hu
      exact QuantumNLS.ResetNormalizationUniquenessLOCAL022.thm_reset_normalization_uniqueness L hr0
        (fun n u => (masses hκ u).1 n) hq0 Ψ' (PhiHat S κ) hΨ' hΦ han hanΦ hm hmΦ hD hDhat hsym hsymΦ u hu
  · -- scaling
    intro κ hκ s hs u hu
    exact PhiHat_scale S hκ hs u
  · -- the full `C¹` limit
    intro ρ0 hρ0 ε hε
    have hM : 0 < C0 * ρ0 ^ 2 + C0 * ρ0 ^ 3 + 1 := by positivity
    refine ⟨min ((d / ρ0) ^ 2) (ε / (C0 * ρ0 ^ 2 + C0 * ρ0 ^ 3 + 1)), lt_min (by positivity) (by positivity),
      fun κ hκ hκ0 u hu => ?_⟩
    have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
    have hκ1 : κ < (d / ρ0) ^ 2 := lt_of_lt_of_le hκ0 (min_le_left _ _)
    have hκ2 : κ < ε / (C0 * ρ0 ^ 2 + C0 * ρ0 ^ 3 + 1) := lt_of_lt_of_le hκ0 (min_le_right _ _)
    have hsu : Real.sqrt κ * ‖u‖ < d := by
      have h1 : Real.sqrt κ < d / ρ0 := (Real.sqrt_lt' (by positivity)).2 hκ1
      rw [lt_div_iff₀ hρ0] at h1
      calc Real.sqrt κ * ‖u‖ ≤ Real.sqrt κ * ρ0 := mul_le_mul_of_nonneg_left hu.le hs.le
        _ < d := h1
    have hsuδ : Real.sqrt κ * ‖u‖ < δ0 := hsu.trans_le hdδ
    have hκM : κ * (C0 * ρ0 ^ 2 + C0 * ρ0 ^ 3 + 1) < ε := (lt_div_iff₀ hM).1 hκ2
    have hu3 : ‖u‖ ^ 3 ≤ ρ0 ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hu.le 3
    have hu2 : ‖u‖ ^ 2 ≤ ρ0 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hu.le 2
    have hA : 0 ≤ κ * (C0 * ρ0 ^ 2) := by positivity
    have hB : 0 ≤ κ * (C0 * ρ0 ^ 3) := by positivity
    refine ⟨lt_dom hκ hsu, ?_, ?_⟩
    · have h1 := PhiHat_map_bound S hC0 hδ0M hq hκ hsuδ
      calc ‖PhiHat S κ u - Setting.Fcl L u‖ ≤ C0 * κ * ‖u‖ ^ 3 := h1
        _ ≤ C0 * κ * ρ0 ^ 3 := mul_le_mul_of_nonneg_left hu3 (mul_nonneg hC0 hκ.le)
        _ ≤ ε := by nlinarith
    · obtain ⟨hd1, hd2'⟩ := PhiHat_deriv_bound S hδ0M hq hκ hsuδ
      rw [hd1.fderiv]
      calc ‖fderiv ℝ S.Phi (Real.sqrt κ • u) - Setting.Fcl L‖ ≤ C0 * κ * ‖u‖ ^ 2 := hd2'
        _ ≤ C0 * κ * ρ0 ^ 2 := mul_le_mul_of_nonneg_left hu2 (mul_nonneg hC0 hκ.le)
        _ ≤ ε := by nlinarith

end QuantumNLS.Local023

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.Local023.reset_open_transform
