import Mathlib
import QuantumNLS.Local021RFinal
import QuantumNLS.Local008CapR29a
import QuantumNLS.Local006FinalJ
import QuantumNLS.Local018ModulusImageRound11
import QuantumNLS.Local020Rr

/-!
# LOCAL-023, stage P: the "full analytic diffeomorphism" premise is PROVED, not assumed

Source: `local_transform.tex:10` (`thm:reset-open-transform`).  The printed theorem does NOT assume that the exact-modulus family
`ζ = g√r` is a diffeomorphism of a ball onto itself; its proof (`local_transform.tex:84-90`) says "The exact-modulus image lemma makes `ζ` a
diffeomorphism of this entire ball onto itself".  The image lemma is LOCAL-018 (`lem:reset-modulus-image`, `symplectic_correction.tex:298`);
its hypotheses (`ζ` real analytic, `ζ(0)=0`, `‖ζ(u)‖=‖u‖`, `sup ‖Dζ−1‖ ≤ ε < 1`) are supplied by the accepted LOCAL-008 / LOCAL-006
(`Local008CapR29a.exact_factor_with_radius_cap` with the LOCAL-006 chart `reset_collective_spectral`) and the exact mass identity.

`fullDiffeoPremise L : FullDiffeoPremise L (π / L)` is the premise of the repaired LOCAL-021 headline
(`Local021Repair.reset_moser_covariance_full`), for the contour radius `r = π/L` fixed internally (as in the accepted LOCAL-008).
It is proved for EVERY LOCAL-020 family `(a, b, rr)` on a ball `ρ` at unit coupling:
* the LOCAL-008 family is identified with the given family on a common ball (the reduction coefficient `b_n` is determined by the printed
  LOCAL-003 matrix identity `Pkg`, `b_eq_of_pkg`; the exact-mass factor `rr_n` by analyticity and the mass identity, `Local020Rr.eq_of_mul_eq`);
* `ζ̃ = ζ ∘ 𝓕⁻¹` is then analytic with `‖Dζ̃ − 1‖ ≤ C‖x‖²`, so LOCAL-018 gives the analytic inverse `η` of a ball onto itself.
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

open QuantumNLS.D01LocalPrimitive (K)
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Fourier (fourierL2)
open QuantumNLS.Local021 QuantumNLS.Local021R
open QuantumNLS.Local007Final (gcoef Pkg)
open QuantumNLS.Local007Statement (Fmap)
open QuantumNLS.Local006.CollectiveF (scalarG)
open QuantumNLS.RootIndexedMasses (masses)

variable {L : ℝ} [Fact (0 < L)]

/-- `𝓕⁻¹ : ℓ²(ℤ) → L²(𝕋_L)` as a real-linear bounded map. -/
def Fi (L : ℝ) [Fact (0 < L)] : K →L[ℝ] L2T L := ((Setting.Fcle L).symm : K →L[ℝ] L2T L)

theorem Fi_apply (x : K) : Fi L x = (fourierL2 L).symm x := rfl

theorem norm_Fi (x : K) : ‖Fi L x‖ = ‖x‖ := by
  rw [Fi_apply]; exact LinearIsometryEquiv.norm_map _ _

theorem Fmap_comp_Fi : (Fmap : L2T L →L[ℝ] K).comp (Fi L) = ContinuousLinearMap.id ℝ K :=
  ContinuousLinearMap.ext fun y => (fourierL2 L).apply_symm_apply y

theorem norm_Fi_le : ‖Fi L‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by rw [norm_Fi, one_mul]

/-- The reduction coefficient `b_n(u)` is determined by the printed matrix identity of `Pkg`. -/
theorem b_eq_of_pkg {κ r ρ C : ℝ} {a : ℤ → L2T L → ℝ} {b : ℤ → L2T L → ℂ}
    (hpk : ∀ n, Pkg L κ r ρ C n (a n) (b n)) {u : L2T L} (hu : u ∈ ball (0 : L2T L) ρ) (n : ℤ) :
    b n u = QuantumNLS.Local003Analytic.Bf L κ (QuantumNLS.LocalSpectral.circleRep u) n r
        (QuantumNLS.LocalSpectral.vec2 1 0) 1 := by
  have hm := (hpk n).2.2.2.1 u hu ((hpk n).2.2.1 u hu) (QuantumNLS.LocalSpectral.vec2 1 0)
  rw [QuantumNLS.Local003Analytic.reducedMatrix2_eq] at hm
  have hm' := congrArg (fun w : QuantumNLS.LocalSpectral.E2 => w 1) hm
  simpa [QuantumNLS.LocalSpectral.vec2] using hm'.symm

theorem eval_analytic {R : L2T L → (ℤ →ᵇ ℝ)} {ρ0 : ℝ} (h : AnalyticOnNhd ℝ R (ball (0 : L2T L) ρ0)) (m : ℤ) :
    AnalyticOnNhd ℝ (fun x : L2T L => (R x) m) (ball (0 : L2T L) ρ0) := by
  intro x hx
  exact ((BoundedContinuousFunction.evalCLM ℝ m).analyticAt (R x)).comp (h x hx)

/-- Two families with the printed `Pkg`, analytic `rr` and the mass identity agree on a common small ball. -/
theorem family_agree {κ r ρ C ρ' C' : ℝ} (hκ : 0 < κ) {a a' : ℤ → L2T L → ℝ} {b b' : ℤ → L2T L → ℂ}
    {rr rr' : L2T L → (ℤ →ᵇ ℝ)} (hC : 0 ≤ C)
    (hpk : ∀ n, Pkg L κ r ρ C n (a n) (b n)) (hrr : AnalyticOnNhd ℝ rr (ball (0 : L2T L) ρ))
    (hmass : ∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ, (masses hκ u).1 n = ‖gcoef L κ * b n u‖ ^ 2 * rr u n)
    (hpk' : ∀ n, Pkg L κ r ρ' C' n (a' n) (b' n)) (hrr' : AnalyticOnNhd ℝ rr' (ball (0 : L2T L) ρ'))
    (hmass' : ∀ u ∈ ball (0 : L2T L) ρ', ∀ n : ℤ, (masses hκ u).1 n = ‖gcoef L κ * b' n u‖ ^ 2 * rr' u n)
    {ρ1 : ℝ} (hρ1 : 0 < ρ1) (h1 : ρ1 ≤ ρ) (h2 : ρ1 ≤ ρ') (hsmall : C * ρ1 ^ 2 < 1) :
    ∀ u ∈ ball (0 : L2T L) ρ1, ∀ n : ℤ, b' n u = b n u ∧ rr' u n = rr u n := by
  have hs1 : ball (0 : L2T L) ρ1 ⊆ ball (0 : L2T L) ρ := ball_subset_ball h1
  have hs2 : ball (0 : L2T L) ρ1 ⊆ ball (0 : L2T L) ρ' := ball_subset_ball h2
  have hb : ∀ u ∈ ball (0 : L2T L) ρ1, ∀ n : ℤ, b' n u = b n u := fun u hu n =>
    (b_eq_of_pkg hpk' (hs2 hu) n).trans (b_eq_of_pkg hpk (hs1 hu) n).symm
  intro u hu n
  refine ⟨hb u hu n, ?_⟩
  have hg : AnalyticOnNhd ℝ (fun w : L2T L => gcoef L κ * b n w) (ball (0 : L2T L) ρ1) :=
    (hpk n).2.2.2.2.2.1.mono hs1
  obtain ⟨w0, hw0, hg0⟩ := QuantumNLS.Local020Rr.g_ne_zero (hpk n) hC hρ1 h1 hsmall
  have heq := QuantumNLS.Local020Rr.eq_of_mul_eq hg ⟨w0, hw0, hg0⟩
    ((eval_analytic hrr' n).mono hs2) ((eval_analytic hrr n).mono hs1)
    (fun w hw => by
      have e1 := hmass' w (hs2 hw) n
      have e2 := hmass w (hs1 hw) n
      rw [hb w hw n] at e1
      show ‖gcoef L κ * b n w‖ ^ 2 * (rr' w) n = ‖gcoef L κ * b n w‖ ^ 2 * (rr w) n
      rw [← e1, ← e2])
  exact heq u hu

/-- **The printed full-analytic-diffeomorphism premise, proved.**  (`ζ̃ = ζ∘𝓕⁻¹` is a real analytic diffeomorphism of a ball onto itself,
for every LOCAL-020 family at unit coupling, contour radius `π/L`.) -/
theorem fullDiffeoPremise : FullDiffeoPremise L (Real.pi / L) := by
  intro ρ C a b rr hρ hC F
  have hL : 0 < L := Fact.out
  have hr : 0 < Real.pi / L := div_pos Real.pi_pos hL
  have hr2 : Real.pi / L < 2 * Real.pi / L :=
    div_lt_div_of_pos_right (by linarith [Real.pi_pos]) hL
  have hs : Real.pi / L < QuantumNLS.ResetFreeResolventLOCAL001.spacing L / 2 := by
    convert hr2 using 1
    unfold QuantumNLS.ResetFreeResolventLOCAL001.spacing
    ring
  obtain ⟨ρg, hρg, Cg, hCg, G, p, e, hGa, hp, hGv, hG0, hF, he, hes, het, hei, heai,
    heven, h5, hGd, hg3, hsums, hkernel⟩ :=
    QuantumNLS.Local006.FinalJ.reset_collective_spectral hL (one_pos : (0 : ℝ) < 1) hr hs
  obtain ⟨ρ', hρ', hρ'g, Cr, hCr, a', b', rr', hpk, hrr, hmass, hbd, hrr0, hrr1, hrr2, hconditional⟩ :=
    QuantumNLS.Local008CapR29a.exact_factor_with_radius_cap ρg hρg (one_pos : (0 : ℝ) < 1) hr hr2
  have hsub : ball (0 : L2T L) ρ' ⊆ ball (0 : L2T L) ρg := ball_subset_ball hρ'g
  have hentry : ∀ u ∈ ball (0 : L2T L) ρ', ∀ n : ℤ,
      scalarG L 1 (Real.pi / L) u n = gcoef L 1 * b' n u := by
    intro u hu n
    have hb := b_eq_of_pkg hpk hu n
    change gcoef L 1 * _ = gcoef L 1 * b' n u
    rw [hb]
  have hGentry : ∀ u ∈ ball (0 : L2T L) ρ', ∀ n : ℤ, G u n = gcoef L 1 * b' n u :=
    fun u hu n => (hGv u (hsub hu) n).trans (hentry u hu n)
  have hFmap : (QuantumNLS.Local006.FirstJetF.fourierR L : L2T L →L[ℝ] K) = Fmap := by
    ext u
    rfl
  have hGder : ∀ u ∈ ball (0 : L2T L) ρ', ‖fderiv ℝ G u - Fmap‖ ≤ Cg * ‖u‖ ^ 2 := by
    intro u hu
    simpa only [hFmap] using hGd u (hsub hu)
  obtain ⟨Z, Cz, hCz, hZn, hZa, hZd, hnorm⟩ :=
    hconditional G Cg hCg hGentry (hGa.mono hsub) hGder
  -- a common radius
  set ρ1 : ℝ := min (min ρ ρ') (min (1 / (C + 1)) (1 / (Cz + 1))) with hρ1def
  have hρ1pos : 0 < ρ1 := lt_min (lt_min hρ hρ') (lt_min (by positivity) (by positivity))
  have hρ1ρ : ρ1 ≤ ρ := (min_le_left _ _).trans (min_le_left _ _)
  have hρ1ρ' : ρ1 ≤ ρ' := (min_le_left _ _).trans (min_le_right _ _)
  have hρ1C : ρ1 ≤ 1 / (C + 1) := (min_le_right _ _).trans (min_le_left _ _)
  have hρ1Z : ρ1 ≤ 1 / (Cz + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hsmallC : C * ρ1 ^ 2 < 1 := by
    have h3 : ρ1 * (C + 1) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hρ1C
    nlinarith [sq_nonneg ρ1, mul_nonneg hρ1pos.le hC]
  have hsmallZ : Cz * ρ1 ^ 2 < 1 := by
    have h3 : ρ1 * (Cz + 1) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hρ1Z
    nlinarith [sq_nonneg ρ1, mul_nonneg hρ1pos.le hCz]
  have hag := family_agree (one_pos : (0 : ℝ) < 1) hC F.1 F.2.1 F.2.2.1 hpk hrr hmass hρ1pos hρ1ρ hρ1ρ' hsmallC
  have hsub1 : ball (0 : L2T L) ρ1 ⊆ ball (0 : L2T L) ρ := ball_subset_ball hρ1ρ
  have hsub1' : ball (0 : L2T L) ρ1 ⊆ ball (0 : L2T L) ρ' := ball_subset_ball hρ1ρ'
  have hFi : ∀ x ∈ ball (0 : K) ρ1, Fi L x ∈ ball (0 : L2T L) ρ1 := fun x hx => by
    rw [mem_ball_zero_iff, norm_Fi]; exact mem_ball_zero_iff.1 hx
  -- `ζ̃ = Z ∘ 𝓕⁻¹` on the ball
  have hzt : ∀ x ∈ ball (0 : K) ρ1, zetaT L 1 b rr x = Z (Fi L x) := by
    intro x hx
    have hu := hFi x hx
    show zetaK L 1 b rr (Fi L x) = Z (Fi L x)
    refine lp.ext (funext fun n => ?_)
    rw [zetaK_apply F (hsub1 hu) n]
    show gcoef L 1 * b n (Fi L x) * ((Real.sqrt (rr (Fi L x) n) : ℝ) : ℂ) = Z (Fi L x) n
    rw [hZn _ (hsub1' hu) n, (hag _ hu n).1, (hag _ hu n).2]
  have han : AnalyticOnNhd ℝ (zetaT L 1 b rr) (ball (0 : K) ρ1) := by
    intro x hx
    have h1 : AnalyticAt ℝ (fun y : K => Z (Fi L y)) x :=
      (hZa (Fi L x) (hsub1' (hFi x hx))).comp ((Fi L).analyticAt x)
    refine h1.congr ?_
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy using (hzt y hy).symm
  have hder : ∀ x ∈ ball (0 : K) ρ1,
      ‖fderiv ℝ (zetaT L 1 b rr) x - 1‖ ≤ Cz * ρ1 ^ 2 := by
    intro x hx
    have hu' : Fi L x ∈ ball (0 : L2T L) ρ' := hsub1' (hFi x hx)
    have hev : zetaT L 1 b rr =ᶠ[𝓝 x] fun y => Z (Fi L y) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy using hzt y hy
    have h1 : HasFDerivAt (fun y => Z (Fi L y)) ((fderiv ℝ Z (Fi L x)).comp (Fi L)) x :=
      ((hZa (Fi L x) hu').differentiableAt.hasFDerivAt).comp x (Fi L).hasFDerivAt
    rw [hev.fderiv_eq, h1.fderiv]
    have e : (fderiv ℝ Z (Fi L x)).comp (Fi L) - 1 = (fderiv ℝ Z (Fi L x) - Fmap).comp (Fi L) := by
      refine ContinuousLinearMap.ext fun y => ?_
      have hy : Fmap (Fi L y) = y := (fourierL2 L).apply_symm_apply y
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hy]
    rw [e]
    have hb := hZd (Fi L x) hu'
    have hn : ‖Fi L x‖ ^ 2 ≤ ρ1 ^ 2 := by
      rw [norm_Fi]
      have := mem_ball_zero_iff.1 hx
      nlinarith [norm_nonneg x]
    calc ‖(fderiv ℝ Z (Fi L x) - Fmap).comp (Fi L)‖
        ≤ ‖fderiv ℝ Z (Fi L x) - Fmap‖ * ‖Fi L‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (Cz * ‖Fi L x‖ ^ 2) * 1 := mul_le_mul hb norm_Fi_le (norm_nonneg _) (mul_nonneg hCz (sq_nonneg _))
      _ ≤ Cz * ρ1 ^ 2 := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hn hCz
  have hnormz : ∀ x ∈ ball (0 : K) ρ1, ‖zetaT L 1 b rr x‖ = ‖x‖ := by
    intro x hx
    have hu := hFi x hx
    show ‖zetaK L 1 b rr (Fi L x)‖ = ‖x‖
    rw [norm_zetaK F (hsub1 hu), norm_Fi]
  obtain ⟨-, -, -, -, -, g, -, hgl, hg⟩ :=
    QuantumNLS.Local018ModulusImage.reset_modulus_image (E := K) (f := zetaT L 1 b rr) (R := ρ1)
      (ε := Cz * ρ1 ^ 2) hρ1pos (fun x hx => han x hx) hnormz hsmallZ hder
  refine ⟨ρ1, hρ1pos, hρ1ρ, g, han, ?_, ?_, ?_, ?_⟩
  · intro y hy
    exact (hg y hy).2.2.1
  · intro y hy
    exact (hg y hy).1
  · intro y hy
    exact (hg y hy).2.1
  · intro x hx
    exact hgl x hx

end QuantumNLS.Local023

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.Local023.b_eq_of_pkg
#print axioms QuantumNLS.Local023.family_agree
#print axioms QuantumNLS.Local023.fullDiffeoPremise
