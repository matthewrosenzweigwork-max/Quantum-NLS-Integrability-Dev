import QuantumNLS.Local008CapR29a
import QuantumNLS.Local006FinalJ

/-! LOCAL-008, `cor:reset-exact-modulus-map` (exact_action_factor.tex:295-305).
The contour radius is chosen internally as π/L. The scalar chart is the actual
normalized lower-left reduction entry from LOCAL-006, and I is the actual
indexed mass. All assertions quantify over the entire L² ball and every integer
coordinate, with no support or nonvanishing restriction. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Metric Set BoundedContinuousFunction
namespace QuantumNLS.Local008ModulusR29a
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Local007Final (gcoef Pkg)
open QuantumNLS.Local007Statement (Fmap)
open QuantumNLS.Local006.CollectiveF (Seq scalarG)
variable {L κ : ℝ} [Fact (0 < L)]

/-- The printed exact-modulus corollary, on one full open Hilbert ball. -/
theorem reset_exact_modulus_map (hκ : 0 < κ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∃ (rr : L2T L → (ℤ →ᵇ ℝ)) (Z : L2T L → Seq),
        AnalyticOnNhd ℝ rr (ball (0 : L2T L) ρ) ∧
        (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ, 1 / 2 < rr u n ∧ rr u n < 3 / 2) ∧
        AnalyticOnNhd ℝ Z (ball (0 : L2T L) ρ) ∧
        (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ,
          Z u n = scalarG L κ (Real.pi / L) u n * (Real.sqrt (rr u n) : ℂ)) ∧
        (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ,
          ‖Z u n‖ ^ 2 = (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) ∧
        (∀ u ∈ ball (0 : L2T L) ρ, ‖Z u‖ = ‖u‖) ∧
        (∀ u ∈ ball (0 : L2T L) ρ,
          ‖fderiv ℝ Z u - Fmap‖ ≤ C * ‖u‖ ^ 2) ∧
        (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ,
          scalarG L κ (Real.pi / L) u n = 0 → Z u n = 0) := by
  have hL : 0 < L := Fact.out
  let r : ℝ := Real.pi / L
  have hr : 0 < r := div_pos Real.pi_pos hL
  have hr2 : r < 2 * Real.pi / L := by dsimp [r]; exact div_lt_div_of_pos_right (by linarith [Real.pi_pos]) hL
  have hs : r < QuantumNLS.ResetFreeResolventLOCAL001.spacing L / 2 := by
    convert hr2 using 1
    unfold QuantumNLS.ResetFreeResolventLOCAL001.spacing
    ring
  obtain ⟨ρg, hρg, Cg, hCg, G, p, e, hGa, hp, hGv, hG0, hF, he, hes, het, hei, heai,
    heven, h5, hGd, hg3, hsums, hkernel⟩ :=
    QuantumNLS.Local006.FinalJ.reset_collective_spectral hL hκ hr hs
  obtain ⟨ρ, hρ, hρg', Cr, hCr, a, b, rr, hpk, hrr, hmass, hbd, hrr0, hrr1, hrr2, hconditional⟩ :=
    QuantumNLS.Local008CapR29a.exact_factor_with_radius_cap ρg hρg hκ hr hr2
  have hsub : ball (0 : L2T L) ρ ⊆ ball 0 ρg := ball_subset_ball hρg'
  have hentry : ∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ,
      scalarG L κ r u n = gcoef L κ * b n u := by
    intro u hu n
    have hm := (hpk n).2.2.2.1 u hu ((hpk n).2.2.1 u hu) (QuantumNLS.LocalSpectral.vec2 1 0)
    rw [QuantumNLS.Local003Analytic.reducedMatrix2_eq] at hm
    have hm' := congrArg (fun w : QuantumNLS.LocalSpectral.E2 => w 1) hm
    have hb : b n u = QuantumNLS.Local003Analytic.Bf L κ (QuantumNLS.LocalSpectral.circleRep u) n r
        (QuantumNLS.LocalSpectral.vec2 1 0) 1 := by
      simpa [QuantumNLS.LocalSpectral.vec2] using hm'.symm
    change gcoef L κ * _ = gcoef L κ * b n u
    rw [hb]
  have hGentry : ∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ, G u n = gcoef L κ * b n u :=
    fun u hu n => (hGv u (hsub hu) n).trans (hentry u hu n)
  have hFmap : (QuantumNLS.Local006.FirstJetF.fourierR L : L2T L →L[ℝ] Seq) = Fmap := by
    ext u
    rfl
  have hGder : ∀ u ∈ ball (0 : L2T L) ρ, ‖fderiv ℝ G u - Fmap‖ ≤ Cg * ‖u‖ ^ 2 := by
    intro u hu
    simpa only [hFmap] using hGd u (hsub hu)
  obtain ⟨Z, C, hC, hZn, hZa, hZd, hnorm⟩ :=
    hconditional G Cg hCg hGentry (hGa.mono hsub) hGder
  have hZscalar : ∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ,
      Z u n = scalarG L κ r u n * (Real.sqrt (rr u n) : ℂ) := by
    intro u hu n
    rw [hZn u hu n, hentry u hu n]
  refine ⟨ρ, hρ, C, hC, rr, Z, hrr, hbd, hZa, hZscalar, ?_, ?_, hZd, ?_⟩
  · intro u hu n
    rw [hZn u hu n, hmass u hu n, norm_mul, mul_pow, Complex.norm_real,
      Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by have := (hbd u hu n).1; linarith)]
  · intro u hu
    have := hnorm u hu
    nlinarith [norm_nonneg (Z u), norm_nonneg u]
  · intro u hu n hz
    rw [hZscalar u hu n, hz, zero_mul]

end QuantumNLS.Local008ModulusR29a
#print axioms QuantumNLS.Local008ModulusR29a.reset_exact_modulus_map
