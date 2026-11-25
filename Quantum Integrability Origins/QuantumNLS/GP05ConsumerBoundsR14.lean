import QuantumNLS.GP05CauchyMajorantsR14
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

/-! GP-05 consumer form for values:prop:riccati and Q07Buniformcuts.
The value weight may be a negative spectral power, exponential remainder or
summable transfer-kernel majorant. It is retained by every fixed derivative on
a single smaller Banach neighborhood. Independent fields are coordinates of E. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Metric
namespace QuantumNLS.GP05ConsumerBoundsR14
open GP05CauchyMajorantsR14
variable {I E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Uniform full multilinear derivative bounds on the smaller neighborhood.
The weight and the neighborhood are independent of the parameter and order. -/
theorem uniform_derivatives (bridge : BanachHolomorphicBridge E F)
    {f : I → E → F} {a : E} {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (weight : I → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (hf : ∀ i, DifferentiableOn ℂ (f i) (ball a R))
    (hb : ∀ i z, z ∈ ball a R → ‖f i z‖ ≤ C*weight i) (n : ℕ) :
    ∀ i z, z ∈ ball a (R/2) →
      ‖iteratedFDeriv ℂ n (f i) z‖ ≤ ((4*(n+1 : ℕ)/R)^n*C)*weight i := by
  intro i z hz
  have hsub : ball z (R/2) ⊆ ball a R := by
    intro y hy
    have h1 : dist y z < R/2 := hy
    have h2 : dist z a < R/2 := hz
    have ht := dist_triangle y z a
    change dist y a < R
    linarith
  have hfa := (bridge _ _ isOpen_ball (hf i)).mono hsub
  have hn : (0 : ℝ) < (n+1 : ℕ) := by positivity
  have hd : 0 < (R/2)/(n+1 : ℕ) := by positivity
  have he : (n+1 : ℕ)*((R/2)/(n+1 : ℕ)) = R/2 := by field_simp
  have h := norm_iterated_steps n hd (mul_nonneg hC (hw i))
    (he.symm ▸ hfa) (he.symm ▸ (fun y hy => hb i y (hsub hy)))
  convert h using 1
  have he' : 2/((R/2)/(n+1 : ℕ)) = 4*(n+1 : ℕ)/R := by field_simp; ring
  rw [he']
  ring

section Physical
variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

/-- The same norm estimates are physical real Hilbert operator estimates after
restriction of scalars, including all mixed directions of independent fields. -/
theorem uniform_real_derivatives (bridge : BanachHolomorphicBridge E F)
    {f : I → E → F} {a : E} {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (weight : I → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (hf : ∀ i, DifferentiableOn ℂ (f i) (ball a R))
    (hb : ∀ i z, z ∈ ball a R → ‖f i z‖ ≤ C*weight i) (n : ℕ) :
    ∀ i z, z ∈ ball a (R/2) →
      ‖iteratedFDeriv ℝ n (f i) z‖ ≤ ((4*(n+1 : ℕ)/R)^n*C)*weight i := by
  intro i z hz
  have hzR : z ∈ ball a R := (ball_subset_ball (by linarith : R/2 ≤ R)) hz
  have hfa := bridge _ _ isOpen_ball (hf i) z hzR
  have hc : ContDiffAt ℂ n (f i) z := hfa.contDiffAt
  rw [← hc.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  simp only [Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars]
  exact uniform_derivatives bridge hR hC weight hw hf hb n i z hz
end Physical
omit [CompleteSpace F] in
/-- The same summable majorant works for every parameter and every increment
in a fixed closed smaller ball. This is a full target-norm statement. -/
theorem uniform_geometric_majorant {p : I → FormalMultilinearSeries ℂ E F}
    {R C s : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hs : 0 ≤ s)
    (hsR : s < commonRadius R)
    (hp : ∀ i n, ‖p i n‖ ≤ C*(2*Real.exp 1/R)^n) :
    Summable (fun n : ℕ => C*(2*Real.exp 1/R*s)^n) ∧
      ∀ i z, ‖z‖ ≤ s → ∀ n,
        ‖p i n (fun _ => z)‖ ≤ C*(2*Real.exp 1/R*s)^n := by
  have hq0 : 0 ≤ 2*Real.exp 1/R*s := by positivity
  have hq : 2*Real.exp 1/R*s < 1 := by
    have he : 0 < 2*Real.exp (1 : ℝ) := by positivity
    unfold commonRadius at hsR
    have hh := (lt_div_iff₀ he).mp hsR
    rw [div_mul_eq_mul_div]
    apply (div_lt_one hR).mpr
    simpa [div_mul_eq_mul_div, mul_comm, mul_left_comm, mul_assoc] using hh
  refine ⟨(summable_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hq0])).mul_left C, ?_⟩
  intro i z hz n
  calc
    _ ≤ ‖p i n‖*(∏ _ : Fin n, ‖z‖) := (p i n).le_opNorm _
    _ = ‖p i n‖*‖z‖^n := by simp
    _ ≤ (C*(2*Real.exp 1/R)^n)*s^n := by
      apply mul_le_mul (hp i n) (pow_le_pow_left₀ (norm_nonneg _) hz n)
        (by positivity) (by positivity)
    _ = C*(2*Real.exp 1/R*s)^n := by rw [mul_pow]; ring

/-- Uniform norm convergence follows from the constructed majorant. -/
theorem uniform_series_convergence {p : I → FormalMultilinearSeries ℂ E F}
    {R C s : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hs : 0 ≤ s)
    (hsR : s < commonRadius R)
    (hp : ∀ i n, ‖p i n‖ ≤ C*(2*Real.exp 1/R)^n) :
    TendstoUniformlyOn
      (fun N (v : I × E) => ∑ n ∈ Finset.range N, p v.1 n (fun _ => v.2))
      (fun v => ∑' n, p v.1 n (fun _ => v.2)) Filter.atTop
      {v : I × E | ‖v.2‖ ≤ s} := by
  have h := uniform_geometric_majorant hR hC hs hsR hp
  apply tendstoUniformlyOn_tsum_nat h.1
  intro n v hv
  exact h.2 v.1 v.2 hv n

end QuantumNLS.GP05ConsumerBoundsR14
