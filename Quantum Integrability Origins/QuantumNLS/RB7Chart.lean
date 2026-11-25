import Mathlib
import QuantumNLS.RB7Unif

/-!
# R-7B122087 `thm:hierarchy`, gradient identification through the strongly symplectic chart (abstract part; own TODO A8)

Printed: "Full Hilbert symplecticity, tested against smooth variations, identifies its derivative with `-i ∇I_{r+1}(u(t))`.  The test gradients and vectors are
smooth and the sums converge, so no unbounded Hamiltonian is differentiated at rough data."

* `memℓ2_of_summable`, `pair_eq_re_inner`: the sequence pairing `Σ Re(conj a_j b_j)` of `RB7Unif` is `Re ⟪a, b⟫` in `ℓ²`.
* `chart_dI`: `H` a complex inner product space (physical `L²`), `Φ : H → ℓ²` with real Fréchet derivative `D` at `u` that is strongly symplectic
  (`2 Im⟨Da,Db⟩ = 2 Im⟨a,b⟩`), `F` `C²` and rotation invariant on `h(W)`, `I(u + εh) = F(Φ-coordinates of u+εh)` along the direction `h`, where the
  coordinate curve `ε ↦ Φ(u+εh)` is continuous into the smoother space `h(U)` (`W² ≤ U`: the REG-015 homeomorphism, applied at all orders, supplies this
  for smooth `h`), and `v ∈ H` with `D v = -i G`, `G` the coordinate gradient of `F` at `Φ u`.  Then `d/dε I(u+εh)|₀ = 2 Re⟨i v, h⟩`, that is,
  `v = -i ∇I(u)` tested against `h` (DEF-015 convention).  No Lipschitz bound of `Φ` between Sobolev scales is used: only the
  `ℓ²` derivative `D h`, continuity into `h(U)` (REG-015) and the compact-uniform Hessian estimate of `RB7Unif`.
* `chart_velocity`: chain rule: if `Ψ` has derivative `D⁻¹` at `z(t)` and `z' = D v` then `(Ψ∘z)' = v`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric

namespace QuantumNLS.RB7

open QuantumNLS.Sobolev
open QuantumNLS.Sobolev.PosWeight

/-- A sequence with summable squared moduli is an element of `ℓ²`. -/
theorem memℓ2_of_summable (a : ℤ → ℂ) (h : Summable fun j => ‖a j‖ ^ 2) :
    Memℓp (E := fun _ : ℤ => ℂ) a (2 : ℝ≥0∞) := by
  refine memℓp_gen ?_
  simpa using h

theorem pair_eq_re_inner (a b : lp (fun _ : ℤ => ℂ) 2) :
    pair (a : ℤ → ℂ) (b : ℤ → ℂ) = (inner ℂ a b).re := by
  have h := (lp.hasSum_inner (𝕜 := ℂ) a b)
  have h2 : HasSum (fun j => (inner ℂ (a j) (b j)).re) (inner ℂ a b).re :=
    Complex.reCLM.hasSum h
  unfold pair
  refine (h2.tsum_eq).symm ▸ ?_
  congr 1
  funext j
  simp [mul_comm]

theorem re_inner_I_smul' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x y : E) :
    (inner ℂ (Complex.I • x) y).re = (inner ℂ x y).im := by
  rw [inner_smul_left]; simp

theorem chart_dI {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {W U : PosWeight}
    (c : Cmp W U) {F : WSeq W → ℝ} (hF : ContDiff ℝ 2 F) (hinv : ∀ u z, F (rot u z) = F z)
    (Φ : H → lp (fun _ : ℤ => ℂ) 2) (I : H → ℝ) (u h : H) (D : H →L[ℝ] lp (fun _ : ℤ => ℂ) 2)
    (hΦ : HasFDerivAt Φ D u)
    (symp : ∀ a b : H, 2 * (inner ℂ (D a) (D b)).im = 2 * (inner ℂ a b).im)
    (ζ : ℝ → WSeq U) (hζ : Continuous ζ)
    (hζΦ : ∀ (ε : ℝ) (n : ℤ), (ζ ε).val n = (Φ (u + ε • h) : ℤ → ℂ) n)
    (hI : ∀ ε : ℝ, I (u + ε • h) = F (iWU c (ζ ε)))
    (G : lp (fun _ : ℤ => ℂ) 2) (hG : (G : ℤ → ℂ) = Gs F c (ζ 0))
    (v : H) (hv : D v = -Complex.I • G) :
    HasDerivAt (fun ε : ℝ => I (u + ε • h)) (2 * (inner ℂ (Complex.I • v) h).re) 0 := by
  -- the coordinate curve in `ℓ²`
  have hline : HasDerivAt (fun ε : ℝ => u + ε • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add u
  have hΦ' : HasFDerivAt Φ D (u + (0 : ℝ) • h) := by simpa using hΦ
  have hcurve : HasDerivAt (fun ε : ℝ => Φ (u + ε • h)) (D h) 0 := hΦ'.comp_hasDerivAt 0 hline
  have hslope := hasDerivAt_iff_tendsto_slope_zero.1 hcurve
  have hq : Tendsto (fun ε : ℝ => ∑' j, ‖(ζ ε - ζ 0).val j / (ε : ℂ) - (D h : ℤ → ℂ) j‖ ^ 2)
      (𝓝[≠] 0) (𝓝 0) := by
    have h0 : Tendsto (fun ε : ℝ => ‖ε⁻¹ • (Φ (u + (0 + ε) • h) - Φ (u + (0 : ℝ) • h)) - D h‖ ^ 2)
        (𝓝[≠] 0) (𝓝 0) := by
      have := (hslope.sub_const (D h)).norm
      simpa [zero_add] using this.pow 2
    refine h0.congr (fun ε => ?_)
    rw [lp_norm_sq_tsum]
    refine tsum_congr (fun j => ?_)
    have e1 : (ζ ε - ζ 0).val j = (Φ (u + ε • h) : ℤ → ℂ) j - (Φ (u + (0 : ℝ) • h) : ℤ → ℂ) j := by
      show (ζ ε).val j - (ζ 0).val j = _
      rw [hζΦ, hζΦ]
    simp only [zero_add, e1]
    have e2 : ((ε⁻¹ • (Φ (u + ε • h) - Φ (u + (0 : ℝ) • h)) - D h : lp (fun _ : ℤ => ℂ) 2) : ℤ → ℂ) j =
        (ε : ℂ)⁻¹ * ((Φ (u + ε • h) : ℤ → ℂ) j - (Φ (u + (0 : ℝ) • h) : ℤ → ℂ) j) - (D h : ℤ → ℂ) j := by
      simp only [lp.coeFn_sub, lp.coeFn_smul, zero_smul, add_zero, Pi.sub_apply, Pi.smul_apply, Complex.real_smul, Complex.ofReal_inv]
    rw [e2, div_eq_inv_mul]
  have hD := hasDerivAt_curve c hF hinv ζ hζ (D h : ℤ → ℂ)
    (by simpa [lp_norm_sq_tsum] using (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by simp) (D h)).summable |>.congr (fun j => by simp)) hq
  have hfun : (fun ε : ℝ => I (u + ε • h)) = fun ε => F (iWU c (ζ ε)) := funext hI
  rw [hfun]
  have hGeq : G = Complex.I • D v := by
    rw [hv, smul_smul]
    simp
  have key : pair (Gs F c (ζ 0)) (D h : ℤ → ℂ) = (inner ℂ (Complex.I • v) h).re := by
    rw [← hG, pair_eq_re_inner, hGeq, re_inner_I_smul', re_inner_I_smul' v h]
    have := symp v h
    linarith
  rw [key] at hD
  exact hD

theorem chart_velocity {H K : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup K] [NormedSpace ℝ K]
    (Ψ : K → H) (z : ℝ → K) (t : ℝ) (e : H ≃L[ℝ] K) (hΨ : HasFDerivAt Ψ (e.symm : K →L[ℝ] H) (z t))
    (z' : K) (hz : HasDerivAt z z' t) (v : H) (hv : e v = z') : HasDerivAt (fun s => Ψ (z s)) v t := by
  have := hΨ.comp_hasDerivAt t hz
  have e2 : (e.symm : K →L[ℝ] H) z' = v := by rw [← hv]; simp
  rwa [e2] at this

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.chart_dI
#print axioms QuantumNLS.RB7.chart_velocity
