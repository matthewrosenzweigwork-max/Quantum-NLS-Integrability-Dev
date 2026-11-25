import Mathlib
import QuantumNLS.RB7Plumb

/-!
# R-7B122087 `thm:hierarchy`, A9 physical: the individual action generator `k_n` and `dI_{r+1}(u)[k_n] = 0`

Printed: "For another smooth solution, the charges are invariant under the smooth individual action rotations ...; differentiating gives zero bracket with each action."

With the accepted chart (`RB7Plumb.ChartFacts`): the individual action rotation `θ ↦ T_{n,θ} u` corresponds, by the intertwining `Φ(T_ψ u) = rotate ψ⁻¹ (Φ u)` of R-F5355ABD, to
`θ ↦ Ψ(Φ(u) + (e^{-iθ} - 1) Φ_n(u) e_n)`; its velocity at `θ = 0` is `k_n(u) := (DΦ(u))⁻¹(-i Φ_n(u) e_n)`.

* `genK C u n`: this generator; `genK_spec`: `DΦ(u) k_n = -i Φ_n(u) e_n`;
* `hasDerivAt_actionRot`: `d/dθ|₀ Ψ(Φ(u) + (e^{-iθ} - 1) Φ_n(u) e_n) = k_n(u)` (chain rule through the analytic inverse chart);
* `dI_generator_zero` (the printed "zero bracket"): under the hypotheses of `RB7Plumb.dI_RF535` (`F` `C²` and rotation invariant on `h^S`, smooth point, REG-015 continuity of the chart curve
  `ε ↦ Φ(u + ε k_n)` into `h^{2S}`, `I(u + εk) = F(Φ(u + εk))`), `d/dε I(u + ε k_n)|₀ = 0`: by strong symplecticity
  `2 Re⟨iv, k_n⟩ = 2 Im⟨-iG, -i Φ_n e_n⟩ = 2 Im(conj G_n Φ_n) = 0` (tangency `RB7Rot.grad_tangent`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology
open MeasureTheory

namespace QuantumNLS.RB7

open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight QuantumNLS.PhysicalTensor
open QuantumNLS.D01LocalPrimitive (K)

variable {L κ : ℝ} [Fact (0 < L)]

/-- The generator `k_n(u) = (DΦ(u))⁻¹(-i Φ_n(u) e_n)` of the individual action rotation of the `n`th coordinate. -/
def genK {hκ : 0 < κ} (C : ChartFacts (L := L) hκ) (u : L2T L) (n : ℤ) : L2T L :=
  (Classical.choose (C.iso u)).symm (lp.single 2 n (-Complex.I * C.Φ u n))

theorem genK_spec {hκ : 0 < κ} (C : ChartFacts (L := L) hκ) (u : L2T L) (n : ℤ) :
    fderiv ℝ C.Φ u (genK C u n) = lp.single 2 n (-Complex.I * C.Φ u n) := by
  obtain ⟨he, -⟩ := Classical.choose_spec (C.iso u)
  rw [he.fderiv]
  simp [genK]

theorem hasDerivAt_actionRot {hκ : 0 < κ} (C : ChartFacts (L := L) hκ) (u : L2T L) (n : ℤ) :
    HasDerivAt (fun θ : ℝ => C.Ψ (C.Φ u + (Complex.exp (-(θ : ℂ) * Complex.I) - 1) • lp.single 2 n (C.Φ u n)))
      (genK C u n) 0 := by
  obtain ⟨-, he'⟩ := Classical.choose_spec (C.iso u)
  set e := Classical.choose (C.iso u)
  have hexp : HasDerivAt (fun θ : ℝ => Complex.exp (-(θ : ℂ) * Complex.I) - 1) (-Complex.I) 0 := by
    have h1 : HasDerivAt (fun θ : ℝ => -(θ : ℂ) * Complex.I) (-Complex.I) 0 := by
      have := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).neg.mul_const Complex.I)
      simpa using this
    have h3 := (HasDerivAt.cexp h1)
    simpa using h3.sub_const 1
  have hc : HasDerivAt (fun θ : ℝ => C.Φ u + (Complex.exp (-(θ : ℂ) * Complex.I) - 1) • lp.single 2 n (C.Φ u n))
      (-Complex.I • lp.single 2 n (C.Φ u n)) 0 := by
    simpa using (hexp.smul_const (lp.single 2 n (C.Φ u n))).const_add (C.Φ u)
  have h0 : C.Φ u + (Complex.exp (-((0 : ℝ) : ℂ) * Complex.I) - 1) • lp.single 2 n (C.Φ u n) = C.Φ u := by simp
  have hΨ : HasFDerivAt C.Ψ (e.symm : K →L[ℝ] L2T L)
      (C.Φ u + (Complex.exp (-((0 : ℝ) : ℂ) * Complex.I) - 1) • lp.single 2 n (C.Φ u n)) := by
    rw [h0]; exact he'
  have := hΨ.comp_hasDerivAt (0 : ℝ) hc
  have e2 : (e.symm : K →L[ℝ] L2T L) (-Complex.I • lp.single 2 n (C.Φ u n)) = genK C u n := by
    change e.symm (-Complex.I • lp.single 2 n (C.Φ u n)) = e.symm (lp.single 2 n (-Complex.I * C.Φ u n))
    rw [← lp.single_smul]
    simp
  rwa [e2] at this

theorem dI_generator_zero {hκ : 0 < κ} (C : ChartFacts (L := L) hκ) {S : ℝ} (hS : 0 ≤ S)
    {F : h02 L S → ℝ} (hF : ContDiff ℝ 2 F) (hinv : ∀ (u : ℤ → Circle) z, F (rot u z) = F z)
    (I : L2T L → ℝ) (u : L2T L) (ζ0 : h02 L (2 * S)) (hζ0 : ∀ m, ζ0.val m = C.Φ u m) (n : ℤ)
    (ζ : ℝ → h02 L (2 * S)) (hζ : Continuous ζ)
    (hcoord : ∀ (ε : ℝ) (m : ℤ), (ζ ε).val m = C.Φ (u + ε • genK C u n) m)
    (hI : ∀ ε : ℝ, I (u + ε • genK C u n) = F (iWU (cmp_def002 (L := L) hS) (ζ ε))) :
    HasDerivAt (fun ε : ℝ => I (u + ε • genK C u n)) 0 0 := by
  obtain ⟨v, hv, hder⟩ := dI_RF535 hκ C hS hF hinv I u ζ0 hζ0
  have h1 := hder (genK C u n) ζ hζ hcoord hI
  have hz : (inner ℂ (Complex.I • v) (genK C u n)).re = 0 := by
    rw [re_inner_I_smul']
    have hs := C.symp u v (genK C u n)
    rw [hv, genK_spec] at hs
    have hG : (conj (ζ0.val n) * Gs F (cmp_def002 (L := L) hS) ζ0 n).im = 0 :=
      grad_tangent (hF.differentiable (by norm_num)) hinv (iWU (cmp_def002 (L := L) hS) ζ0) n
    have hin : (inner ℂ (-Complex.I • Gl (cmp_def002 (L := L) hS) hF hinv ζ0)
        (lp.single 2 n (-Complex.I * C.Φ u n))).im = 0 := by
      rw [lp.inner_single_right]
      have e1 : ((-Complex.I • Gl (cmp_def002 (L := L) hS) hF hinv ζ0 : lp (fun _ : ℤ => ℂ) 2) : ℤ → ℂ) n =
          -Complex.I * Gs F (cmp_def002 (L := L) hS) ζ0 n := by
        simp only [lp.coeFn_smul, Gl_val, Pi.smul_apply, smul_eq_mul]
      rw [e1]
      have e2 : inner ℂ (-Complex.I * Gs F (cmp_def002 (L := L) hS) ζ0 n) (-Complex.I * C.Φ u n) =
          conj (conj (ζ0.val n) * Gs F (cmp_def002 (L := L) hS) ζ0 n) := by
        rw [hζ0 n]
        simp only [RCLike.inner_apply, map_mul, map_neg, Complex.conj_conj, Complex.conj_I]
        linear_combination (-(C.Φ u n : ℂ) * conj (Gs F (cmp_def002 (L := L) hS) ζ0 n)) * Complex.I_sq
      rw [e2, Complex.conj_im, hG, neg_zero]
    linarith
  rw [hz] at h1
  simpa using h1

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.genK_spec
#print axioms QuantumNLS.RB7.hasDerivAt_actionRot
#print axioms QuantumNLS.RB7.dI_generator_zero
