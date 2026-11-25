import Mathlib
import QuantumNLS.RB7Reg
import QuantumNLS.RB7Dir
import QuantumNLS.RB7Slice
import QuantumNLS.RB7Gen
import QuantumNLS.RB7Act

/-!
# R-7B122087 `thm:hierarchy`, A9': constancy of all action moduli along an arbitrary smooth Hamiltonian flow line (RB7Const)

Printed: "For another smooth solution, the charges are invariant under the smooth individual action rotations ...; differentiating gives zero bracket with each action.
All action moduli are therefore constant along that solution.  Its coordinate frequencies are the same constants, so each coordinate satisfies the same scalar linear equation."

Let `Ψ'` be ANY `HierarchyFlow.IsHamFlow` of `hamiltonian L κ r` and `u` smooth periodic.  `flowline`: the `L²`-curve `c(s) = [Ψ'_s u]` is differentiable with velocity `v(s) = [∂_s Ψ'_s u]`
(`RB7Slice.hasDerivAt_slice`, joint smoothness is part of `IsHamFlow`), and, because the gradient in `IsSmoothGradient` is `g_s = i v(s)` tested against smooth directions
(`RB7Dir.grad_eq_of_isSmoothGradient`), `DΦ(c(s)) v(s) = -i G` with `G` the `ℓ²` coordinate gradient of `F_r` at `Φ(c(s))` (`RB7Dir.dir_deriv`, `RB7Plumb.dI_RF535`).
`re_inner_I_genK`: the zero bracket `Re⟨i v, k_n⟩ = 0` for the individual action generator `k_n` (strong symplecticity + tangency, the computation of `RB7Gen.dI_generator_zero`), and by
`RB7Act.action_const` every modulus `|Φ_n(c(s))|²` is constant.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology NNReal ContDiff
open MeasureTheory

namespace QuantumNLS.RB7

open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight QuantumNLS.PhysicalTensor QuantumNLS.Fourier
open QuantumNLS.Reg015Setting QuantumNLS.ClassicalCharges QuantumNLS.SmoothScalarMomentsPhysical
open QuantumNLS.D01LocalPrimitive (K)
open QuantumNLS.HierarchyFlow

variable {L κ : ℝ} [Fact (0 < L)] {hκ : 0 < κ}

theorem smoothL2_congr {f f' : ℝ → ℂ} (h : f = f') (hf : SmoothPeriodic L f) (hf' : SmoothPeriodic L f') :
    smoothL2 hf = smoothL2 hf' := by subst h; rfl

/-- **The zero bracket** `Re⟨i v, k_n⟩ = 0` (strong symplecticity and tangency; the algebra of `RB7Gen.dI_generator_zero`). -/
theorem re_inner_I_genK {hκ : 0 < κ} (C : ChartFacts (L := L) hκ) {S : ℝ} (hS : 0 ≤ S)
    {F : h02 L S → ℝ} (hF : ContDiff ℝ 2 F) (hinv : ∀ (u : ℤ → Circle) z, F (rot u z) = F z)
    (u : L2T L) (ζ0 : h02 L (2 * S)) (hζ0 : ∀ m, ζ0.val m = C.Φ u m) (n : ℤ) (v : L2T L)
    (hv : fderiv ℝ C.Φ u v = -Complex.I • Gl (cmp_def002 (L := L) hS) hF hinv ζ0) :
    (inner ℂ (Complex.I • v) (genK C u n)).re = 0 := by
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

/-- **The flow line** of an arbitrary smooth Hamiltonian flow `Ψ'` of `Re I_{r+1}`. -/
theorem flowline (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ)
    {Ψ' : ℝ → (ℝ → ℂ) → (ℝ → ℂ)} (hΨ : IsHamFlow L (hamiltonian L κ r) Ψ')
    {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    ∃ (c v : ℝ → L2T L),
      (∀ s (hs : SmoothPeriodic L (Ψ' s u)), c s = smoothL2 hs) ∧
      (∀ s, HasDerivAt c (v s) s) ∧
      (∀ s (hs : SmoothPeriodic L (Ψ' s u)),
        fderiv ℝ C.Φ (c s) (v s) = -Complex.I • Gcoord hR C r hs) ∧
      (∀ s (hs : SmoothPeriodic L (Ψ' s u)) (n : ℤ),
        (inner ℂ (Complex.I • v s) (genK C (c s) n)).re = 0) := by
  obtain ⟨h0, hG, hs⟩ := hΨ u hu
  let G : ℝ × ℝ → ℂ := fun p => Ψ' p.1 u p.2
  have hper : ∀ τ x, G (τ, x + L) = G (τ, x) := fun τ x => ((hs τ).1).periodic x
  let c : ℝ → L2T L := fun s => smoothL2 (slice_smooth hG hper s)
  let v : ℝ → L2T L := fun s => smoothL2 (dslice_smooth hG hper s)
  have hc : ∀ s, HasDerivAt c (v s) s := fun s => hasDerivAt_slice hG hper s
  have hcs : ∀ s (hs' : SmoothPeriodic L (Ψ' s u)), c s = smoothL2 hs' := fun s hs' => rfl
  -- the velocity is `v_dir`
  have key : ∀ s (hs' : SmoothPeriodic L (Ψ' s u)), ∃ vd : L2T L,
      v s = vd ∧ fderiv ℝ C.Φ (c s) vd = -Complex.I • Gcoord hR C r hs' := by
    intro s hs'
    obtain ⟨vd, hvd, hder⟩ := dir_deriv hR C r hs'
    obtain ⟨g, hg, hgd⟩ := (hs s).2
    have hdg : dslice G s = fun x => -Complex.I * g x := by
      funext x
      exact (hasDerivAt_partial (hG.of_le (by simp)) s x).unique (hgd x)
    have hI := grad_eq_of_isSmoothGradient hR C r hs' hder hg
    refine ⟨vd, ?_, ?_⟩
    · have h1 : v s = smoothL2 (smooth_const_mul hg.1 (-Complex.I)) :=
        smoothL2_congr hdg _ _
      rw [h1, smoothL2_const_mul hg.1 (-Complex.I), hI, smul_smul]
      simp
    · exact hvd
  refine ⟨c, v, hcs, hc, fun s hs' => ?_, fun s hs' n => ?_⟩
  · obtain ⟨vd, h1, h2⟩ := key s hs'
    rw [h1]; exact h2
  · obtain ⟨vd, h1, h2⟩ := key s hs'
    rw [h1]
    exact re_inner_I_genK C (NNReal.coe_nonneg (SOf r)) (Fd_contDiff hR C r) (Fd_inv hR C r) (c s)
      (zeta0 hR C r hs') (fun m => rfl) n vd h2

/-- **All action moduli are constant along an arbitrary smooth Hamiltonian flow line.** -/
theorem moduli_const (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ)
    {Ψ' : ℝ → (ℝ → ℂ) → (ℝ → ℂ)} (hΨ : IsHamFlow L (hamiltonian L κ r) Ψ')
    {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (n : ℤ) (s s' : ℝ)
    (hs : SmoothPeriodic L (Ψ' s u)) (hs' : SmoothPeriodic L (Ψ' s' u)) :
    ‖(C.Φ (smoothL2 hs) : ℤ → ℂ) n‖ ^ 2 = ‖(C.Φ (smoothL2 hs') : ℤ → ℂ) n‖ ^ 2 := by
  obtain ⟨c, v, hcs, hc, hD, hbr⟩ := flowline hR C r hΨ hu
  have hΦ : ∀ s, HasFDerivAt C.Φ (fderiv ℝ C.Φ (c s)) (c s) :=
    fun s => ((C.ana_Φ (c s)).differentiableAt).hasFDerivAt
  have hsm : ∀ s, SmoothPeriodic L (Ψ' s u) := fun s => ((hΨ u hu).2.2 s).1
  have := action_const C.Φ n c v (fun s => fderiv ℝ C.Φ (c s)) hc hΦ (fun s a b => C.symp (c s) a b)
    (fun s => genK C (c s) n) (fun s => genK_spec C (c s) n) (fun s => hbr s (hsm s) n) s s'
  rw [← hcs s hs, ← hcs s' hs']
  exact this

/-- The derivative of every coordinate along the flow line is `-i` times the coordinate gradient. -/
theorem coord_hasDerivAt (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ)
    {Ψ' : ℝ → (ℝ → ℂ) → (ℝ → ℂ)} (hΨ : IsHamFlow L (hamiltonian L κ r) Ψ')
    {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    ∃ c : ℝ → L2T L, (∀ s (hs : SmoothPeriodic L (Ψ' s u)), c s = smoothL2 hs) ∧
      ∀ (s : ℝ) (hs : SmoothPeriodic L (Ψ' s u)) (j : ℤ),
        HasDerivAt (fun t : ℝ => (C.Φ (c t) : ℤ → ℂ) j) (-Complex.I * (Gcoord hR C r hs : ℤ → ℂ) j) s := by
  obtain ⟨c, v, hcs, hc, hD, -⟩ := flowline hR C r hΨ hu
  refine ⟨c, hcs, fun s hs j => ?_⟩
  have hΦ : HasFDerivAt C.Φ (fderiv ℝ C.Φ (c s)) (c s) :=
    ((C.ana_Φ (c s)).differentiableAt).hasFDerivAt
  have h1 := hΦ.comp_hasDerivAt s (hc s)
  have h2 := hasDerivAt_coord _ _ s j h1
  have e : (fderiv ℝ C.Φ (c s) (v s) : ℤ → ℂ) j = -Complex.I * (Gcoord hR C r hs : ℤ → ℂ) j := by
    rw [hD s hs]
    simp only [neg_smul, lp.coeFn_neg, lp.coeFn_smul, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, neg_mul]
  rw [e] at h2
  exact h2

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.re_inner_I_genK
#print axioms QuantumNLS.RB7.flowline
#print axioms QuantumNLS.RB7.moduli_const
#print axioms QuantumNLS.RB7.coord_hasDerivAt
