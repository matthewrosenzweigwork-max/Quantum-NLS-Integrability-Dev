import Mathlib
import QuantumNLS.RB7Chart

/-!
# R-7B122087 `thm:hierarchy`: constancy of the actions along a smooth solution (abstract part, own TODO A9) and the `Z^new` conversion (statement fidelity)

Printed: "For another smooth solution, the charges are invariant under the smooth individual action rotations, as follows from the scalar measure identity;
differentiating gives zero bracket with each action.  All action moduli are therefore constant along that solution."

* `action_const`: `u : ℝ → H` differentiable with velocity `v`, `Φ : H → ℓ²` with symplectic derivative `D_s`, `k_s ∈ H` the generator of the individual rotation at `n`
  (`D_s k_s = -i Φ_n(u_s) e_n`), and the vanishing bracket `Re⟨i v_s, k_s⟩ = 0` (= `dI_{r+1}(u_s)[k_s]` for a solution with `v = -i∇I_{r+1}`, which is `0` by the
  rotation invariance of `I_{r+1}` along `θ ↦ T_{n,θ} u`, i.e. `RB7Moment` + `RB7Scale.inv_of_chart`): then `|Φ_n(u_s)|²` is constant in `s`.
* Fidelity of the printed conversion `Z^new_j = √2 Φ_{-j}`: `reflect`, `grad_scaleReflect`, `printed_freq_eq`.  With the printed convention
  `dF[η e_j] = Re(conj(w_j) η)` (so `w = 2 ∇`, our `grad`), the printed frequency `ω_j = Re(conj(Z_j) w_j)/|Z_j|²` of `F_Z = F_Φ ∘ (Z ↦ Φ)` equals our frequency
  `Ω_{-j} = Re(conj(Φ_{-j}) ∇_{-j}F_Φ)/|Φ_{-j}|²` of the `Φ`-coordinates at the reflected index: no extra factor of two and no reflection sign.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate Topology ENNReal
open Filter Set

namespace QuantumNLS.RB7

open QuantumNLS.Sobolev
open QuantumNLS.Sobolev.PosWeight

section Act

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem hasDerivAt_coord (z : ℝ → lp (fun _ : ℤ => ℂ) 2) (z' : lp (fun _ : ℤ => ℂ) 2) (s : ℝ) (n : ℤ)
    (h : HasDerivAt z z' s) : HasDerivAt (fun s => (z s : ℤ → ℂ) n) (z' n) s :=
  (lp.evalCLM (E := fun _ : ℤ => ℂ) ℝ (2 : ℝ≥0∞) n).hasFDerivAt.comp_hasDerivAt s h

/-- `d/ds |a(s)|² = 2 Re(conj a a')` for a complex curve. -/
theorem hasDerivAt_normSq (a : ℝ → ℂ) (a' : ℂ) (s : ℝ) (h : HasDerivAt a a' s) :
    HasDerivAt (fun s => ‖a s‖ ^ 2) (2 * (conj (a s) * a').re) s := by
  have e : (fun s => ‖a s‖ ^ 2) = fun s => (conj (a s) * a s).re := by
    funext s; rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [e]
  have h1 : HasDerivAt (fun s => conj (a s) * a s) (conj a' * a s + conj (a s) * a') s := by
    have hc : HasDerivAt (fun s => conj (a s)) (conj a') s := h.star
    exact hc.mul h
  have h2 : HasDerivAt (fun s => (conj (a s) * a s).re) ((conj a' * a s + conj (a s) * a').re) s :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt s h1
  convert h2 using 1
  have : (conj a' * a s).re = (conj (a s) * a').re := by
    have := Complex.conj_re (conj (a s) * a')
    rw [← this, map_mul, Complex.conj_conj, mul_comm]
  rw [Complex.add_re, this]; ring

theorem action_const (Φ : H → lp (fun _ : ℤ => ℂ) 2) (n : ℤ) (u v : ℝ → H) (D : ℝ → H →L[ℝ] lp (fun _ : ℤ => ℂ) 2)
    (hu : ∀ s, HasDerivAt u (v s) s) (hΦ : ∀ s, HasFDerivAt Φ (D s) (u s))
    (symp : ∀ s a b, 2 * (inner ℂ (D s a) (D s b)).im = 2 * (inner ℂ a b).im)
    (k : ℝ → H) (hk : ∀ s, D s (k s) = lp.single 2 n (-Complex.I * (Φ (u s) : ℤ → ℂ) n))
    (hbr : ∀ s, (inner ℂ (Complex.I • v s) (k s)).re = 0) (s s' : ℝ) :
    ‖(Φ (u s) : ℤ → ℂ) n‖ ^ 2 = ‖(Φ (u s') : ℤ → ℂ) n‖ ^ 2 := by
  have hder : ∀ s, HasDerivAt (fun s => ‖(Φ (u s) : ℤ → ℂ) n‖ ^ 2) 0 s := by
    intro s
    have h1 : HasDerivAt (fun s => Φ (u s)) (D s (v s)) s := (hΦ s).comp_hasDerivAt s (hu s)
    have h2 := hasDerivAt_coord _ _ s n h1
    have h3 := hasDerivAt_normSq _ _ s h2
    convert h3 using 1
    -- `Re(conj Φ_n (D v)_n) = Im⟨D k, D v⟩ = Im⟨k, v⟩ = -Re⟨i v, k⟩ = 0`
    have e1 : (inner ℂ (D s (k s)) (D s (v s))).im = (conj ((Φ (u s) : ℤ → ℂ) n) * (D s (v s)) n).re := by
      rw [hk s, lp.inner_single_left]
      simp [Complex.mul_re, Complex.mul_im]
      ring
    have e2 := symp s (k s) (v s)
    have e3 : (inner ℂ (k s) (v s)).im = -(inner ℂ (v s) (k s)).im := by
      rw [← inner_conj_symm (k s) (v s), Complex.conj_im]
    have e4 := re_inner_I_smul' (v s) (k s)
    have := hbr s
    have e5 : (inner ℂ (Complex.I • v s) (k s)).re = (inner ℂ (v s) (k s)).im := e4
    nlinarith
  exact is_const_of_deriv_eq_zero (fun s => (hder s).differentiableAt) (fun s => (hder s).deriv) s s'

end Act


section Fidelity

variable {W : PosWeight}

/-- The index reflection `z ↦ (z_{-j})_j` for a reflection-symmetric weight (the `Z^new_j = √2 Φ_{-j}` relabelling). -/
def reflectL (hW : ∀ j, W.w (-j) = W.w j) : WSeq W →ₗ[ℝ] WSeq W where
  toFun z := WSeq.mk W (fun j => z.val (-j)) (by
    have := (Equiv.neg ℤ).summable_iff.2 z.summable
    refine this.congr (fun j => ?_)
    simp [hW j])
  map_add' x y := WSeq.ext (funext fun j => rfl)
  map_smul' c x := WSeq.ext (funext fun j => by simp [Complex.real_smul]; rfl)

@[simp] theorem reflectL_val (hW : ∀ j, W.w (-j) = W.w j) (z : WSeq W) (j : ℤ) :
    (reflectL hW z).val j = z.val (-j) := rfl

theorem norm_reflectL (hW : ∀ j, W.w (-j) = W.w j) (z : WSeq W) : ‖reflectL hW z‖ = ‖z‖ := by
  have h : ‖reflectL hW z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [norm_sq_eq_tsum, norm_sq_eq_tsum]
    simp only [reflectL_val]
    rw [← (Equiv.neg ℤ).tsum_eq (fun j => W.w j * ‖z.val j‖ ^ 2)]
    refine tsum_congr (fun j => ?_)
    simp [hW j]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

def reflect (hW : ∀ j, W.w (-j) = W.w j) : WSeq W →L[ℝ] WSeq W :=
  (reflectL hW).mkContinuous 1 (fun z => by rw [norm_reflectL hW z]; simp)

@[simp] theorem reflect_val (hW : ∀ j, W.w (-j) = W.w j) (z : WSeq W) (j : ℤ) :
    (reflect hW z).val j = z.val (-j) := rfl

theorem reflect_ev (hW : ∀ j, W.w (-j) = W.w j) (c : ℂ) (j : ℤ) :
    reflect hW (c • ev W j) = c • ev W (-j) := by
  refine WSeq.ext (funext fun n => ?_)
  simp only [reflect_val, smul_ev_val]
  by_cases h : -n = j
  · have : n = -j := by omega
    simp [h, this]
  · have : n ≠ -j := fun h' => h (by omega)
    simp [h, this]

/-- Gradient of `ℓ ∘ (a • reflect)` (`a` real): `∇_j = a ∇_{-j}`. -/
theorem grad_scaleReflect (hW : ∀ j, W.w (-j) = W.w j) (ℓ : WSeq W →L[ℝ] ℝ) (a : ℝ) (j : ℤ) :
    grad (ℓ.comp (a • reflect hW)) j = (a : ℂ) * grad ℓ (-j) := by
  apply grad_unique
  intro c
  have h1 : (ℓ.comp (a • reflect hW)) (c • ev W j) = ℓ (((a : ℂ) * c) • ev W (-j)) := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, reflect_ev]
    congr 1
    rw [← smul_assoc, Complex.real_smul]
  rw [h1, map_smul_ev_eq]
  congr 1
  have : conj ((a : ℂ) * grad ℓ (-j)) * c = conj (grad ℓ (-j)) * ((a : ℂ) * c) := by
    rw [map_mul, Complex.conj_ofReal]; ring
  rw [this]

/-- **Fidelity of the printed `Z^new` conversion.**  With `Z_j = √2 Φ_{-j}` (so `F_Z = F_Φ ∘ (2^{-1/2} • reflect)`) and the printed gradient convention
`dF[η e_j] = Re(conj(w_j) η)` (`w = 2 ∇`), the printed frequency `Re(conj(Z_j) w^Z_j)/|Z_j|²` equals the `Φ`-coordinate frequency
`Re(conj(Φ_{-j}) ∇_{-j}F_Φ)/|Φ_{-j}|²` at the reflected index. -/
theorem printed_freq_eq (hW : ∀ j, W.w (-j) = W.w j) (ℓ : WSeq W →L[ℝ] ℝ) (φ : ℂ) (j : ℤ) (hφ : φ ≠ 0) :
    (conj ((Real.sqrt 2 : ℝ) * φ) * (2 * grad (ℓ.comp ((Real.sqrt 2)⁻¹ • reflect hW)) j)).re /
        ‖(Real.sqrt 2 : ℝ) * φ‖ ^ 2 = (conj φ * grad ℓ (-j)).re / ‖φ‖ ^ 2 := by
  rw [grad_scaleReflect]
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hn : ‖((Real.sqrt 2 : ℝ) : ℂ) * φ‖ ^ 2 = 2 * ‖φ‖ ^ 2 := by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h2, sq]
    rw [hs]
  have hp : (0 : ℝ) < ‖φ‖ := norm_pos_iff.2 hφ
  rw [hn]
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h2.ne'
  have e : conj (((Real.sqrt 2 : ℝ) : ℂ) * φ) * (2 * ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * grad ℓ (-j))) =
      ((2 : ℝ) : ℂ) * (conj φ * grad ℓ (-j)) := by
    rw [map_mul, Complex.conj_ofReal, Complex.ofReal_inv]
    push_cast
    field_simp
  rw [e, Complex.re_ofReal_mul]
  field_simp

end Fidelity

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.action_const
#print axioms QuantumNLS.RB7.grad_scaleReflect
#print axioms QuantumNLS.RB7.printed_freq_eq
