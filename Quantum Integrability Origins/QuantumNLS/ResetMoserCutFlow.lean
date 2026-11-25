import QuantumNLS.ResetMoserCutField
import QuantumNLS.ResetMoserExist
import QuantumNLS.ResetMoserFlowGlobal
import QuantumNLS.ResetMoserBounds

/-!
# `thm:reset-moser` (LOCAL-017), item 5b: the complete flow of `Fc`, conservation of every `q_n`, and the Moser flow `S_t`

Source: `symplectic_correction.tex`, "The deformation and its invariant ball": "Along it every `q_n` is constant.  Summing these exact equalities gives conservation
of `‖z‖²`; no differentiation of an infinite sum is needed.  A trajectory starting in `B_r` therefore stays in its initial smaller closed ball.  ... so the solution extends
through `0 ≤ t ≤ 1`. ... Denote the flow from zero to `t` by `S_t`."

* `Fl`: the complete flow of `Fc` (Picard-Lindelof, `ResetMoserExist.exists_flow`), a `FlowOn Fc Fl univ`, so the frozen `ResetMoserFlowGlobal` theorems apply
  (`diffAt`, `group_law`, `variational`);
* `Fl_snd`: `(Fl s p).2 = p.2 + s`;
* `q_Fl` / `norm_Fl`: `q_n` and `‖·‖` are conserved on the first coordinate (from `dq_Yf_zero`, `tsum_norm_sq`);
* `Sfl t z = (Fl t (z, 0)).1`, `Sfl_deriv`: for `‖z‖ ≤ R0/4`, `∂ₜ S_t z = Y_{sig t}(S_t z)`, and `Fl t (z, 0) = (S_t z, t)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal NNReal
open Filter Set Metric

namespace QuantumNLS.ResetMoser

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.ResetMoserClamp

namespace MoserData

variable {S : Hyp} (MD : MoserData S)

theorem exists_Fl : ∃ Φ : ℝ → K × ℝ → K × ℝ, (∀ v, Φ 0 v = v) ∧
    ∀ v t, HasDerivAt (fun s => Φ s v) (MD.Fc (Φ t v)) t := by
  obtain ⟨Kc, hK⟩ := MD.Fc_lipschitz
  exact ResetMoserExist.exists_flow hK MD.Fc_norm_le

/-- The complete flow of the cut-off field. -/
def Fl : ℝ → K × ℝ → K × ℝ := MD.exists_Fl.choose

theorem Fl_zero (v : K × ℝ) : MD.Fl 0 v = v := MD.exists_Fl.choose_spec.1 v

theorem Fl_deriv (v : K × ℝ) (t : ℝ) : HasDerivAt (fun s => MD.Fl s v) (MD.Fc (MD.Fl t v)) t :=
  MD.exists_Fl.choose_spec.2 v t

theorem Fl_flowOn : ResetMoserFlow.FlowOn MD.Fc MD.Fl univ where
  isOpen := isOpen_univ
  cd := MD.Fc_contDiff.contDiffOn
  deriv := fun v _ t => MD.Fl_deriv v t
  mem := fun _ _ _ => trivial
  zero := fun v _ => MD.Fl_zero v

theorem Fl_snd (p : K × ℝ) (s : ℝ) : (MD.Fl s p).2 = p.2 + s := by
  have hd : ∀ x : ℝ, HasDerivAt (fun r => (MD.Fl r p).2 - r) 0 x := by
    intro x
    have h1 := (hasFDerivAt_snd (𝕜 := ℝ) (E := K) (F := ℝ) (p := MD.Fl x p)).comp_hasDerivAt x (MD.Fl_deriv p x)
    have h2 := h1.sub (hasDerivAt_id x)
    refine h2.congr_deriv ?_
    simp [Fc_snd]
  have := is_const_of_deriv_eq_zero (f := fun r => (MD.Fl r p).2 - r)
    (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) s 0
  simp only [MD.Fl_zero, sub_zero] at this
  linarith

theorem Fl_fst_deriv (p : K × ℝ) (t : ℝ) :
    HasDerivAt (fun s => (MD.Fl s p).1) (MD.cutF (‖(MD.Fl t p).1‖ ^ 2) • MD.Ghat (MD.Fl t p)) t := by
  have h := (hasFDerivAt_fst (𝕜 := ℝ) (E := K) (F := ℝ) (p := MD.Fl t p)).comp_hasDerivAt t
    (MD.Fl_deriv p t)
  exact h

theorem dq_cut_Ghat (q' : K × ℝ) (n : ℤ) :
    fderiv ℝ (q n) q'.1 (MD.cutF (‖q'.1‖ ^ 2) • MD.Ghat q') = 0 := by
  by_cases h0 : MD.cutF (‖q'.1‖ ^ 2) = 0
  · rw [h0, zero_smul, map_zero]
  · have hp := MD.mem_ball_of_cutF_ne h0
    rw [map_smul]
    have : fderiv ℝ (q n) q'.1 (MD.Ghat q') = 0 := MD.dq_Yf_zero (by
      have := abs_sig_le q'.2; linarith) hp n
    rw [this, smul_zero]

theorem q_Fl (p : K × ℝ) (n : ℤ) (t : ℝ) : q n (MD.Fl t p).1 = q n p.1 := by
  have hd : ∀ x : ℝ, HasDerivAt (fun r => q n (MD.Fl r p).1) 0 x := by
    intro x
    have h1 := ((hasFDerivAt_q n (MD.Fl x p).1).differentiableAt.hasFDerivAt).comp_hasDerivAt x
      (MD.Fl_fst_deriv p x)
    refine h1.congr_deriv ?_
    exact MD.dq_cut_Ghat (MD.Fl x p) n
  have := is_const_of_deriv_eq_zero (f := fun r => q n (MD.Fl r p).1)
    (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) t 0
  simpa [MD.Fl_zero] using this

theorem norm_Fl (p : K × ℝ) (t : ℝ) : ‖(MD.Fl t p).1‖ = ‖p.1‖ := by
  have h : ‖(MD.Fl t p).1‖ ^ 2 = ‖p.1‖ ^ 2 := by
    rw [tsum_norm_sq, tsum_norm_sq]
    congr 1
    funext n
    exact MD.q_Fl p n t
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- The Moser flow from `0` to `t`: `S_t z = (Φ_t (z, 0)).1`. -/
def Sfl (t : ℝ) (z : K) : K := (MD.Fl t (z, 0)).1

theorem Sfl_zero (z : K) : MD.Sfl 0 z = z := by simp [Sfl, MD.Fl_zero]

theorem Fl_eq (t : ℝ) (z : K) : MD.Fl t (z, 0) = (MD.Sfl t z, t) := by
  ext
  · rfl
  · simp [MD.Fl_snd]

theorem norm_Sfl (t : ℝ) (z : K) : ‖MD.Sfl t z‖ = ‖z‖ := MD.norm_Fl (z, 0) t

theorem q_Sfl (n : ℤ) (t : ℝ) (z : K) : q n (MD.Sfl t z) = q n z := MD.q_Fl (z, 0) n t

theorem Sfl_deriv {z : K} (hz : ‖z‖ ≤ MD.R0 / 4) (t : ℝ) :
    HasDerivAt (fun s => MD.Sfl s z) (MD.Yf (sig t) (MD.Sfl t z)) t := by
  have h := MD.Fl_fst_deriv (z, 0) t
  have hn : ‖(MD.Fl t (z, 0)).1‖ ≤ MD.R0 / 4 := by rw [MD.norm_Fl]; exact hz
  rw [MD.cutF_one hn, one_smul, MD.Fl_eq t z] at h
  exact h

end MoserData

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.MoserData.Fl_flowOn
#print axioms QuantumNLS.ResetMoser.MoserData.Fl_snd
#print axioms QuantumNLS.ResetMoser.MoserData.q_Fl
#print axioms QuantumNLS.ResetMoser.MoserData.norm_Fl
#print axioms QuantumNLS.ResetMoser.MoserData.Sfl_deriv
