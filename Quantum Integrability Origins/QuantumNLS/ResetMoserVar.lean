import QuantumNLS.ResetMoserCutFlow
import QuantumNLS.ResetMoserGronwallOp

/-!
# `thm:reset-moser` (LOCAL-017), item 5d: the variational equation of `S_t`, the Gronwall bounds for `DS_t` and `DS_t^{-1}`, the inverse, the cubic displacement

Source: `symplectic_correction.tex`, "The deformation and its invariant ball": "The full variational equation and Gronwall's inequality give
`‖DS_t(z) − 1‖ ≤ e^{C‖z‖²} − 1`, `‖DS_t(z)^{-1}‖ ≤ e^{C‖z‖²}`.  The same estimates hold for the reversed flow.  The cubic displacement bound follows by integrating `Y_t`."

All from the frozen `ResetMoserFlowGlobal` (`diffAt`, `group_law`, `variational`) applied to the complete flow `Fl` of `Fc` on `K × ℝ`:
* `Lam T = fst ∘ T ∘ inl` (the `K`-block of an operator on `K × ℝ`); `DS_eq : DS_t(z) = Lam (D Fl_t (z,0))`; `DS_var : ∂ₜ DS_t(z) = Lam(DFc(Φ_t)) DS_t(z)`;
* `exists_var_bound`: `‖Lam(D Fl_{εr} q) − 1‖ ≤ κ‖z‖² e^{κ‖z‖²}` for `|ε| ≤ 1`, `r ∈ [0,1]`, `‖z‖ < R0/4` (`ε = 1`: `S_1`; `ε = −1` at `(w, 1)`: the reversed flow);
* `Tinv w = (Fl (−1) (w, 1)).1`: `Tinv ∘ S_1 = id`, `S_1 ∘ Tinv = id` (group law);
* `norm_Sfl_sub_le`: `‖S_1 z − z‖ ≤ B‖z‖³`.
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

/-- The `K`-block `T ↦ fst ∘ T ∘ inl` of an operator on `K × ℝ`. -/
def Lam : (K × ℝ →L[ℝ] K × ℝ) →L[ℝ] (K →L[ℝ] K) :=
  ((ContinuousLinearMap.compL ℝ K (K × ℝ) K) (ContinuousLinearMap.fst ℝ K ℝ)).comp
    ((ContinuousLinearMap.compL ℝ K (K × ℝ) (K × ℝ)).flip (ContinuousLinearMap.inl ℝ K ℝ))

theorem Lam_apply (T : K × ℝ →L[ℝ] K × ℝ) (h : K) : Lam T h = (T (h, 0)).1 := by
  simp [Lam]

theorem Lam_one : Lam (1 : K × ℝ →L[ℝ] K × ℝ) = 1 := by
  ext h
  simp [Lam_apply]

theorem norm_Lam_prod_le (L : K × ℝ →L[ℝ] K) : ‖Lam (L.prod (0 : K × ℝ →L[ℝ] ℝ))‖ ≤ ‖L‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun h => ?_)
  rw [Lam_apply]
  simp only [ContinuousLinearMap.prod_apply]
  have h1 : ‖(h, (0 : ℝ))‖ = ‖h‖ := by simp [Prod.norm_def]
  calc ‖L (h, 0)‖ ≤ ‖L‖ * ‖(h, (0 : ℝ))‖ := L.le_opNorm _
    _ = ‖L‖ * ‖h‖ := by rw [h1]

namespace MoserData

variable {S : Hyp} (MD : MoserData S)

theorem Fl_diff (t : ℝ) (p : K × ℝ) : DifferentiableAt ℝ (MD.Fl t) p :=
  ResetMoserFlow.diffAt MD.Fl_flowOn (mem_univ p) t

theorem snd_fderiv_Fl (t : ℝ) (p v : K × ℝ) : (fderiv ℝ (MD.Fl t) p v).2 = v.2 := by
  have h1 : HasFDerivAt (fun q => (MD.Fl t q).2)
      ((ContinuousLinearMap.snd ℝ K ℝ).comp (fderiv ℝ (MD.Fl t) p)) p :=
    (hasFDerivAt_snd).comp p (MD.Fl_diff t p).hasFDerivAt
  have h2 : HasFDerivAt (fun q : K × ℝ => (MD.Fl t q).2) (ContinuousLinearMap.snd ℝ K ℝ) p := by
    have : (fun q : K × ℝ => (MD.Fl t q).2) = fun q => q.2 + t := funext fun q => MD.Fl_snd q t
    rw [this]
    exact (hasFDerivAt_snd).add_const t
  have := h1.unique h2
  simpa using congrArg (fun T => T v) this

theorem J_inl (t : ℝ) (p : K × ℝ) (h : K) :
    fderiv ℝ (MD.Fl t) p (h, 0) = (Lam (fderiv ℝ (MD.Fl t) p) h, 0) := by
  ext
  · simp [Lam_apply]
  · simpa using MD.snd_fderiv_Fl t p (h, 0)

theorem Lam_comp_J (T : K × ℝ →L[ℝ] K × ℝ) (t : ℝ) (p : K × ℝ) :
    Lam (T.comp (fderiv ℝ (MD.Fl t) p)) = Lam T * Lam (fderiv ℝ (MD.Fl t) p) := by
  refine ContinuousLinearMap.ext (fun h => ?_)
  calc Lam (T.comp (fderiv ℝ (MD.Fl t) p)) h = (T (fderiv ℝ (MD.Fl t) p (h, 0))).1 := Lam_apply _ _
    _ = (T (Lam (fderiv ℝ (MD.Fl t) p) h, 0)).1 := by rw [MD.J_inl]
    _ = (Lam T * Lam (fderiv ℝ (MD.Fl t) p)) h := (Lam_apply _ _).symm

theorem hasFDerivAt_Sfl (t : ℝ) (z : K) :
    HasFDerivAt (MD.Sfl t) (Lam (fderiv ℝ (MD.Fl t) (z, 0))) z := by
  have h1 : HasFDerivAt (fun w : K => ((w, (0 : ℝ)) : K × ℝ)) (ContinuousLinearMap.inl ℝ K ℝ) z :=
    hasFDerivAt_prodMk_left z (0 : ℝ)
  have h2 := (hasFDerivAt_fst (𝕜 := ℝ) (E := K) (F := ℝ) (p := MD.Fl t (z, 0))).comp z
    ((MD.Fl_diff t (z, 0)).hasFDerivAt.comp z h1)
  exact h2

theorem DS_eq (t : ℝ) (z : K) : fderiv ℝ (MD.Sfl t) z = Lam (fderiv ℝ (MD.Fl t) (z, 0)) :=
  (MD.hasFDerivAt_Sfl t z).fderiv

theorem Sfl_diff (t : ℝ) (z : K) : DifferentiableAt ℝ (MD.Sfl t) z :=
  (MD.hasFDerivAt_Sfl t z).differentiableAt

/-- The variational equation in the time variable: `∂ₜ DS_t(z) = Lam(DFc(Φ_t(z,0))) · DS_t(z)`. -/
theorem DS_var (z : K) (r : ℝ) :
    HasDerivAt (fun s => fderiv ℝ (MD.Sfl s) z)
      (Lam (fderiv ℝ MD.Fc (MD.Fl r (z, 0))) * fderiv ℝ (MD.Sfl r) z) r := by
  have hv := ResetMoserFlow.variational MD.Fl_flowOn (mem_univ (z, (0 : ℝ))) r
  have h2 := (Lam.hasFDerivAt).comp_hasDerivAt r hv
  have e : (fun s => fderiv ℝ (MD.Sfl s) z) = fun s => Lam (fderiv ℝ (MD.Fl s) (z, 0)) :=
    funext fun s => MD.DS_eq s z
  rw [e, MD.DS_eq]
  refine h2.congr_deriv ?_
  exact MD.Lam_comp_J _ r (z, 0)

theorem exists_kappa : ∃ κ : ℝ, 0 ≤ κ ∧ ∀ q : K × ℝ, ‖q.1‖ < MD.R0 / 4 →
    ∃ L : K × ℝ →L[ℝ] K, HasFDerivAt MD.Ghat L q ∧
      fderiv ℝ MD.Fc q = L.prod (0 : K × ℝ →L[ℝ] ℝ) ∧ ‖L‖ ≤ κ * ‖q.1‖ ^ 2 := by
  obtain ⟨κ, hκ, h⟩ := MD.Ghat_deriv_kappa
  refine ⟨κ, hκ, fun q hq => ?_⟩
  have hqR : q.1 ∈ ball (0 : K) MD.R0 := by
    rw [mem_ball_zero_iff]; have := MD.R0_pos; linarith
  obtain ⟨L, hL, hLn⟩ := h q hqR
  refine ⟨L, hL, ?_, hLn⟩
  have hev : MD.Fc =ᶠ[𝓝 q] fun r => (MD.Ghat r, (1 : ℝ)) := by
    filter_upwards [(continuous_norm.comp continuous_fst).continuousAt.eventually
      (Iio_mem_nhds hq)] with r hr
    exact MD.Fc_eq_of_small (le_of_lt hr)
  have : HasFDerivAt MD.Fc (L.prod (0 : K × ℝ →L[ℝ] ℝ)) q :=
    (hL.prodMk (hasFDerivAt_const (1 : ℝ) q)).congr_of_eventuallyEq hev
  exact this.fderiv

theorem var_deriv (q : K × ℝ) (ε r : ℝ) :
    HasDerivAt (fun s => Lam (fderiv ℝ (MD.Fl (ε * s)) q))
      ((ε • Lam (fderiv ℝ MD.Fc (MD.Fl (ε * r) q))) * Lam (fderiv ℝ (MD.Fl (ε * r)) q)) r := by
  have hv := ResetMoserFlow.variational MD.Fl_flowOn (mem_univ q) (ε * r)
  have h1 := hv.scomp r ((hasDerivAt_id r).const_mul ε)
  have h2 := (Lam.hasFDerivAt).comp_hasDerivAt r h1
  refine h2.congr_deriv ?_
  rw [map_smul, MD.Lam_comp_J]
  refine ContinuousLinearMap.ext (fun h => ?_)
  simp

theorem exists_var_bound : ∃ κ : ℝ, 0 ≤ κ ∧ ∀ q : K × ℝ, ‖q.1‖ < MD.R0 / 4 → ∀ ε : ℝ, |ε| ≤ 1 →
    ∀ r ∈ Icc (0 : ℝ) 1, ‖Lam (fderiv ℝ (MD.Fl (ε * r)) q) - 1‖ ≤
      κ * ‖q.1‖ ^ 2 * Real.exp (κ * ‖q.1‖ ^ 2) := by
  obtain ⟨κ, hκ, h⟩ := MD.exists_kappa
  refine ⟨κ, hκ, fun q hq ε hε r hr => ?_⟩
  have hk0 : 0 ≤ κ * ‖q.1‖ ^ 2 := by positivity
  have hU0 : Lam (fderiv ℝ (MD.Fl (ε * 0)) q) = 1 := by
    have : MD.Fl (ε * 0) = id := by
      rw [mul_zero]; exact funext MD.Fl_zero
    rw [this, fderiv_id]
    exact Lam_one
  have hd : ∀ s : ℝ, HasDerivAt (fun s => Lam (fderiv ℝ (MD.Fl (ε * s)) q))
      ((ε • Lam (fderiv ℝ MD.Fc (MD.Fl (ε * s) q))) * Lam (fderiv ℝ (MD.Fl (ε * s)) q)) s :=
    fun s => MD.var_deriv q ε s
  have hA : ∀ s ∈ Icc (0 : ℝ) 1, ‖ε • Lam (fderiv ℝ MD.Fc (MD.Fl (ε * s) q))‖ ≤ κ * ‖q.1‖ ^ 2 := by
    intro s _
    have hq' : ‖(MD.Fl (ε * s) q).1‖ < MD.R0 / 4 := by rw [MD.norm_Fl]; exact hq
    obtain ⟨L, _, hLf, hLn⟩ := h _ hq'
    rw [hLf, norm_smul, Real.norm_eq_abs]
    rw [MD.norm_Fl] at hLn
    calc |ε| * ‖Lam (L.prod (0 : K × ℝ →L[ℝ] ℝ))‖ ≤ 1 * ‖L‖ :=
          mul_le_mul hε (norm_Lam_prod_le L) (norm_nonneg _) zero_le_one
      _ ≤ κ * ‖q.1‖ ^ 2 := by rw [one_mul]; exact hLn
  exact (ResetMoserGronwallOp.gronwall_op (U := fun s => Lam (fderiv ℝ (MD.Fl (ε * s)) q))
    (A := fun s => ε • Lam (fderiv ℝ MD.Fc (MD.Fl (ε * s) q))) hk0 hU0 hd hA r hr).2

/-- The inverse candidate `T w = (Φ_{-1}(w, 1)).1`. -/
def Tinv (w : K) : K := (MD.Fl (-1) (w, 1)).1

theorem Fl_neg_eq (w : K) : MD.Fl (-1) (w, 1) = (MD.Tinv w, 0) := by
  ext
  · rfl
  · simp [MD.Fl_snd]

theorem Sfl_one_Tinv (w : K) : MD.Sfl 1 (MD.Tinv w) = w := by
  have h := ResetMoserFlow.group_law MD.Fl_flowOn (mem_univ ((w, (1 : ℝ)) : K × ℝ)) (-1) 1
  rw [neg_add_cancel, MD.Fl_zero, MD.Fl_neg_eq, MD.Fl_eq] at h
  exact (congrArg Prod.fst h).symm

theorem Tinv_Sfl_one (z : K) : MD.Tinv (MD.Sfl 1 z) = z := by
  have h := ResetMoserFlow.group_law MD.Fl_flowOn (mem_univ ((z, (0 : ℝ)) : K × ℝ)) 1 (-1)
  rw [add_neg_cancel, MD.Fl_zero, MD.Fl_eq, MD.Fl_neg_eq] at h
  exact (congrArg Prod.fst h).symm

theorem hasFDerivAt_Tinv (w : K) :
    HasFDerivAt MD.Tinv (Lam (fderiv ℝ (MD.Fl (-1)) (w, 1))) w := by
  have h1 : HasFDerivAt (fun v : K => ((v, (1 : ℝ)) : K × ℝ)) (ContinuousLinearMap.inl ℝ K ℝ) w :=
    hasFDerivAt_prodMk_left w (1 : ℝ)
  have h2 := (hasFDerivAt_fst (𝕜 := ℝ) (E := K) (F := ℝ) (p := MD.Fl (-1) (w, 1))).comp w
    ((MD.Fl_diff (-1) (w, 1)).hasFDerivAt.comp w h1)
  exact h2

theorem norm_Tinv (w : K) : ‖MD.Tinv w‖ = ‖w‖ := MD.norm_Fl (w, 1) (-1)

theorem norm_Sfl_sub_le {z : K} (hz : ‖z‖ < MD.R0 / 4) : ‖MD.Sfl 1 z - z‖ ≤ MD.B * ‖z‖ ^ 3 := by
  have hR := MD.R0_pos
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun t => MD.Sfl t z)
    (f' := fun t => MD.Yf (sig t) (MD.Sfl t z)) (C := MD.B * ‖z‖ ^ 3) (a := 0) (b := 1)
    (fun x _ => (MD.Sfl_deriv hz.le x).hasDerivWithinAt)
    (fun x _ => by
      have hb : MD.Sfl x z ∈ ball (0 : K) MD.R0 := by
        rw [mem_ball_zero_iff, MD.norm_Sfl]; linarith
      have := MD.norm_Yf_le (t := sig x) (by have := abs_sig_le x; linarith) hb
      rwa [MD.norm_Sfl] at this) 1 ⟨zero_le_one, le_rfl⟩
  simpa [MD.Sfl_zero] using h

end MoserData

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.MoserData.DS_var
#print axioms QuantumNLS.ResetMoser.MoserData.exists_var_bound
#print axioms QuantumNLS.ResetMoser.MoserData.Sfl_one_Tinv
#print axioms QuantumNLS.ResetMoser.MoserData.Tinv_Sfl_one
#print axioms QuantumNLS.ResetMoser.MoserData.norm_Sfl_sub_le
