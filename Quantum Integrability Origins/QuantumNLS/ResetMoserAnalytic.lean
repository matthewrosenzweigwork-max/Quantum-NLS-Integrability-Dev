import QuantumNLS.ResetMoserVar
import QuantumNLS.Ext025A4HeldDependence

/-!
# `thm:reset-moser` (LOCAL-017), item 5e: real analyticity of `S = S_1` and of `S^{-1}`

Source: `symplectic_correction.tex`, "The deformation and its invariant ball": "Picard iteration on a small complex neighborhood and continuation through finitely many
subintervals prove real analyticity."  Here via the ACCEPTED general Held GP-04 proposition `Ext025A4HeldDependence.held` (arbitrary real Banach `V`, `W`; the radius and the majorant constructed),
applied on `V = W = K × ℝ` (time as an extra coordinate), `L = id`, to the complete flow `Fl` of the cut-off field `Fc` (and, for `S^{-1}`, to the flow `t ↦ Fl (−t)` of `−Fc`):

* `Fc_analyticAt`: `Fc` is real analytic near every point `p` with `‖p.1‖ < R0/4` and `p.2 ∈ [0,1]` (there `Fc = (Ycov(t(Ω − ω)) β⁰, 1)`: analytic `Ω`, analytic `β⁰`, `analyticAt_YcovX`);
* the trajectory `{Fl t (u,0) : t ∈ [0,1]}` is compact and lies in that region (conservation of the norm, `Fl_snd`);
* `Sfl_one_analyticAt`, `Tinv_analyticAt`: `S_1` and `S_1^{-1}` are real analytic at every `u` with `‖u‖ < R0/4`.
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

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.ResetMoserClamp QuantumNLS.RealAnalyticDef

namespace MoserData

variable {S : Hyp} (MD : MoserData S)

theorem Fc_analyticAt {p : K × ℝ} (hp1 : ‖p.1‖ < MD.R0 / 4) (hp2 : p.2 ∈ Icc (0 : ℝ) 1) :
    AnalyticAt ℝ MD.Fc p := by
  have hR := MD.R0_pos
  have hpb : p.1 ∈ ball (0 : K) MD.R0 := mem_ball_zero_iff.2 (by linarith)
  have hΩ : AnalyticAt ℝ S.Ω p.1 :=
    analyticAt_of_isRealAnalyticPoly (S.Ω_analytic p.1 (MD.ball_sub hpb))
  have hD : AnalyticAt ℝ (fun q : K × ℝ => Dt S q.2 q.1) p :=
    analyticAt_snd.smul ((hΩ.comp analyticAt_fst).sub analyticAt_const)
  have hb : AnalyticAt ℝ (fun q : K × ℝ => MD.β0 q.1) p := (MD.β0_an p.1 hpb).comp analyticAt_fst
  have hsm : ‖Dt S p.2 p.1‖ < 1 :=
    MD.norm_Dt_lt (by rw [abs_of_nonneg hp2.1]; linarith [hp2.2]) hpb
  have hY := analyticAt_YcovX hD hb hsm
  have hev : MD.Fc =ᶠ[𝓝 p] fun q => (Ycov (Dt S q.2 q.1) (MD.β0 q.1), (1 : ℝ)) := by
    have h1 : ∀ᶠ q in 𝓝 p, ‖q.1‖ < MD.R0 / 4 :=
      (continuous_norm.comp continuous_fst).continuousAt.eventually (Iio_mem_nhds hp1)
    have h2 : ∀ᶠ q in 𝓝 p, q.2 ∈ Ioo (-1 / 4 : ℝ) (5 / 4) :=
      continuous_snd.continuousAt.eventually
        (Ioo_mem_nhds (by linarith [hp2.1]) (by linarith [hp2.2]))
    filter_upwards [h1, h2] with q hq1 hq2
    rw [MD.Fc_eq_of_small hq1.le]
    refine Prod.ext ?_ rfl
    show MD.Ghat q = _
    simp [Ghat, sig_eq ⟨hq2.1.le, hq2.2.le⟩]
  exact (hY.prod analyticAt_const).congr hev.symm

theorem Fl_continuous (v : K × ℝ) : Continuous (fun t => MD.Fl t v) :=
  continuous_iff_continuousAt.2 fun t => (MD.Fl_deriv v t).continuousAt

theorem Fl_one_analyticAt {u : K} (hu : ‖u‖ < MD.R0 / 4) : AnalyticAt ℝ (MD.Fl 1) (u, 0) := by
  have hcomp : IsCompact ((fun t => MD.Fl t (u, 0)) '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image (MD.Fl_continuous (u, 0))
  have hg : AnalyticOnNhd ℝ MD.Fc ((fun t => MD.Fl t (u, 0)) '' Icc (0 : ℝ) 1) := by
    rintro p ⟨t, ht, rfl⟩
    have h1 : ‖(MD.Fl t (u, 0)).1‖ < MD.R0 / 4 := by rw [MD.norm_Fl]; exact hu
    have h2 : (MD.Fl t (u, 0)).2 ∈ Icc (0 : ℝ) 1 := by rw [MD.Fl_snd]; simpa using ht
    exact MD.Fc_analyticAt h1 h2
  obtain ⟨r, hr, C, h⟩ := Ext025A4HeldDependence.held (V := K × ℝ) (W := K × ℝ) Unit MD.Fc
    (fun _ => ContinuousLinearMap.id ℝ (K × ℝ)) 1 (fun _ => MD.Fl)
    ((fun t => MD.Fl t (u, 0)) '' Icc (0 : ℝ) 1) (u, 0) hcomp hg
    (fun _ => ContinuousLinearMap.norm_id_le)
    (fun _ x t => MD.Fl_deriv x t) (fun _ x => MD.Fl_zero x) (fun _ t ht => ⟨t, ht, rfl⟩)
  obtain ⟨p, hp, _⟩ := h ()
  exact hp.analyticAt

theorem Fl_neg_one_analyticAt {w : K} (hw : ‖w‖ < MD.R0 / 4) : AnalyticAt ℝ (MD.Fl (-1)) (w, 1) := by
  have hcomp : IsCompact ((fun t => MD.Fl (-t) (w, 1)) '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image ((MD.Fl_continuous (w, 1)).comp continuous_neg)
  have hg : AnalyticOnNhd ℝ (fun v => -MD.Fc v) ((fun t => MD.Fl (-t) (w, 1)) '' Icc (0 : ℝ) 1) := by
    rintro p ⟨t, ht, rfl⟩
    have h1 : ‖(MD.Fl (-t) (w, 1)).1‖ < MD.R0 / 4 := by rw [MD.norm_Fl]; exact hw
    have h2 : (MD.Fl (-t) (w, 1)).2 ∈ Icc (0 : ℝ) 1 := by
      rw [MD.Fl_snd]
      constructor <;> linarith [ht.1, ht.2]
    exact (MD.Fc_analyticAt h1 h2).neg
  obtain ⟨r, hr, C, h⟩ := Ext025A4HeldDependence.held (V := K × ℝ) (W := K × ℝ) Unit (fun v => -MD.Fc v)
    (fun _ => ContinuousLinearMap.id ℝ (K × ℝ)) 1 (fun _ t x => MD.Fl (-t) x)
    ((fun t => MD.Fl (-t) (w, 1)) '' Icc (0 : ℝ) 1) (w, 1) hcomp hg
    (fun _ => ContinuousLinearMap.norm_id_le)
    (fun _ x t => by
      have := (MD.Fl_deriv x (-t)).scomp t (hasDerivAt_neg t)
      refine this.congr_deriv ?_
      simp)
    (fun _ x => by simp [MD.Fl_zero]) (fun _ t ht => ⟨t, ht, rfl⟩)
  obtain ⟨p, hp, _⟩ := h ()
  exact hp.analyticAt

theorem Sfl_one_analyticAt {u : K} (hu : ‖u‖ < MD.R0 / 4) : AnalyticAt ℝ (MD.Sfl 1) u := by
  have h1 : AnalyticAt ℝ (fun v : K => ((v, (0 : ℝ)) : K × ℝ)) u := analyticAt_id.prod analyticAt_const
  have h2 : AnalyticAt ℝ (MD.Fl 1) (u, 0) := MD.Fl_one_analyticAt hu
  have h3 : AnalyticAt ℝ (fun v : K => MD.Fl 1 (v, 0)) u :=
    AnalyticAt.comp_of_eq (g := MD.Fl 1) (f := fun v : K => ((v, (0 : ℝ)) : K × ℝ)) h2 h1 rfl
  exact AnalyticAt.comp_of_eq (g := Prod.fst) (f := fun v : K => MD.Fl 1 (v, 0)) analyticAt_fst h3 rfl

theorem Tinv_analyticAt {w : K} (hw : ‖w‖ < MD.R0 / 4) : AnalyticAt ℝ MD.Tinv w := by
  have h1 : AnalyticAt ℝ (fun v : K => ((v, (1 : ℝ)) : K × ℝ)) w := analyticAt_id.prod analyticAt_const
  have h2 : AnalyticAt ℝ (MD.Fl (-1)) (w, 1) := MD.Fl_neg_one_analyticAt hw
  have h3 : AnalyticAt ℝ (fun v : K => MD.Fl (-1) (v, 1)) w :=
    AnalyticAt.comp_of_eq (g := MD.Fl (-1)) (f := fun v : K => ((v, (1 : ℝ)) : K × ℝ)) h2 h1 rfl
  exact AnalyticAt.comp_of_eq (g := Prod.fst) (f := fun v : K => MD.Fl (-1) (v, 1)) analyticAt_fst h3 rfl

end MoserData

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.MoserData.Fc_analyticAt
#print axioms QuantumNLS.ResetMoser.MoserData.Sfl_one_analyticAt
#print axioms QuantumNLS.ResetMoser.MoserData.Tinv_analyticAt
