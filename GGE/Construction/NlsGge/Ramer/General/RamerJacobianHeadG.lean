import Mathlib
import NlsGge.Ramer.General.FibreBridgeGb
import NlsGge.Ramer.General.RamerStep2FibrewiseG
import NlsGge.Ramer.General.RamerStep8aG
import NlsGge.Ramer.General.RamerApproximantG
import NlsGge.Ramer.General.SpaceTransferG
import NlsGge.Ramer.General.RamerDensityG
import NlsGge.Ramer.General.HypothesisBridgeG
import NlsGge.Ramer.General.DivergenceIdentificationGlobalG
import NlsGge.Ramer.General.LinearDecompositionG
import NlsGge.Ramer.RamerFiniteChainRule

/-!
# R9a, generalized (GD9): the Ramer Jacobian of a general field, and head-valued fields

Adapted from `NlsGge/Ramer/RamerJacobianHead.lean` over a `RamerSetting S`.  Dictionary:
`ramerDiv ↦ S.ramerDiv`, `ramerJac ↦ S.ramerJac`, `TM ↦ S.TM`, `compField ↦ S.compField`,
`fibreMapOf ↦ S.fibreMapOf`, `fibreJ ↦ S.fibreJ`, `ramerA ↦ S.ramerA`, `ramerJE ↦ S.ramerJE`,
`headProj c m ↦ S.headProj m`, `inclE ↦ S.incl`, `fullWeightedSequenceGaussian c s ↦ S.γE`,
`fullWeightSequenceGaussian c.val ↦ S.γ`.  No norm of `E` is used.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal RealInnerProductSpace

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer NlsGge.Analysis.RegularizedDeterminant

section General

variable (S : NlsGge.Ramer.General.RamerSetting)

open Classical in
/-- A fixed choice of the L3b divergence of a `C²` field (and `0` for other fields).
(Old: `ramerDiv`.) -/
def ramerDiv (M : S.E → S.H) : (ℤ → ℂ) → ℝ :=
  if h : ContDiff ℝ 2 M then Classical.choose (S.divergence_identification M h) else 0

/-- Ramer's `J^{I+M}`. (Old: `ramerJac`.) -/
def ramerJac (M : S.E → S.H) (x : S.E) : ℝ :=
  S.ramerJE M (S.ramerDiv M) x

theorem ramerJac_eq (M : S.E → S.H) (x : S.E) :
    S.ramerJac M x =
      |det2 (S.hsDerivH M x)| *
        Real.exp (-(S.ramerDiv M (S.coordE x)) - ‖M x‖ ^ 2 / 2) :=
  S.ramerJE_eq _ _ x

theorem ramerDiv_spec (M : S.E → S.H) (hM : ContDiff ℝ 2 M) :
    AEStronglyMeasurable (S.ramerDiv M) S.γ ∧
    (∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ z ∂S.γ,
        Tendsto (fun j => S.ramerA (φ j) M z) atTop (𝓝 (S.ramerDiv M z))) ∧
    TendstoInMeasure S.γ (fun n => S.ramerA n M) atTop (S.ramerDiv M) := by
  have h := Classical.choose_spec (S.divergence_identification M hM)
  unfold ramerDiv
  rw [dif_pos hM]
  exact ⟨h.1, h.2.2.2.1, h.2.2.2.2⟩

/-! ### Item 1: stabilization -/

theorem headProj_apply (n : ℕ) (h : S.H) :
    S.headProj n h = ((S.cmTrunc n h : S.head n) : S.H) := rfl

/-- Pairing with a basis vector outside `W m` kills `P_m`-fixed vectors. -/
theorem inner_basis_of_headFixed (m : ℕ) (p : ℤ × Fin 2) (hp : p.1 ∉ symmetricModes m)
    (w : S.H) (hw : S.headProj m w = w) :
    ⟪weightedRealHilbertBasis S.cmWeight p, w⟫ = 0 := by
  rw [← hw, S.headProj_apply, S.inner_basis_cmTrunc, if_neg hp]

theorem fderiv_headFixed (m : ℕ) (M : S.E → S.H)
    (hMd : Differentiable ℝ M) (hm : ∀ x, S.headProj m (M x) = M x)
    (x : S.E) (v : S.E) :
    S.headProj m (fderiv ℝ M x v) = fderiv ℝ M x v := by
  have hM' : M = fun y => S.headProj m (M y) := funext fun y => (hm y).symm
  have h1 : fderiv ℝ M x = fderiv ℝ (fun y => S.headProj m (M y)) x :=
    congrArg (fun f => fderiv ℝ f x) hM'
  have h2 : fderiv ℝ (fun y => S.headProj m (M y)) x = (S.headProj m).comp (fderiv ℝ M x) :=
    ((S.headProj m).hasFDerivAt.comp x (hMd x).hasFDerivAt).fderiv
  exact (congrArg (fun L => L v) (h1.trans h2)).symm

/-- **Item 1.** For a `V_m`-valued `C¹` field, `ramerA n M = ramerA m M` for `n ≥ m`. -/
theorem ramerA_eq_of_headValued {m : ℕ} (M : S.E → S.H)
    (hMd : Differentiable ℝ M) (hm : ∀ x, S.headProj m (M x) = M x) {n : ℕ} (hmn : m ≤ n) :
    S.ramerA n M = S.ramerA m M := by
  funext z
  unfold ramerA
  have hsub : basisIndex m ⊆ basisIndex n := by
    intro p hp
    rw [Finset.mem_product] at hp ⊢
    exact ⟨symmetricModes_mono hmn hp.1, hp.2⟩
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl (fun p hp => ?_)
    have hp1 : p.1 ∈ symmetricModes m := (Finset.mem_product.1 hp).1
    have : ⟪weightedRealHilbertBasis S.cmWeight p, ((S.headPt n z : S.head n) : S.H)⟫ =
        ⟪weightedRealHilbertBasis S.cmWeight p, ((S.headPt m z : S.head m) : S.H)⟫ := by
      apply S.inner_basis_congr
      rw [S.hcoord_headPt, S.hcoord_headPt, if_pos (symmetricModes_mono hmn hp1), if_pos hp1]
    have this' : ⟪((S.headPt n z : S.head n) : S.H),
        weightedRealHilbertBasis S.cmWeight p⟫ =
        ⟪((S.headPt m z : S.head m) : S.H),
        weightedRealHilbertBasis S.cmWeight p⟫ :=
      (real_inner_comm _ _).symm.trans (this.trans (real_inner_comm _ _))
    rw [this']
  · intro p hpn hpm
    have hp1 : p.1 ∉ symmetricModes m := fun h => hpm (Finset.mem_product.2 ⟨h, Finset.mem_univ _⟩)
    rw [S.inner_basis_of_headFixed m p hp1 _ (hm _),
      S.inner_basis_of_headFixed m p hp1 _ (S.fderiv_headFixed m M hMd hm _ _)]
    simp

/-- **Item 1 (a.e. form).** `ramerDiv M = ramerA m M` `γ`-a.e. -/
theorem ramerDiv_ae_eq_ramerA {m : ℕ}
    (M : S.E → S.H) (hM : ContDiff ℝ 2 M)
    (hm : ∀ x, S.headProj m (M x) = M x) :
    ∀ᵐ z ∂S.γ, S.ramerDiv M z = S.ramerA m M z := by
  obtain ⟨φ, hφ, hlim⟩ := (S.ramerDiv_spec M hM).2.1
  filter_upwards [hlim] with z hz
  have hev : ∀ᶠ j in atTop, S.ramerA (φ j) M z = S.ramerA m M z := by
    filter_upwards [eventually_ge_atTop m] with j hj
    have := S.ramerA_eq_of_headValued M
      (hM.differentiable (by norm_num)) hm ((hj.trans (hφ.id_le j)))
    exact congrFun this z
  exact tendsto_nhds_unique hz (tendsto_const_nhds.congr' (hev.mono fun j h => h.symm))

/-- **Item 1 on `E`.** -/
theorem ramerDiv_coordE_ae_eq {m : ℕ}
    (M : S.E → S.H) (hM : ContDiff ℝ 2 M)
    (hm : ∀ x, S.headProj m (M x) = M x) :
    ∀ᵐ x ∂S.γE, S.ramerDiv M (S.coordE x) = S.ramerA m M (S.coordE x) :=
  S.ae_of_ae_coordE (S.ramerDiv_ae_eq_ramerA M hM hm)

/-! ### Item 2: the fibre form -/

/-- The map `T_M = I + iM`. (Old: `TM`.) -/
def TM (M : S.E → S.H) (y : S.E) : S.E :=
  y + S.incl (M y)

theorem Sn_eq_TM {m : ℕ} (M : S.E → S.H)
    (hm : ∀ x, S.headProj m (M x) = M x) : S.Sn m M = S.TM M := by
  funext y
  simp only [Sn, TM, hm]

/-- For a `V_m`-valued field, `ramerJE M (ramerA m M)` is the fibre Jacobian of `I + iM`. -/
theorem fibreJ_TM_eq {m : ℕ} (M : S.E → S.H)
    (hM : ContDiff ℝ 1 M) (hm : ∀ x, S.headProj m (M x) = M x) (x : S.E) :
    S.fibreJ m (S.fibreMapOf m (S.TM M)) (S.coordE x) =
      S.ramerJE M (S.ramerA m M) x := by
  rw [← S.Sn_eq_TM M hm, S.fibreJ_Sn_eq m M hM x, ramerJn]
  have e : (fun y => S.headProj m (M y)) = M := funext hm
  rw [e]

/-- **Item 2.** `ramerJac M x` is the fibre Jacobian of the fibre maps of `I + iM`, a.e. -/
theorem ramerJac_ae_eq_fibreJ {m : ℕ}
    (M : S.E → S.H) (hM : ContDiff ℝ 2 M)
    (hm : ∀ x, S.headProj m (M x) = M x) :
    ∀ᵐ x ∂S.γE,
      S.ramerJac M x = S.fibreJ m (S.fibreMapOf m (S.TM M)) (S.coordE x) := by
  filter_upwards [S.ramerDiv_coordE_ae_eq M hM hm] with x hx
  rw [S.fibreJ_TM_eq M (hM.of_le (by norm_num)) hm, ramerJac, S.ramerJE_eq, S.ramerJE_eq, hx]

/-! ### Item 4: product formula -/

theorem differentiable_TM (M : S.E → S.H)
    (hM : Differentiable ℝ M) : Differentiable ℝ (S.TM M) :=
  differentiable_id.add (S.incl.differentiable.comp hM)

theorem contDiff_TM (M : S.E → S.H)
    {k : ℕ∞} (hM : ContDiff ℝ k M) : ContDiff ℝ k (S.TM M) :=
  contDiff_id.add (S.incl.contDiff.comp hM)

/-- The composite field `M₁ + M₂ ∘ (I + iM₁)`. (Old: `compField`.) -/
def compField (M₁ M₂ : S.E → S.H) (x : S.E) : S.H :=
  M₁ x + M₂ (S.TM M₁ x)

theorem TM_compField (M₁ M₂ : S.E → S.H) :
    S.TM (S.compField M₁ M₂) = S.TM M₂ ∘ S.TM M₁ := by
  funext x
  simp only [TM, compField, Function.comp, map_add]
  abel

theorem contDiff_compField (M₁ M₂ : S.E → S.H)
    {k : ℕ∞} (h₁ : ContDiff ℝ k M₁) (h₂ : ContDiff ℝ k M₂) :
    ContDiff ℝ k (S.compField M₁ M₂) :=
  h₁.add (h₂.comp (S.contDiff_TM M₁ h₁))

theorem headProj_compField {m : ℕ}
    (M₁ M₂ : S.E → S.H)
    (h₁ : ∀ x, S.headProj m (M₁ x) = M₁ x) (h₂ : ∀ x, S.headProj m (M₂ x) = M₂ x)
    (x : S.E) :
    S.headProj m (S.compField M₁ M₂ x) = S.compField M₁ M₂ x := by
  simp only [compField, map_add, h₁, h₂]

theorem sameTail_TM {m : ℕ} (M : S.E → S.H)
    (hm : ∀ x, S.headProj m (M x) = M x) (x : S.E) :
    S.SameTail m (S.TM M x) x := by
  rw [← S.Sn_eq_TM M hm]
  exact S.sameTail_Sn m M x

/-- Fibre maps compose, for tail-fixing maps. -/
theorem fibreMapOf_comp (m : ℕ) (Φ Ψ : S.E → S.E)
    (hΦ : ∀ x, S.SameTail m (Φ x) x) (t : TailSpace m) :
    S.fibreMapOf m (Ψ ∘ Φ) t = S.fibreMapOf m Ψ t ∘ S.fibreMapOf m Φ t := by
  funext v
  by_cases ht : S.TailSummable m t
  · have h1 := S.realE_headRec_fibreMapOf m Φ t v ht (hΦ _)
    have e1 := S.realE_headRec m v t ht
    have e2 := S.realE_headRec m (S.fibreMapOf m Φ t v) t ht
    have hb : S.tailBase m t + S.headToE m (S.fibreMapOf m Φ t v) =
        Φ (S.tailBase m t + S.headToE m v) := by
      rw [← e1, ← e2]; exact h1
    show S.fibreMapOf m (Ψ ∘ Φ) t v = S.fibreMapOf m Ψ t (S.fibreMapOf m Φ t v)
    rw [S.fibreMapOf_of_summable m _ t v ht, S.fibreMapOf_of_summable m Ψ t _ ht, hb]
    rfl
  · show S.fibreMapOf m (Ψ ∘ Φ) t v = S.fibreMapOf m Ψ t (S.fibreMapOf m Φ t v)
    rw [S.fibreMapOf_of_not_summable m _ t _ ht, S.fibreMapOf_of_not_summable m _ t _ ht,
      S.fibreMapOf_of_not_summable m _ t _ ht]

theorem tailPt_coordE_of_sameTail (m : ℕ) (Φ : S.E → S.E)
    (hΦ : ∀ x, S.SameTail m (Φ x) x) (x : S.E) :
    tailPt m (S.coordE (Φ x)) = tailPt m (S.coordE x) := by
  funext i
  exact hΦ x i.1 i.2

theorem headPt_coordE_eq_fibreMapOf (m : ℕ) (Φ : S.E → S.E) (x : S.E) :
    S.headPt m (S.coordE (Φ x)) =
      S.fibreMapOf m Φ (tailPt m (S.coordE x)) (S.headPt m (S.coordE x)) := by
  rw [S.fibreMapOf_of_summable m Φ _ _ (S.tailSummable_coordE m x),
    S.tailBase_add_headToE m x]

/-- Chain rule for the fibre Jacobians of tail-fixing maps, pointwise. -/
theorem fibreJ_comp (m : ℕ) (Φ Ψ : S.E → S.E)
    (hΦ : ∀ x, S.SameTail m (Φ x) x)
    (hΦf : ∀ t, Differentiable ℝ (S.fibreMapOf m Φ t))
    (hΨf : ∀ t, Differentiable ℝ (S.fibreMapOf m Ψ t)) (x : S.E) :
    S.fibreJ m (S.fibreMapOf m (Ψ ∘ Φ)) (S.coordE x) =
      S.fibreJ m (S.fibreMapOf m Ψ) (S.coordE (Φ x)) *
        S.fibreJ m (S.fibreMapOf m Φ) (S.coordE x) := by
  unfold fibreJ
  rw [S.fibreMapOf_comp m Φ Ψ hΦ, S.tailPt_coordE_of_sameTail m Φ hΦ x,
    S.headPt_coordE_eq_fibreMapOf m Φ x]
  exact finiteRamerDensity_comp _ _ _ (hΦf _ _) (hΨf _ _)

/-- **Item 4 (exact pointwise form).** -/
theorem ramerJE_compField {m : ℕ}
    (M₁ M₂ : S.E → S.H)
    (h₁ : ContDiff ℝ 1 M₁) (h₂ : ContDiff ℝ 1 M₂)
    (hm₁ : ∀ x, S.headProj m (M₁ x) = M₁ x) (hm₂ : ∀ x, S.headProj m (M₂ x) = M₂ x)
    (x : S.E) :
    S.ramerJE (S.compField M₁ M₂) (S.ramerA m (S.compField M₁ M₂)) x =
      S.ramerJE M₂ (S.ramerA m M₂) (S.TM M₁ x) *
        S.ramerJE M₁ (S.ramerA m M₁) x := by
  have h12 := S.contDiff_compField M₁ M₂ h₁ h₂
  have hm12 := S.headProj_compField M₁ M₂ hm₁ hm₂
  rw [← S.fibreJ_TM_eq _ h12 hm12, ← S.fibreJ_TM_eq M₂ h₂ hm₂,
    ← S.fibreJ_TM_eq M₁ h₁ hm₁, TM_compField]
  have hd : ∀ {M : S.E → S.H}, ContDiff ℝ 1 M →
      (∀ x, S.headProj m (M x) = M x) → ∀ t, Differentiable ℝ (S.fibreMapOf m (S.TM M) t) :=
    fun {M} hM hmM t => by
      rw [← S.Sn_eq_TM M hmM]
      exact S.differentiable_fibreMapOf_Sn m M (hM.differentiable one_ne_zero) t
  exact S.fibreJ_comp m _ _ (S.sameTail_TM M₁ hm₁)
    (hd h₁ hm₁) (hd h₂ hm₂) x

/-- **Item 4.** Product formula for `V_m`-valued `C²` fields, a.e., assuming that `I + iM₁`
preserves `γ_E`-null sets (which cannot be dropped: `ramerDiv M₂` is only defined a.e.). -/
theorem ramerJac_compField_ae {m : ℕ}
    (M₁ M₂ : S.E → S.H)
    (h₁ : ContDiff ℝ 2 M₁) (h₂ : ContDiff ℝ 2 M₂)
    (hm₁ : ∀ x, S.headProj m (M₁ x) = M₁ x) (hm₂ : ∀ x, S.headProj m (M₂ x) = M₂ x)
    (hnull : Measure.QuasiMeasurePreserving (S.TM M₁) S.γE S.γE) :
    ∀ᵐ x ∂S.γE,
      S.ramerJac (S.compField M₁ M₂) x =
        S.ramerJac M₂ (S.TM M₁ x) * S.ramerJac M₁ x := by
  have h12 := S.contDiff_compField M₁ M₂ h₁ h₂
  have hm12 := S.headProj_compField M₁ M₂ hm₁ hm₂
  have a12 := S.ramerDiv_coordE_ae_eq _ h12 hm12
  have a1 := S.ramerDiv_coordE_ae_eq _ h₁ hm₁
  have a2 := hnull.ae (S.ramerDiv_coordE_ae_eq _ h₂ hm₂)
  filter_upwards [a12, a1, a2] with x x12 x1 x2
  have := S.ramerJE_compField M₁ M₂ (h₁.of_le (by norm_num)) (h₂.of_le (by norm_num))
    hm₁ hm₂ x
  rw [ramerJac, ramerJac, ramerJac, S.ramerJE_eq, S.ramerJE_eq, S.ramerJE_eq, x12, x1, x2]
  rw [S.ramerJE_eq, S.ramerJE_eq, S.ramerJE_eq] at this
  exact this

end General

end NlsGge.Ramer.General.RamerSetting
