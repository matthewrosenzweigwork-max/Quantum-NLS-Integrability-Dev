import Mathlib
import NlsGge.Ramer.FibreBridge
import NlsGge.Ramer.RamerStep2Fibrewise
import NlsGge.Ramer.RamerStep8a
import NlsGge.Ramer.RamerApproximant
import NlsGge.Ramer.SpaceTransfer
import NlsGge.Ramer.RamerDensity
import NlsGge.Ramer.DivergenceIdentificationGlobal
import NlsGge.Ramer.LinearDecomposition
import NlsGge.Ramer.RamerFiniteChainRule

/-!
# R9a: the Ramer Jacobian of a general field, and head-valued fields

See `RamerJacobianHead.md`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal RealInnerProductSpace

namespace NlsGge.Ramer

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant

section General

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

open Classical in
/-- A fixed choice of the L3b divergence of a `C²` field (and `0` for other fields). -/
def ramerDiv (hs : (1 : ℝ) / 2 < s) (M : FullWeightedHilbert c s → ActualCM c) :
    (ℤ → ℂ) → ℝ :=
  if h : ContDiff ℝ 2 M then Classical.choose (divergence_identification c s hs M h) else 0

/-- Ramer's `J^{I+M}`. -/
def ramerJac (hs : (1 : ℝ) / 2 < s) (M : FullWeightedHilbert c s → ActualCM c)
    (x : FullWeightedHilbert c s) : ℝ :=
  ramerJE c s hs M (ramerDiv c s hs M) x

theorem ramerJac_eq (hs : (1 : ℝ) / 2 < s) (M : FullWeightedHilbert c s → ActualCM c)
    (x : FullWeightedHilbert c s) :
    ramerJac c s hs M x =
      |det2 (hsDerivH c s hs M x)| *
        Real.exp (-(ramerDiv c s hs M (coordE c s x)) - ‖M x‖ ^ 2 / 2) :=
  ramerJE_eq c s hs _ _ x

theorem ramerDiv_spec (hs : (1 : ℝ) / 2 < s) (M : FullWeightedHilbert c s → ActualCM c)
    (hM : ContDiff ℝ 2 M) :
    AEStronglyMeasurable (ramerDiv c s hs M) (NlsGge.Measure.fullWeightSequenceGaussian c.val) ∧
    (∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
        Tendsto (fun j => ramerA c s (zero_le_of_half_lt hs) (φ j) M z) atTop
          (𝓝 (ramerDiv c s hs M z))) ∧
    TendstoInMeasure (NlsGge.Measure.fullWeightSequenceGaussian c.val)
        (fun n => ramerA c s (zero_le_of_half_lt hs) n M) atTop (ramerDiv c s hs M) := by
  have h := Classical.choose_spec (divergence_identification c s hs M hM)
  unfold ramerDiv
  rw [dif_pos hM]
  exact ⟨h.1, h.2.2.2.1, h.2.2.2.2⟩

/-! ### Item 1: stabilization -/

variable {c s}

/-- Pairing with a basis vector outside `W m` kills `P_m`-fixed vectors. -/
theorem inner_basis_of_headFixed (m : ℕ) (p : ℤ × Fin 2) (hp : p.1 ∉ symmetricModes m)
    (w : ActualCM c) (hw : headProj c m w = w) :
    ⟪weightedRealHilbertBasis (cmModeWeight c) p, w⟫ = 0 := by
  rw [← hw, headProj_apply, inner_basis_cmTrunc, if_neg hp]

theorem fderiv_headFixed (m : ℕ) (M : FullWeightedHilbert c s → ActualCM c)
    (hMd : Differentiable ℝ M) (hm : ∀ x, headProj c m (M x) = M x)
    (x : FullWeightedHilbert c s) (v : FullWeightedHilbert c s) :
    headProj c m (fderiv ℝ M x v) = fderiv ℝ M x v := by
  have hM' : M = fun y => headProj c m (M y) := funext fun y => (hm y).symm
  have h1 : fderiv ℝ M x = fderiv ℝ (fun y => headProj c m (M y)) x :=
    congrArg (fun f => fderiv ℝ f x) hM'
  have h2 : fderiv ℝ (fun y => headProj c m (M y)) x = (headProj c m).comp (fderiv ℝ M x) :=
    ((headProj c m).hasFDerivAt.comp x (hMd x).hasFDerivAt).fderiv
  exact (congrArg (fun L => L v) (h1.trans h2)).symm

/-- **Item 1.** For a `V_m`-valued `C¹` field, `ramerA n M = ramerA m M` for `n ≥ m`. -/
theorem ramerA_eq_of_headValued (hs0 : 0 ≤ s) {m : ℕ} (M : FullWeightedHilbert c s → ActualCM c)
    (hMd : Differentiable ℝ M) (hm : ∀ x, headProj c m (M x) = M x) {n : ℕ} (hmn : m ≤ n) :
    ramerA c s hs0 n M = ramerA c s hs0 m M := by
  funext z
  unfold ramerA
  have hsub : basisIndex m ⊆ basisIndex n := by
    intro p hp
    rw [Finset.mem_product] at hp ⊢
    exact ⟨symmetricModes_mono hmn hp.1, hp.2⟩
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl (fun p hp => ?_)
    have hp1 : p.1 ∈ symmetricModes m := (Finset.mem_product.1 hp).1
    have : ⟪weightedRealHilbertBasis (cmModeWeight c) p, ((headPt c n z : actualCMHead c n) : ActualCM c)⟫ =
        ⟪weightedRealHilbertBasis (cmModeWeight c) p, ((headPt c m z : actualCMHead c m) : ActualCM c)⟫ := by
      apply inner_basis_congr
      rw [cmCoord_headPt, cmCoord_headPt, if_pos (symmetricModes_mono hmn hp1), if_pos hp1]
    have this' : ⟪((headPt c n z : actualCMHead c n) : ActualCM c),
        weightedRealHilbertBasis (cmModeWeight c) p⟫ =
        ⟪((headPt c m z : actualCMHead c m) : ActualCM c),
        weightedRealHilbertBasis (cmModeWeight c) p⟫ :=
      (real_inner_comm _ _).symm.trans (this.trans (real_inner_comm _ _))
    rw [this']
  · intro p hpn hpm
    have hp1 : p.1 ∉ symmetricModes m := fun h => hpm (Finset.mem_product.2 ⟨h, Finset.mem_univ _⟩)
    rw [inner_basis_of_headFixed m p hp1 _ (hm _),
      inner_basis_of_headFixed m p hp1 _ (fderiv_headFixed m M hMd hm _ _)]
    simp

variable (c s)

/-- **Item 1 (a.e. form).** `ramerDiv M = ramerA m M` `γ`-a.e. -/
theorem ramerDiv_ae_eq_ramerA (hs : (1 : ℝ) / 2 < s) {m : ℕ}
    (M : FullWeightedHilbert c s → ActualCM c) (hM : ContDiff ℝ 2 M)
    (hm : ∀ x, headProj c m (M x) = M x) :
    ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      ramerDiv c s hs M z = ramerA c s (zero_le_of_half_lt hs) m M z := by
  obtain ⟨φ, hφ, hlim⟩ := (ramerDiv_spec c s hs M hM).2.1
  filter_upwards [hlim] with z hz
  have hev : ∀ᶠ j in atTop,
      ramerA c s (zero_le_of_half_lt hs) (φ j) M z = ramerA c s (zero_le_of_half_lt hs) m M z := by
    filter_upwards [eventually_ge_atTop m] with j hj
    have := ramerA_eq_of_headValued (zero_le_of_half_lt hs) M
      (hM.differentiable (by norm_num)) hm ((hj.trans (hφ.id_le j)))
    exact congrFun this z
  exact tendsto_nhds_unique hz (tendsto_const_nhds.congr' (hev.mono fun j h => h.symm))

/-- **Item 1 on `E`.** -/
theorem ramerDiv_coordE_ae_eq (hs : (1 : ℝ) / 2 < s) {m : ℕ}
    (M : FullWeightedHilbert c s → ActualCM c) (hM : ContDiff ℝ 2 M)
    (hm : ∀ x, headProj c m (M x) = M x) :
    ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s),
      ramerDiv c s hs M (coordE c s x) = ramerA c s (zero_le_of_half_lt hs) m M (coordE c s x) :=
  ae_of_ae_coordE c s hs (ramerDiv_ae_eq_ramerA c s hs M hM hm)

/-! ### Item 2: the fibre form -/

/-- The map `T_M = I + iM`. -/
def TM (hs : (1 : ℝ) / 2 < s) (M : FullWeightedHilbert c s → ActualCM c)
    (y : FullWeightedHilbert c s) : FullWeightedHilbert c s :=
  y + inclE c s hs (M y)

theorem Sn_eq_TM (hs : (1 : ℝ) / 2 < s) {m : ℕ} (M : FullWeightedHilbert c s → ActualCM c)
    (hm : ∀ x, headProj c m (M x) = M x) : Sn c s hs m M = TM c s hs M := by
  funext y
  simp only [Sn, TM, hm]

/-- For a `V_m`-valued field, `ramerJE M (ramerA m M)` is the fibre Jacobian of `I + iM`. -/
theorem fibreJ_TM_eq (hs : (1 : ℝ) / 2 < s) {m : ℕ} (M : FullWeightedHilbert c s → ActualCM c)
    (hM : ContDiff ℝ 1 M) (hm : ∀ x, headProj c m (M x) = M x) (x : FullWeightedHilbert c s) :
    fibreJ c m (fibreMapOf c s m (TM c s hs M)) (coordE c s x) =
      ramerJE c s hs M (ramerA c s (zero_le_of_half_lt hs) m M) x := by
  rw [← Sn_eq_TM c s hs M hm, fibreJ_Sn_eq c s m hs M hM x, ramerJn]
  have e : (fun y => headProj c m (M y)) = M := funext hm
  rw [e]

/-- **Item 2.** `ramerJac M x` is the fibre Jacobian of the fibre maps of `I + iM`, a.e. -/
theorem ramerJac_ae_eq_fibreJ (hs : (1 : ℝ) / 2 < s) {m : ℕ}
    (M : FullWeightedHilbert c s → ActualCM c) (hM : ContDiff ℝ 2 M)
    (hm : ∀ x, headProj c m (M x) = M x) :
    ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s),
      ramerJac c s hs M x =
        fibreJ c m (fibreMapOf c s m (TM c s hs M)) (coordE c s x) := by
  filter_upwards [ramerDiv_coordE_ae_eq c s hs M hM hm] with x hx
  rw [fibreJ_TM_eq c s hs M (hM.of_le (by norm_num)) hm, ramerJac, ramerJE_eq, ramerJE_eq, hx]

/-! ### Item 4: product formula -/

theorem differentiable_TM (hs : (1 : ℝ) / 2 < s) (M : FullWeightedHilbert c s → ActualCM c)
    (hM : Differentiable ℝ M) : Differentiable ℝ (TM c s hs M) :=
  differentiable_id.add ((inclE c s hs).differentiable.comp hM)

theorem contDiff_TM (hs : (1 : ℝ) / 2 < s) (M : FullWeightedHilbert c s → ActualCM c)
    {k : ℕ∞} (hM : ContDiff ℝ k M) : ContDiff ℝ k (TM c s hs M) :=
  contDiff_id.add ((inclE c s hs).contDiff.comp hM)

/-- The composite field `M₁ + M₂ ∘ (I + iM₁)`. -/
def compField (hs : (1 : ℝ) / 2 < s) (M₁ M₂ : FullWeightedHilbert c s → ActualCM c)
    (x : FullWeightedHilbert c s) : ActualCM c :=
  M₁ x + M₂ (TM c s hs M₁ x)

theorem TM_compField (hs : (1 : ℝ) / 2 < s) (M₁ M₂ : FullWeightedHilbert c s → ActualCM c) :
    TM c s hs (compField c s hs M₁ M₂) = TM c s hs M₂ ∘ TM c s hs M₁ := by
  funext x
  simp only [TM, compField, Function.comp, map_add]
  abel

theorem contDiff_compField (hs : (1 : ℝ) / 2 < s) (M₁ M₂ : FullWeightedHilbert c s → ActualCM c)
    {k : ℕ∞} (h₁ : ContDiff ℝ k M₁) (h₂ : ContDiff ℝ k M₂) :
    ContDiff ℝ k (compField c s hs M₁ M₂) :=
  h₁.add (h₂.comp (contDiff_TM c s hs M₁ h₁))

theorem headProj_compField (hs : (1 : ℝ) / 2 < s) {m : ℕ}
    (M₁ M₂ : FullWeightedHilbert c s → ActualCM c)
    (h₁ : ∀ x, headProj c m (M₁ x) = M₁ x) (h₂ : ∀ x, headProj c m (M₂ x) = M₂ x)
    (x : FullWeightedHilbert c s) :
    headProj c m (compField c s hs M₁ M₂ x) = compField c s hs M₁ M₂ x := by
  simp only [compField, map_add, h₁, h₂]

theorem sameTail_TM (hs : (1 : ℝ) / 2 < s) {m : ℕ} (M : FullWeightedHilbert c s → ActualCM c)
    (hm : ∀ x, headProj c m (M x) = M x) (x : FullWeightedHilbert c s) :
    SameTail c s m (TM c s hs M x) x := by
  rw [← Sn_eq_TM c s hs M hm]
  exact sameTail_Sn c s hs m M x

/-- Fibre maps compose, for tail-fixing maps. -/
theorem fibreMapOf_comp (m : ℕ) (Φ Ψ : FullWeightedHilbert c s → FullWeightedHilbert c s)
    (hΦ : ∀ x, SameTail c s m (Φ x) x) (t : TailSpace m) :
    fibreMapOf c s m (Ψ ∘ Φ) t = fibreMapOf c s m Ψ t ∘ fibreMapOf c s m Φ t := by
  funext v
  by_cases ht : TailSummable c s m t
  · have h1 := realE_headRec_fibreMapOf c s m Φ t v ht (hΦ _)
    have e1 := realE_headRec c s m v t ht
    have e2 := realE_headRec c s m (fibreMapOf c s m Φ t v) t ht
    have hb : tailBase c s m t + headToE c s m (fibreMapOf c s m Φ t v) =
        Φ (tailBase c s m t + headToE c s m v) := by
      rw [← e1, ← e2]; exact h1
    show fibreMapOf c s m (Ψ ∘ Φ) t v = fibreMapOf c s m Ψ t (fibreMapOf c s m Φ t v)
    rw [fibreMapOf_of_summable c s m _ t v ht, fibreMapOf_of_summable c s m Ψ t _ ht, hb]
    rfl
  · show fibreMapOf c s m (Ψ ∘ Φ) t v = fibreMapOf c s m Ψ t (fibreMapOf c s m Φ t v)
    rw [fibreMapOf_of_not_summable c s m _ t _ ht, fibreMapOf_of_not_summable c s m _ t _ ht,
      fibreMapOf_of_not_summable c s m _ t _ ht]

theorem tailPt_coordE_of_sameTail (m : ℕ) (Φ : FullWeightedHilbert c s → FullWeightedHilbert c s)
    (hΦ : ∀ x, SameTail c s m (Φ x) x) (x : FullWeightedHilbert c s) :
    tailPt m (coordE c s (Φ x)) = tailPt m (coordE c s x) := by
  funext i
  exact hΦ x i.1 i.2

theorem headPt_coordE_eq_fibreMapOf (m : ℕ) (Φ : FullWeightedHilbert c s → FullWeightedHilbert c s)
    (x : FullWeightedHilbert c s) :
    headPt c m (coordE c s (Φ x)) =
      fibreMapOf c s m Φ (tailPt m (coordE c s x)) (headPt c m (coordE c s x)) := by
  rw [fibreMapOf_of_summable c s m Φ _ _ (tailSummable_coordE c s m x),
    tailBase_add_headToE c s m x]

/-- Chain rule for the fibre Jacobians of tail-fixing maps, pointwise. -/
theorem fibreJ_comp (m : ℕ) (Φ Ψ : FullWeightedHilbert c s → FullWeightedHilbert c s)
    (hΦ : ∀ x, SameTail c s m (Φ x) x)
    (hΦf : ∀ t, Differentiable ℝ (fibreMapOf c s m Φ t))
    (hΨf : ∀ t, Differentiable ℝ (fibreMapOf c s m Ψ t)) (x : FullWeightedHilbert c s) :
    fibreJ c m (fibreMapOf c s m (Ψ ∘ Φ)) (coordE c s x) =
      fibreJ c m (fibreMapOf c s m Ψ) (coordE c s (Φ x)) *
        fibreJ c m (fibreMapOf c s m Φ) (coordE c s x) := by
  unfold fibreJ
  rw [fibreMapOf_comp c s m Φ Ψ hΦ, tailPt_coordE_of_sameTail c s m Φ hΦ x,
    headPt_coordE_eq_fibreMapOf c s m Φ x]
  exact finiteRamerDensity_comp _ _ _ (hΦf _ _) (hΨf _ _)

/-- **Item 4 (exact pointwise form).** -/
theorem ramerJE_compField (hs : (1 : ℝ) / 2 < s) {m : ℕ}
    (M₁ M₂ : FullWeightedHilbert c s → ActualCM c)
    (h₁ : ContDiff ℝ 1 M₁) (h₂ : ContDiff ℝ 1 M₂)
    (hm₁ : ∀ x, headProj c m (M₁ x) = M₁ x) (hm₂ : ∀ x, headProj c m (M₂ x) = M₂ x)
    (x : FullWeightedHilbert c s) :
    ramerJE c s hs (compField c s hs M₁ M₂)
        (ramerA c s (zero_le_of_half_lt hs) m (compField c s hs M₁ M₂)) x =
      ramerJE c s hs M₂ (ramerA c s (zero_le_of_half_lt hs) m M₂) (TM c s hs M₁ x) *
        ramerJE c s hs M₁ (ramerA c s (zero_le_of_half_lt hs) m M₁) x := by
  have h12 := contDiff_compField c s hs M₁ M₂ h₁ h₂
  have hm12 := headProj_compField c s hs M₁ M₂ hm₁ hm₂
  rw [← fibreJ_TM_eq c s hs _ h12 hm12, ← fibreJ_TM_eq c s hs M₂ h₂ hm₂,
    ← fibreJ_TM_eq c s hs M₁ h₁ hm₁, TM_compField]
  have hd : ∀ {M : FullWeightedHilbert c s → ActualCM c}, ContDiff ℝ 1 M →
      (∀ x, headProj c m (M x) = M x) → ∀ t, Differentiable ℝ (fibreMapOf c s m (TM c s hs M) t) :=
    fun {M} hM hmM t => by
      rw [← Sn_eq_TM c s hs M hmM]
      exact differentiable_fibreMapOf_Sn c s m hs M (hM.differentiable one_ne_zero) t
  exact fibreJ_comp c s m _ _ (sameTail_TM c s hs M₁ hm₁)
    (hd h₁ hm₁) (hd h₂ hm₂) x

/-- **Item 4.** Product formula for `V_m`-valued `C²` fields, a.e., assuming that `I + iM₁`
preserves `γ_E`-null sets (which cannot be dropped: `ramerDiv M₂` is only defined a.e.). -/
theorem ramerJac_compField_ae (hs : (1 : ℝ) / 2 < s) {m : ℕ}
    (M₁ M₂ : FullWeightedHilbert c s → ActualCM c)
    (h₁ : ContDiff ℝ 2 M₁) (h₂ : ContDiff ℝ 2 M₂)
    (hm₁ : ∀ x, headProj c m (M₁ x) = M₁ x) (hm₂ : ∀ x, headProj c m (M₂ x) = M₂ x)
    (hnull : Measure.QuasiMeasurePreserving (TM c s hs M₁)
      (NlsGge.Measure.fullWeightedSequenceGaussian c s)
      (NlsGge.Measure.fullWeightedSequenceGaussian c s)) :
    ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s),
      ramerJac c s hs (compField c s hs M₁ M₂) x =
        ramerJac c s hs M₂ (TM c s hs M₁ x) * ramerJac c s hs M₁ x := by
  have h12 := contDiff_compField c s hs M₁ M₂ h₁ h₂
  have hm12 := headProj_compField c s hs M₁ M₂ hm₁ hm₂
  have a12 := ramerDiv_coordE_ae_eq c s hs _ h12 hm12
  have a1 := ramerDiv_coordE_ae_eq c s hs _ h₁ hm₁
  have a2 := hnull.ae (ramerDiv_coordE_ae_eq c s hs _ h₂ hm₂)
  filter_upwards [a12, a1, a2] with x x12 x1 x2
  have := ramerJE_compField c s hs M₁ M₂ (h₁.of_le (by norm_num)) (h₂.of_le (by norm_num))
    hm₁ hm₂ x
  rw [ramerJac, ramerJac, ramerJac, ramerJE_eq, ramerJE_eq, ramerJE_eq, x12, x1, x2]
  rw [ramerJE_eq, ramerJE_eq, ramerJE_eq] at this
  exact this

end General

end NlsGge.Ramer
