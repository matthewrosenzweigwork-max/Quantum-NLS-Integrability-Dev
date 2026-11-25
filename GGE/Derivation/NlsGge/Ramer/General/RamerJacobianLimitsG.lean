import Mathlib
import NlsGge.Ramer.General.RamerJacobianHeadG
import NlsGge.Ramer.General.RamerStep8bG

/-!
# R9b, generalized (GD11): divergence convergences and linearity

Adapted from `NlsGge/Ramer/RamerJacobianLimits.lean` over a `RamerSetting S`.  Dictionary:
`ramerA c s hs0 ↦ S.ramerA`, `ramerSum ↦ S.ramerSum`, `ramerDiv ↦ S.ramerDiv`,
`ramerJac ↦ S.ramerJac`, `TM ↦ S.TM`, `headProj c k ↦ S.headProj k`, `inclE ↦ S.incl`,
`hsDerivH ↦ S.hsDerivH`, `coordE ↦ S.coordE`, `fullWeightSequenceGaussian c.val ↦ S.γ`,
`headPt c m z ↦ S.headPt m z`, `fullWeightedSequenceRealization ↦ S.R`.
No norm of `E` is used.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal RealInnerProductSpace

namespace NlsGge.Ramer.Gen

/-! ### Subsequences of in-measure convergent sequences -/

theorem exists_subseq_ae_of_tendstoInMeasure {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {g : α → ℝ} (h : TendstoInMeasure μ f atTop g) {ψ : ℕ → ℕ}
    (hψ : StrictMono ψ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ x ∂μ, Tendsto (fun j => f (ψ (φ j)) x) atTop (𝓝 (g x)) := by
  have h' : TendstoInMeasure μ (fun n => f (ψ n)) atTop g :=
    fun ε hε => (h ε hε).comp hψ.tendsto_atTop
  exact h'.exists_seq_tendsto_ae

end NlsGge.Ramer.Gen

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer NlsGge.Analysis.RegularizedDeterminant

section Limits

variable (S : NlsGge.Ramer.General.RamerSetting)

/-! ### Item 1: linearity -/

theorem ramerA_add (n : ℕ) (M₁ M₂ : S.E → S.H)
    (h₁ : Differentiable ℝ M₁) (h₂ : Differentiable ℝ M₂) :
    S.ramerA n (M₁ + M₂) = S.ramerA n M₁ + S.ramerA n M₂ := by
  funext z
  unfold ramerA
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have hf : fderiv ℝ (M₁ + M₂) (S.R z) = fderiv ℝ M₁ (S.R z) + fderiv ℝ M₂ (S.R z) :=
    fderiv_add (h₁ _) (h₂ _)
  rw [hf, add_apply]
  set b := weightedRealHilbertBasis S.cmWeight p
  set y := S.R z
  set u := S.incl b
  have e1 : ⟪b, M₁ y + M₂ y⟫ = ⟪b, M₁ y⟫ + ⟪b, M₂ y⟫ := inner_add_right _ _ _
  have e2 : ⟪b, fderiv ℝ M₁ y u + fderiv ℝ M₂ y u⟫ =
      ⟪b, fderiv ℝ M₁ y u⟫ + ⟪b, fderiv ℝ M₂ y u⟫ := inner_add_right _ _ _
  rw [e1, e2]
  ring

/-- **Item 1.** Linearity of the divergence, a.e. (Old: `ramerDiv_add_ae`.) -/
theorem ramerDiv_add_ae (M₁ M₂ : S.E → S.H)
    (h₁ : ContDiff ℝ 2 M₁) (h₂ : ContDiff ℝ 2 M₂) :
    S.ramerDiv (M₁ + M₂) =ᵐ[S.γ] S.ramerDiv M₁ + S.ramerDiv M₂ := by
  have h12 : ContDiff ℝ 2 (M₁ + M₂) := h₁.add h₂
  have d₁ : Differentiable ℝ M₁ := h₁.differentiable (by norm_num)
  have d₂ : Differentiable ℝ M₂ := h₂.differentiable (by norm_num)
  have s₁ := (S.ramerDiv_spec M₁ h₁).2.2
  have s₂ := (S.ramerDiv_spec M₂ h₂).2.2
  have s₁₂ := (S.ramerDiv_spec _ h12).2.2
  obtain ⟨ψ, hψ, a₁⟩ := s₁.exists_seq_tendsto_ae
  obtain ⟨φ₂, hφ₂, a₂⟩ := NlsGge.Ramer.Gen.exists_subseq_ae_of_tendstoInMeasure s₂ hψ
  obtain ⟨φ₃, hφ₃, a₃⟩ :=
    NlsGge.Ramer.Gen.exists_subseq_ae_of_tendstoInMeasure s₁₂ (hψ.comp hφ₂)
  filter_upwards [a₁, a₂, a₃] with z z₁ z₂ z₃
  have e₁ : Tendsto (fun j => S.ramerA (ψ (φ₂ (φ₃ j))) M₁ z) atTop
      (𝓝 (S.ramerDiv M₁ z)) :=
    z₁.comp ((hφ₂.comp hφ₃).tendsto_atTop)
  have e₂ : Tendsto (fun j => S.ramerA (ψ (φ₂ (φ₃ j))) M₂ z) atTop
      (𝓝 (S.ramerDiv M₂ z)) :=
    z₂.comp hφ₃.tendsto_atTop
  have e₃ : Tendsto (fun j => S.ramerA (ψ (φ₂ (φ₃ j))) (M₁ + M₂) z)
      atTop (𝓝 (S.ramerDiv (M₁ + M₂) z)) := z₃
  have e₄ := e₁.add e₂
  have : (fun j => S.ramerA (ψ (φ₂ (φ₃ j))) (M₁ + M₂) z) =
      fun j => S.ramerA (ψ (φ₂ (φ₃ j))) M₁ z + S.ramerA (ψ (φ₂ (φ₃ j))) M₂ z := by
    funext j
    rw [S.ramerA_add _ _ _ d₁ d₂]; rfl
  rw [this] at e₃
  exact tendsto_nhds_unique e₃ e₄

/-! ### Item 2: range projections -/

theorem headProj_idem (k : ℕ) (w : S.H) : S.headProj k (S.headProj k w) = S.headProj k w := by
  apply S.hcoord_ext
  intro n
  rw [S.hcoord_headProj, S.hcoord_headProj]
  split_ifs <;> rfl

theorem inner_basis_headProj (k : ℕ) (p : ℤ × Fin 2) (hp : p.1 ∈ symmetricModes k) (w : S.H) :
    ⟪weightedRealHilbertBasis S.cmWeight p, S.headProj k w⟫ =
      ⟪weightedRealHilbertBasis S.cmWeight p, w⟫ := by
  rw [S.headProj_apply, S.inner_basis_cmTrunc]; simp [hp]

/-- The projected field `P_k ∘ M`. (Old: `projField`.) -/
abbrev projField (k : ℕ) (M : S.E → S.H) : S.E → S.H := fun y => S.headProj k (M y)

theorem contDiff_projField (k : ℕ) (M : S.E → S.H) {n : ℕ∞}
    (hM : ContDiff ℝ n M) : ContDiff ℝ n (S.projField k M) :=
  (S.headProj k).contDiff.comp hM

theorem ramerA_projField (k : ℕ) (M : S.E → S.H)
    (hM : Differentiable ℝ M) :
    S.ramerA k (S.projField k M) = S.ramerA k M := by
  funext z
  unfold ramerA
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hp1 : p.1 ∈ symmetricModes k := (Finset.mem_product.1 hp).1
  have hf : fderiv ℝ (S.projField k M) (S.R z) =
      (S.headProj k).comp (fderiv ℝ M (S.R z)) :=
    ((S.headProj k).hasFDerivAt.comp _ (hM _).hasFDerivAt).fderiv
  set y := S.R z
  set b := weightedRealHilbertBasis S.cmWeight p
  set u := S.incl b
  have e1 : ⟪b, ((S.headProj k).comp (fderiv ℝ M y)) u⟫ = ⟪b, fderiv ℝ M y u⟫ :=
    S.inner_basis_headProj k p hp1 _
  have e2 : ⟪b, S.projField k M y⟫ = ⟪b, M y⟫ := S.inner_basis_headProj k p hp1 _
  rw [hf]
  erw [e1, e2]

/-- **Item 2 (divergence).** (Old: `ramerDiv_projField_subseq`.) -/
theorem ramerDiv_projField_subseq (M : S.E → S.H)
    (hM : ContDiff ℝ 2 M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ z ∂S.γ,
        (∀ j, S.ramerDiv (S.projField (φ j) M) z = S.ramerA (φ j) M z) ∧
        Tendsto (fun j => S.ramerDiv (S.projField (φ j) M) z) atTop
          (𝓝 (S.ramerDiv M z)) := by
  obtain ⟨φ, hφ, hlim⟩ := (S.ramerDiv_spec M hM).2.1
  refine ⟨φ, hφ, ?_⟩
  have hall : ∀ᵐ z ∂S.γ, ∀ j,
      S.ramerDiv (S.projField (φ j) M) z = S.ramerA (φ j) M z := by
    rw [ae_all_iff]
    intro j
    filter_upwards [S.ramerDiv_ae_eq_ramerA (m := φ j) (S.projField (φ j) M)
      (S.contDiff_projField _ M hM) (fun x => S.headProj_idem _ _)] with z hz
    rw [hz, S.ramerA_projField _ M (hM.differentiable (by norm_num))]
  filter_upwards [hall, hlim] with z h1 h2
  exact ⟨h1, h2.congr (fun j => (h1 j).symm)⟩

/-- **Item 2 (derivative and values).** (Old: `tendsto_hsDerivH_projField`.) -/
theorem tendsto_hsDerivH_projField (M : S.E → S.H)
    (hM : Differentiable ℝ M) (x : S.E) :
    Tendsto (fun k : ℕ => S.hsDerivH (S.projField k M) x) atTop (𝓝 (S.hsDerivH M x)) :=
  S.tendsto_hsDerivH_headProj M hM x

theorem tendsto_projField_apply (M : S.E → S.H) (x : S.E) :
    Tendsto (fun k : ℕ => S.projField k M x) atTop (𝓝 (M x)) :=
  S.headProj_tendsto (M x)

/-! ### Item 4: generic `J`-convergence -/

/-- (Old: `tendsto_ramerJac`.) -/
theorem tendsto_ramerJac {ι : Type*} {l : Filter ι}
    (Mj : ι → S.E → S.H) (M : S.E → S.H) (x : S.E)
    (h1 : Tendsto (fun j => Mj j x) l (𝓝 (M x)))
    (h2 : Tendsto (fun j => S.hsDerivH (Mj j) x) l (𝓝 (S.hsDerivH M x)))
    (h3 : Tendsto (fun j => S.ramerDiv (Mj j) (S.coordE x)) l
      (𝓝 (S.ramerDiv M (S.coordE x)))) :
    Tendsto (fun j => S.ramerJac (Mj j) x) l (𝓝 (S.ramerJac M x)) := by
  simp only [ramerJac_eq]
  have d : Tendsto (fun j => |det2 (S.hsDerivH (Mj j) x)|) l
      (𝓝 |det2 (S.hsDerivH M x)|) :=
    ((continuous_det2.tendsto _).comp h2).abs
  have e : Tendsto (fun j => Real.exp (-(S.ramerDiv (Mj j) (S.coordE x)) -
      ‖Mj j x‖ ^ 2 / 2)) l
      (𝓝 (Real.exp (-(S.ramerDiv M (S.coordE x)) - ‖M x‖ ^ 2 / 2))) :=
    (Real.continuous_exp.tendsto _).comp
      (h3.neg.sub ((h1.norm.pow 2).div_const 2))
  exact d.mul e

/-! ### Item 3: fixed finite range, varying argument -/

/-- The field `R ∘ G ∘ T` with `R = P_m`. (Old: `rangeComp`.) -/
abbrev rangeComp (m : ℕ) (G : S.E → S.H) (T : S.E → S.E) : S.E → S.H :=
  fun y => S.headProj m (G (T y))

theorem fderiv_TM (M : S.E → S.H)
    (hM : Differentiable ℝ M) (y u : S.E) :
    fderiv ℝ (S.TM M) y u = u + S.incl (fderiv ℝ M y u) := by
  have h : HasFDerivAt (S.TM M) (ContinuousLinearMap.id ℝ _ + S.incl.comp (fderiv ℝ M y)) y :=
    (hasFDerivAt_id y).add (S.incl.hasFDerivAt.comp y (hM y).hasFDerivAt)
  rw [h.fderiv]
  rfl

theorem fderiv_rangeComp (m : ℕ) (G : S.E → S.H)
    (hG : Differentiable ℝ G) (M : S.E → S.H)
    (hM : Differentiable ℝ M) (y u : S.E) :
    fderiv ℝ (S.rangeComp m G (S.TM M)) y u =
      S.headProj m (fderiv ℝ G (S.TM M y) (u + S.incl (fderiv ℝ M y u))) := by
  have hT := S.differentiable_TM M hM
  have h : HasFDerivAt (S.rangeComp m G (S.TM M))
      ((S.headProj m).comp ((fderiv ℝ G (S.TM M y)).comp (fderiv ℝ (S.TM M) y))) y :=
    (S.headProj m).hasFDerivAt.comp y ((hG _).hasFDerivAt.comp y (hT y).hasFDerivAt)
  have e : fderiv ℝ (S.rangeComp m G (S.TM M)) y u =
      S.headProj m (fderiv ℝ G (S.TM M y) (fderiv ℝ (S.TM M) y u)) := by
    erw [h.fderiv]; rfl
  rw [e, S.fderiv_TM M hM]

theorem contDiff_rangeComp (m : ℕ) (G : S.E → S.H)
    (M : S.E → S.H) {n : ℕ∞} (hG : ContDiff ℝ n G)
    (hM : ContDiff ℝ n M) : ContDiff ℝ n (S.rangeComp m G (S.TM M)) :=
  (S.headProj m).contDiff.comp (hG.comp (S.contDiff_TM M hM))

theorem tendsto_ramerSum_rangeComp (m : ℕ)
    (G K : S.E → S.H) (hG : ContDiff ℝ 1 G) (hK : ContDiff ℝ 1 K)
    (x : S.H) (y : S.E) :
    Tendsto (fun k : ℕ => S.ramerSum m (S.rangeComp m G (S.TM (S.projField k K))) x y) atTop
      (𝓝 (S.ramerSum m (S.rangeComp m G (S.TM K)) x y)) := by
  have dG : Differentiable ℝ G := hG.differentiable one_ne_zero
  have dK : Differentiable ℝ K := hK.differentiable one_ne_zero
  have dKk : ∀ k, Differentiable ℝ (S.projField k K) := fun k =>
    (S.contDiff_projField k K hK).differentiable one_ne_zero
  have hD : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  have hTy : Tendsto (fun k : ℕ => S.TM (S.projField k K) y) atTop (𝓝 (S.TM K y)) := by
    unfold TM
    exact tendsto_const_nhds.add ((S.incl).continuous.continuousAt.tendsto.comp
      (S.tendsto_projField_apply K y))
  have hGy : Tendsto (fun k : ℕ => G (S.TM (S.projField k K) y)) atTop
      (𝓝 (G (S.TM K y))) := (hG.continuous.tendsto _).comp hTy
  have hDy : Tendsto (fun k : ℕ => fderiv ℝ G (S.TM (S.projField k K) y)) atTop
      (𝓝 (fderiv ℝ G (S.TM K y))) := (hD.tendsto _).comp hTy
  unfold ramerSum
  refine tendsto_finsetSum _ (fun p _ => ?_)
  set b := weightedRealHilbertBasis S.cmWeight p
  set u := S.incl b
  have hDK : Tendsto (fun k : ℕ => fderiv ℝ (S.projField k K) y u) atTop
      (𝓝 (fderiv ℝ K y u)) := by
    have : ∀ k, fderiv ℝ (S.projField k K) y u = S.headProj k (fderiv ℝ K y u) := by
      intro k
      have hf : fderiv ℝ (S.projField k K) y = (S.headProj k).comp (fderiv ℝ K y) :=
        ((S.headProj k).hasFDerivAt.comp _ (dK y).hasFDerivAt).fderiv
      rw [hf]; rfl
    simp only [this]
    exact S.headProj_tendsto _
  have hv : Tendsto (fun k : ℕ => u + S.incl (fderiv ℝ (S.projField k K) y u)) atTop
      (𝓝 (u + S.incl (fderiv ℝ K y u))) :=
    tendsto_const_nhds.add (S.incl.continuous.continuousAt.tendsto.comp hDK)
  have hw : Tendsto (fun k : ℕ => fderiv ℝ G (S.TM (S.projField k K) y)
      (u + S.incl (fderiv ℝ (S.projField k K) y u))) atTop
      (𝓝 (fderiv ℝ G (S.TM K y) (u + S.incl (fderiv ℝ K y u)))) :=
    (isBoundedBilinearMap_apply.continuous.tendsto
      (fderiv ℝ G (S.TM K y), u + S.incl (fderiv ℝ K y u))).comp (hDy.prodMk_nhds hv)
  have hP := (S.headProj m).continuous
  have t1 : Tendsto (fun k : ℕ => S.rangeComp m G (S.TM (S.projField k K)) y) atTop
      (𝓝 (S.rangeComp m G (S.TM K) y)) := (hP.tendsto _).comp hGy
  have t2 : Tendsto (fun k : ℕ => fderiv ℝ (S.rangeComp m G (S.TM (S.projField k K))) y u)
      atTop (𝓝 (fderiv ℝ (S.rangeComp m G (S.TM K)) y u)) := by
    simp only [S.fderiv_rangeComp m G dG _ (dKk _), S.fderiv_rangeComp m G dG _ dK]
    exact (hP.tendsto _).comp hw
  exact (tendsto_const_nhds.mul (tendsto_const_nhds.inner t1)).sub (tendsto_const_nhds.inner t2)

/-- **Item 3.** (Old: `ramerDiv_rangeComp_tendsto_ae`.) -/
theorem ramerDiv_rangeComp_tendsto_ae (m : ℕ)
    (G K : S.E → S.H) (hG : ContDiff ℝ 2 G) (hK : ContDiff ℝ 2 K) :
    ∀ᵐ z ∂S.γ,
      Tendsto (fun k : ℕ => S.ramerDiv (S.rangeComp m G (S.TM (S.projField k K))) z) atTop
        (𝓝 (S.ramerDiv (S.rangeComp m G (S.TM K)) z)) := by
  have hall : ∀ᵐ z ∂S.γ, ∀ k : ℕ,
      S.ramerDiv (S.rangeComp m G (S.TM (S.projField k K))) z =
        S.ramerA m (S.rangeComp m G (S.TM (S.projField k K))) z := by
    rw [ae_all_iff]
    intro k
    exact S.ramerDiv_ae_eq_ramerA _
      (S.contDiff_rangeComp m G _ hG (S.contDiff_projField k K hK))
      (fun x => S.headProj_idem _ _)
  have h0 := S.ramerDiv_ae_eq_ramerA (S.rangeComp m G (S.TM K))
    (S.contDiff_rangeComp m G K hG hK) (fun x => S.headProj_idem _ _)
  filter_upwards [hall, h0] with z h1 h2
  rw [h2]
  have := S.tendsto_ramerSum_rangeComp m G K (hG.of_le (by norm_num)) (hK.of_le (by norm_num))
    (S.headPt m z : S.H) (S.R z)
  simp only [h1]
  exact this

end Limits

end NlsGge.Ramer.General.RamerSetting
