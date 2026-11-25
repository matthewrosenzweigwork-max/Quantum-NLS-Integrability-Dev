import NlsGge.Ramer.RamerLocalLowerBoundA

/-!
# R10-P4 (part B): the Jacobian chain for `T₂ ∘ Π' ∘ S ∘ T₁`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped Topology ENNReal

namespace NlsGge.Ramer

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant

section Chain

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

/-- Null-set preservation of a map `Φ` on a set `A`. -/
def NullOn {X : Type*} [MeasurableSpace X] (μ : Measure X) (Φ : X → X) (A : Set X) : Prop :=
  ∀ N : Set X, μ N = 0 → μ (A ∩ Φ ⁻¹' N) = 0

theorem NullOn.comp {X : Type*} [MeasurableSpace X] {μ : Measure X} {Φ₁ Φ₂ : X → X}
    {A₁ A₂ : Set X} (h₁ : NullOn μ Φ₁ A₁) (h₂ : NullOn μ Φ₂ A₂) (hA : ∀ x ∈ A₁, Φ₁ x ∈ A₂) :
    NullOn μ (Φ₂ ∘ Φ₁) A₁ := by
  intro N hN
  refine measure_mono_null ?_ (h₁ _ (h₂ N hN))
  rintro x ⟨hx1, hx2⟩
  exact ⟨hx1, hA x hx1, hx2⟩

theorem NullOn.mono {X : Type*} [MeasurableSpace X] {μ : Measure X} {Φ : X → X}
    {A A' : Set X} (h : NullOn μ Φ A) (hA : A' ⊆ A) : NullOn μ Φ A' := fun N hN =>
  measure_mono_null (inter_subset_inter_left _ hA) (h N hN)

theorem NullOn.congr {X : Type*} [MeasurableSpace X] {μ : Measure X} {Φ Φ' : X → X}
    {A : Set X} (h : NullOn μ Φ A) (hΦ : EqOn Φ Φ' A) : NullOn μ Φ' A := fun N hN =>
  measure_mono_null (fun x (hx : x ∈ A ∩ Φ' ⁻¹' N) =>
    (⟨hx.1, by simpa [hΦ hx.1] using hx.2⟩ : x ∈ A ∩ Φ ⁻¹' N)) (h N hN)

variable {c s}

/-- The assembled field `F_a = e₁ + F' ∘ T₁`, `F' = L + F'' ∘ S`, `F'' = G + Â ∘ Π`. -/
def fieldFa (hs : (1 : ℝ) / 2 < s) (e₁ : ActualCM c)
    (L G Â : FullWeightedHilbert c s → ActualCM c) : FullWeightedHilbert c s → ActualCM c :=
  (fun _ => e₁) + (L + (G + Â ∘ TM c s hs G) ∘ TM c s hs L) ∘ TM c s hs (fun _ => e₁)

theorem TM_add_comp (hs : (1 : ℝ) / 2 < s) (M₁ M₂ : FullWeightedHilbert c s → ActualCM c) :
    TM c s hs (M₁ + M₂ ∘ TM c s hs M₁) = TM c s hs M₂ ∘ TM c s hs M₁ :=
  TM_compField c s hs M₁ M₂

theorem TM_fieldFa (hs : (1 : ℝ) / 2 < s) (e₁ : ActualCM c)
    (L G Â : FullWeightedHilbert c s → ActualCM c) (x : FullWeightedHilbert c s) :
    TM c s hs (fieldFa hs e₁ L G Â) x =
      TM c s hs Â (TM c s hs G (TM c s hs L (x + inclE c s hs e₁))) := by
  unfold fieldFa
  rw [TM_add_comp, TM_add_comp, TM_add_comp]
  rfl

theorem contDiff_fieldFa (hs : (1 : ℝ) / 2 < s) (e₁ : ActualCM c)
    {L G Â : FullWeightedHilbert c s → ActualCM c} (hL : ContDiff ℝ 2 L) (hG : ContDiff ℝ 2 G)
    (hÂ : ContDiff ℝ 2 Â) : ContDiff ℝ 2 (fieldFa hs e₁ L G Â) := by
  unfold fieldFa
  have h1 : ContDiff ℝ 2 (G + Â ∘ TM c s hs G) := hG.add (hÂ.comp (contDiff_TM c s hs G hG))
  have h2 : ContDiff ℝ 2 (L + (G + Â ∘ TM c s hs G) ∘ TM c s hs L) :=
    hL.add (h1.comp (contDiff_TM c s hs L hL))
  exact contDiff_const.add (h2.comp (contDiff_TM c s hs _ contDiff_const))

/-- The Jacobian chain: `J_{F_a}(x) = J_Â(Π b) J_G(b) J_L(a) J_{τ}(x)` a.e. on `V`,
`a = x + i e₁`, `b = S a`. -/
theorem chain_ae (hs : (1 : ℝ) / 2 < s) (e₁ : ActualCM c)
    {L G Â : FullWeightedHilbert c s → ActualCM c} (hL : ContDiff ℝ 2 L) (hG : ContDiff ℝ 2 G)
    (hÂ : ContDiff ℝ 2 Â) {r : ℝ} {V : Set (FullWeightedHilbert c s)} (hV : IsOpen V)
    (hVa : ∀ x ∈ V, x + inclE c s hs e₁ ∈ ball (0 : FullWeightedHilbert c s) r)
    (hLn : NullPresOn c s hs L (ball (0 : FullWeightedHilbert c s) r))
    (hLnk : ∀ᶠ k in atTop, NullPresOn c s hs (projField k L) (ball (0 : FullWeightedHilbert c s) r))
    (hGn : NullPresOn c s hs G (ball (0 : FullWeightedHilbert c s) r))
    (hGnk : ∀ᶠ k in atTop, NullPresOn c s hs (projField k G) (ball (0 : FullWeightedHilbert c s) r)) :
    ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s), x ∈ V →
      TM c s hs L (x + inclE c s hs e₁) ∈ ball (0 : FullWeightedHilbert c s) r →
      ramerJac c s hs (fieldFa hs e₁ L G Â) x =
        ramerJac c s hs Â (TM c s hs G (TM c s hs L (x + inclE c s hs e₁))) *
          ramerJac c s hs G (TM c s hs L (x + inclE c s hs e₁)) *
          ramerJac c s hs L (x + inclE c s hs e₁) *
          ramerJac c s hs (fun _ => e₁) x := by
  set γ := NlsGge.Measure.fullWeightedSequenceGaussian c s with hγ
  have hG' : ContDiff ℝ 2 (G + Â ∘ TM c s hs G) := hG.add (hÂ.comp (contDiff_TM c s hs G hG))
  have J3 := ramer_lemma_5_4_eventually c s hs _ isOpen_ball G Â hG hÂ hGn hGnk
  have J2 := ramer_lemma_5_4_eventually c s hs _ isOpen_ball L _ hL hG' hLn hLnk
  have hF' : ContDiff ℝ 2 (L + (G + Â ∘ TM c s hs G) ∘ TM c s hs L) :=
    hL.add (hG'.comp (contDiff_TM c s hs L hL))
  have J1 := ramer_lemma_5_4_eventually c s hs V hV (fun _ => e₁)
    (L + (G + Â ∘ TM c s hs G) ∘ TM c s hs L) contDiff_const hF' (hT_TM_const c s hs e₁ V)
    (hTk_TM_const_eventually c s hs e₁ V)
  -- transfer `J3` through `S` on `ball r`
  have J3' := ae_on_comp (T := TM c s hs L) (U := ball (0 : FullWeightedHilbert c s) r)
    hLn (P := fun b => b ∈ ball (0 : FullWeightedHilbert c s) r →
      ramerJac c s hs (G + Â ∘ TM c s hs G) b =
        ramerJac c s hs Â (TM c s hs G b) * ramerJac c s hs G b) J3
  -- combine `J2`, `J3'` on `ball r`
  have J23 : ∀ᵐ a ∂γ, a ∈ ball (0 : FullWeightedHilbert c s) r →
      TM c s hs L a ∈ ball (0 : FullWeightedHilbert c s) r →
      ramerJac c s hs (L + (G + Â ∘ TM c s hs G) ∘ TM c s hs L) a =
        ramerJac c s hs Â (TM c s hs G (TM c s hs L a)) * ramerJac c s hs G (TM c s hs L a) *
          ramerJac c s hs L a := by
    filter_upwards [J2, J3'] with a h2 h3 ha hb
    rw [h2 ha, h3 ha hb]
  have J23' := (quasiMeasurePreserving_add_inclE c s hs e₁).ae J23
  filter_upwards [J1, J23'] with x h1 h23 hxV hb
  have ha := hVa x hxV
  rw [show fieldFa hs e₁ L G Â = (fun _ => e₁) + (L + (G + Â ∘ TM c s hs G) ∘ TM c s hs L) ∘
    TM c s hs (fun _ => e₁) from rfl, h1 hxV]
  show ramerJac c s hs (L + (G + Â ∘ TM c s hs G) ∘ TM c s hs L) (x + inclE c s hs e₁) * _ = _
  rw [h23 ha hb]

#print axioms chain_ae

end Chain

end NlsGge.Ramer
