import Mathlib
import NlsGge.Ramer.General.RamerLocalLowerBoundAG

/-!
# R10-P4 (part B), generalized (GE8b): the Jacobian chain for `T₂ ∘ Π' ∘ S ∘ T₁`

Adapted from `NlsGge/Ramer/RamerLocalLowerBoundB.lean` over a `RamerSetting S`.  Dictionary as in
`RamerLocalLowerBoundAG`; moreover `ramer_lemma_5_4_eventually c s hs ↦ S.ramer_lemma_5_4_eventually`,
`hT_TM_const c s hs ↦ S.hT_TM_const`, `hTk_TM_const_eventually ↦ S.hTk_TM_const_eventually`,
`quasiMeasurePreserving_add_inclE c s hs ↦ S.quasiMeasurePreserving_add_incl`,
`NullPresOn c s hs ↦ S.NullPresOn`, `TM_compField ↦ S.TM_compField`.
`NullOn` is generic and lives in `NlsGge.Ramer.Gen`.  No isotropy is used.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped Topology ENNReal

namespace NlsGge.Ramer.Gen

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
end NlsGge.Ramer.Gen

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant NlsGge.Ramer NlsGge.Ramer.Gen

variable (S : NlsGge.Ramer.General.RamerSetting)

/-- The assembled field `F_a = e₁ + F' ∘ T₁`, `F' = L + F'' ∘ S`, `F'' = G + Â ∘ Π`.
(Old: `fieldFa`.) -/
def fieldFa (e₁ : S.H)
    (L G Â : S.E → S.H) : S.E → S.H :=
  (fun _ => e₁) + (L + (G + Â ∘ S.TM G) ∘ S.TM L) ∘ S.TM (fun _ => e₁)

theorem TM_add_comp (M₁ M₂ : S.E → S.H) :
    S.TM (M₁ + M₂ ∘ S.TM M₁) = S.TM M₂ ∘ S.TM M₁ :=
  S.TM_compField M₁ M₂

theorem TM_fieldFa (e₁ : S.H)
    (L G Â : S.E → S.H) (x : S.E) :
    S.TM (S.fieldFa e₁ L G Â) x =
      S.TM Â (S.TM G (S.TM L (x + S.incl e₁))) := by
  unfold fieldFa
  rw [S.TM_add_comp, S.TM_add_comp, S.TM_add_comp]
  rfl

theorem contDiff_fieldFa (e₁ : S.H)
    {L G Â : S.E → S.H} (hL : ContDiff ℝ 2 L) (hG : ContDiff ℝ 2 G)
    (hÂ : ContDiff ℝ 2 Â) : ContDiff ℝ 2 (S.fieldFa e₁ L G Â) := by
  unfold fieldFa
  have h1 : ContDiff ℝ 2 (G + Â ∘ S.TM G) := hG.add (hÂ.comp (S.contDiff_TM G hG))
  have h2 : ContDiff ℝ 2 (L + (G + Â ∘ S.TM G) ∘ S.TM L) :=
    hL.add (h1.comp (S.contDiff_TM L hL))
  exact contDiff_const.add (h2.comp (S.contDiff_TM _ contDiff_const))

/-- The Jacobian chain: `J_{F_a}(x) = J_Â(Π b) J_G(b) J_L(a) J_{τ}(x)` a.e. on `V`,
`a = x + i e₁`, `b = S a`. (Old: `chain_ae`.) -/
theorem chain_ae (e₁ : S.H)
    {L G Â : S.E → S.H} (hL : ContDiff ℝ 2 L) (hG : ContDiff ℝ 2 G)
    (hÂ : ContDiff ℝ 2 Â) {r : ℝ} {V : Set S.E} (hV : IsOpen V)
    (hVa : ∀ x ∈ V, x + S.incl e₁ ∈ ball (0 : S.E) r)
    (hLn : S.NullPresOn L (ball (0 : S.E) r))
    (hLnk : ∀ᶠ k in atTop, S.NullPresOn (S.projField k L) (ball (0 : S.E) r))
    (hGn : S.NullPresOn G (ball (0 : S.E) r))
    (hGnk : ∀ᶠ k in atTop, S.NullPresOn (S.projField k G) (ball (0 : S.E) r)) :
    ∀ᵐ x ∂S.γE, x ∈ V →
      S.TM L (x + S.incl e₁) ∈ ball (0 : S.E) r →
      S.ramerJac (S.fieldFa e₁ L G Â) x =
        S.ramerJac Â (S.TM G (S.TM L (x + S.incl e₁))) *
          S.ramerJac G (S.TM L (x + S.incl e₁)) *
          S.ramerJac L (x + S.incl e₁) *
          S.ramerJac (fun _ => e₁) x := by
  set γ := S.γE with hγ
  have hG' : ContDiff ℝ 2 (G + Â ∘ S.TM G) := hG.add (hÂ.comp (S.contDiff_TM G hG))
  have J3 := S.ramer_lemma_5_4_eventually _ isOpen_ball G Â hG hÂ hGn hGnk
  have J2 := S.ramer_lemma_5_4_eventually _ isOpen_ball L _ hL hG' hLn hLnk
  have hF' : ContDiff ℝ 2 (L + (G + Â ∘ S.TM G) ∘ S.TM L) :=
    hL.add (hG'.comp (S.contDiff_TM L hL))
  have J1 := S.ramer_lemma_5_4_eventually V hV (fun _ => e₁)
    (L + (G + Â ∘ S.TM G) ∘ S.TM L) contDiff_const hF' (S.hT_TM_const e₁ V)
    (S.hTk_TM_const_eventually e₁ V)
  -- transfer `J3` through `S` on `ball r`
  have J3' := Gen.ae_on_comp (T := S.TM L) (U := ball (0 : S.E) r)
    hLn (P := fun b => b ∈ ball (0 : S.E) r →
      S.ramerJac (G + Â ∘ S.TM G) b =
        S.ramerJac Â (S.TM G b) * S.ramerJac G b) J3
  -- combine `J2`, `J3'` on `ball r`
  have J23 : ∀ᵐ a ∂γ, a ∈ ball (0 : S.E) r →
      S.TM L a ∈ ball (0 : S.E) r →
      S.ramerJac (L + (G + Â ∘ S.TM G) ∘ S.TM L) a =
        S.ramerJac Â (S.TM G (S.TM L a)) * S.ramerJac G (S.TM L a) *
          S.ramerJac L a := by
    filter_upwards [J2, J3'] with a h2 h3 ha hb
    rw [h2 ha, h3 ha hb]
  have J23' := (S.quasiMeasurePreserving_add_incl e₁).ae J23
  filter_upwards [J1, J23'] with x h1 h23 hxV hb
  have ha := hVa x hxV
  rw [show S.fieldFa e₁ L G Â = (fun _ => e₁) + (L + (G + Â ∘ S.TM G) ∘ S.TM L) ∘
    S.TM (fun _ => e₁) from rfl, h1 hxV]
  show S.ramerJac (L + (G + Â ∘ S.TM G) ∘ S.TM L) (x + S.incl e₁) * _ = _
  rw [h23 ha hb]

end NlsGge.Ramer.General.RamerSetting
