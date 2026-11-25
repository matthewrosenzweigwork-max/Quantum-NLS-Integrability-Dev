import QuantumNLS.TerraMultiRound25Contour

/-! Sign-flip contour covariance with the Neumann side conditions discharged. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
namespace QuantumNLS.LocalSpectral.Round25
open QuantumNLS.Local002 QuantumNLS.LocalSpectral.Round24

variable {L κ r : ℝ}

/-- The operator graph depends only on the almost-everywhere potential. -/
theorem graph_congr_ae {u v : ℝ → ℂ} (h : u =ᵐ[μI L] v) (σ : ℤˣ) :
    LuGraph L κ u σ = LuGraph L κ v σ := by
  ext p
  constructor <;> intro hp
  · rcases hp with ⟨g, d, hgd, hb, ho⟩
    refine ⟨g, d, hgd, hb, ?_⟩
    filter_upwards [ho, h] with x hx huv
    simpa [huv] using hx
  · rcases hp with ⟨g, d, hgd, hb, ho⟩
    refine ⟨g, d, hgd, hb, ?_⟩
    filter_upwards [ho, h] with x hx huv
    simpa [huv] using hx

theorem isResolvent_congr_ae {u v : ℝ → ℂ} (h : u =ᵐ[μI L] v)
    (σ : ℤˣ) (z : ℂ) (R : H2 L →L[ℂ] H2 L) :
    IsResolvent L κ u σ z R ↔ IsResolvent L κ v σ z R := by
  unfold IsResolvent
  rw [graph_congr_ae h σ]

theorem resolvent_congr_ae {u v : ℝ → ℂ} (h : u =ᵐ[μI L] v)
    (σ : ℤˣ) (z : ℂ) : resolvent L κ u σ z = resolvent L κ v σ z := by
  unfold resolvent
  have heq : (∃ R, IsResolvent L κ u σ z R) ↔ ∃ R, IsResolvent L κ v σ z R := by
    simp only [isResolvent_congr_ae h σ z]
  by_cases hu : ∃ R, IsResolvent L κ u σ z R
  · have hv := heq.mp hu
    rw [dite_eq_left hu, dite_eq_left hv]
    exact IsResolvent.unique ((isResolvent_congr_ae h σ z _).mp hu.choose_spec) hv.choose_spec
  · have hv : ¬ ∃ R, IsResolvent L κ v σ z R := fun hv => hu (heq.mpr hv)
    simp [hu, hv]

/-- Both contour symmetries hold without separate existence or integrability
assumptions throughout the explicit Neumann ball. -/
theorem contour_parity (hyp : FreeResolventHyp L κ) (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) (n : ℤ) (u : Lp ℂ 2 (μI L))
    (hq : qpar κ L r u < 1) (x : H2 L) :
    rieszProj L κ (fun t => -(u : ℝ → ℂ) t) (parity n) n r (parityOp L x) =
      parityOp L (rieszProj L κ (u : ℝ → ℂ) (parity n) n r x) ∧
    dressedIntegral L κ (fun t => -(u : ℝ → ℂ) t) n r (parityOp L x) =
      parityOp L (dressedIntegral L κ (u : ℝ → ℂ) n r x) := by
  have hneg : ((-u : Lp ℂ 2 (μI L)) : ℝ → ℂ) =ᵐ[μI L] fun t => -(u : ℝ → ℂ) t := Lp.coeFn_neg u
  have hqneg : qpar κ L r (-u) < 1 := by simpa [qpar] using hq
  have hR : ∀ z ∈ sphere (center L n) r, ∃ R, IsResolvent L κ (u : ℝ → ℂ) (parity n) z R :=
    fun z hz => (contour_resolvent hyp hr hr2 n u hq z hz).imp (fun _ h => h.1)
  have hS : ∀ z ∈ sphere (center L n) r, ∃ R, IsResolvent L κ (fun t => -(u : ℝ → ℂ) t) (parity n) z R := by
    intro z hz
    obtain ⟨R, hR, _⟩ := contour_resolvent hyp hr hr2 n (-u) hqneg z hz
    exact ⟨R, (isResolvent_congr_ae hneg _ _ _).mp hR⟩
  have hi := contour_integrable hyp hr hr2 n u hq
  have hj : CircleIntegrable (fun z => resolvent L κ (fun t => -(u : ℝ → ℂ) t) (parity n) z) (center L n) r := by
    have hf : (fun z => resolvent L κ (fun t => -(u : ℝ → ℂ) t) (parity n) z) =
        (fun z => resolvent L κ ((-u : Lp ℂ 2 (μI L)) : ℝ → ℂ) (parity n) z) := by
      funext z
      exact (resolvent_congr_ae hneg _ _).symm
    rw [hf]
    exact contour_integrable hyp hr hr2 n (-u) hqneg
  exact ⟨riesz_parity L κ _ _ n r hr.le hR hS hi hj x,
    dressed_parity L κ _ n r hr.le hR hS hi hj x⟩

end QuantumNLS.LocalSpectral.Round25
#print axioms QuantumNLS.LocalSpectral.Round25.graph_congr_ae
#print axioms QuantumNLS.LocalSpectral.Round25.isResolvent_congr_ae
#print axioms QuantumNLS.LocalSpectral.Round25.resolvent_congr_ae
#print axioms QuantumNLS.LocalSpectral.Round25.contour_parity
