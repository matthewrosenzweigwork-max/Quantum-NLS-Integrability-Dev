import NlsGge.Analysis.AffineCircleDeformation
import NlsGge.GK38.StdRootBranches
import NlsGge.GK38.ActionContourGeometry

/-! Contour independence of the actual canonical complex NLS action.
Both complete isolating families use the same potential and canonical root.
The domain and genuine circle integrability are earned before comparing integrals. -/
set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory
namespace NlsGge.GK38
noncomputable section

def actionCutDomain38 (φ : PotPair) : Set ℂ := {z | z ∉ gapSegments38 φ}

def actionIntegrand38 (φ : PotPair) (z : ℂ) : ℂ :=
  z * deriv (discrim φ) z / canonRoot38 φ z

def contourAction38 (φ : PotPair) (c : ℂ) (r : ℝ) : ℂ :=
  (1 / (Real.pi : ℂ)) * circleIntegral (actionIntegrand38 φ) c r

def gkActionC38 (φ : PotPair) (n : ℤ) : ℂ :=
  contourAction38 φ (discC φ n) (discR φ n)

def ActionContourIndependence38 : Prop :=
  ∀ (φ : PotPair), φ ∈ gkW →
    ∀ (C0 C1 : ℤ → ℂ) (R0 R1 : ℤ → ℝ),
      IsolatingFamily38 φ C0 R0 → IsolatingFamily38 φ C1 R1 →
      ∀ n : ℤ, contourAction38 φ (C0 n) (R0 n) = contourAction38 φ (C1 n) (R1 n)

def ActionContourRealization38 : Prop :=
  ∀ (φ : PotPair), φ ∈ gkW →
    ∀ (C0 C1 : ℤ → ℂ) (R0 R1 : ℤ → ℝ),
      IsolatingFamily38 φ C0 R0 → IsolatingFamily38 φ C1 R1 →
      ∀ n : ℤ,
        CircleIntegrable (actionIntegrand38 φ) (C0 n) (R0 n) ∧
        CircleIntegrable (actionIntegrand38 φ) (C1 n) (R1 n) ∧
        contourAction38 φ (C0 n) (R0 n) = contourAction38 φ (C1 n) (R1 n)

def ActionIntegrability38 : Prop :=
  ∀ (φ : PotPair), φ ∈ gkW → ∀ (C : ℤ → ℂ) (R : ℤ → ℝ),
    IsolatingFamily38 φ C R → ∀ n : ℤ, CircleIntegrable (actionIntegrand38 φ) (C n) (R n)

def ActionFamilyHomotopy38 : Prop :=
  ∀ (φ : PotPair), φ ∈ gkW →
    ∀ (C0 C1 : ℤ → ℂ) (R0 R1 : ℤ → ℝ),
      IsolatingFamily38 φ C0 R0 → IsolatingFamily38 φ C1 R1 →
      ∀ n : ℤ, 0 < R0 n ∧ 0 < R1 n ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          sphere (((1 - t) : ℝ) • C0 n + t • C1 n)
            ((1 - t) * R0 n + t * R1 n) ⊆ actionCutDomain38 φ

theorem actionCutDomain_eq_fibre38 (φ : PotPair) (hφ : φ ∈ gkW) :
    actionCutDomain38 φ = (fun z : ℂ => (φ, z)) ⁻¹' rootDomain38 := by
  ext z
  simp only [actionCutDomain38, Set.mem_ofPred_eq, Set.mem_preimage, rootDomain38,
    hφ, true_and]

theorem isOpen_actionCutDomain38 (φ : PotPair) (hφ : φ ∈ gkW) :
    IsOpen (actionCutDomain38 φ) := by
  rw [actionCutDomain_eq_fibre38 φ hφ]
  exact NlsGge.GK38.isOpen_rootDomain38.preimage
    (continuous_const.prodMk continuous_id)

theorem actionIntegrand_joint_analytic38 :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => actionIntegrand38 p.1 p.2) rootDomain38 := by
  intro p hp
  exact (analyticAt_snd.mul
    (NlsGge.GK38.analyticOnNhd_discrimDeriv_joint38 p (Set.mem_univ _))).div
    (NlsGge.GK38.canonRoot_analytic38 p hp)
    (NlsGge.GK38.canonRoot_ne_zero38 p.1 hp.1 p.2 hp.2)

theorem actionIntegrand_analytic38 (φ : PotPair) (hφ : φ ∈ gkW) :
    AnalyticOnNhd ℂ (actionIntegrand38 φ) (actionCutDomain38 φ) := by
  intro z hz
  have hp : (φ, z) ∈ rootDomain38 := ⟨hφ, hz⟩
  exact (actionIntegrand_joint_analytic38 (φ, z) hp).comp
    ((analyticAt_const (v := φ)).prod analyticAt_id)

theorem action_contour_sphere_subset38 (φ : PotPair) (C0 C1 : ℤ → ℂ) (R0 R1 : ℤ → ℝ)
    (h0 : IsolatingFamily38 φ C0 R0) (h1 : IsolatingFamily38 φ C1 R1)
    (n : ℤ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    sphere (((1 - t) : ℝ) • C0 n + t • C1 n)
      ((1 - t) * R0 n + t * R1 n) ⊆ actionCutDomain38 φ := by
  intro z hz
  exact NlsGge.GK38.contour_sphere_avoids_cuts38 φ C0 C1 R0 R1 h0 h1 n t ht z hz

theorem action_contour_radii_pos38 (φ : PotPair) (C0 C1 : ℤ → ℂ) (R0 R1 : ℤ → ℝ)
    (h0 : IsolatingFamily38 φ C0 R0) (h1 : IsolatingFamily38 φ C1 R1)
    (n : ℤ) : 0 < R0 n ∧ 0 < R1 n :=
  ⟨NlsGge.GK38.isolating_radius_pos38 h0 n,
    NlsGge.GK38.isolating_radius_pos38 h1 n⟩

theorem action_family_homotopy38 : ActionFamilyHomotopy38 := by
  intro φ _ C0 C1 R0 R1 h0 h1 n
  exact ⟨(action_contour_radii_pos38 φ C0 C1 R0 R1 h0 h1 n).1,
    (action_contour_radii_pos38 φ C0 C1 R0 R1 h0 h1 n).2,
    fun t ht => action_contour_sphere_subset38 φ C0 C1 R0 R1 h0 h1 n t ht⟩

theorem action_circle_integrable38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    CircleIntegrable (actionIntegrand38 φ) (C n) (R n) := by
  have hs : sphere (C n) (R n) ⊆ actionCutDomain38 φ := by
    simpa only [sub_zero, one_smul, zero_smul, add_zero, one_mul, zero_mul] using
      (action_contour_sphere_subset38 φ C C R R hf hf n 0 ⟨le_rfl, zero_le_one⟩)
  exact ((actionIntegrand_analytic38 φ hφ).continuousOn.mono hs).circleIntegrable
    (NlsGge.GK38.isolating_radius_pos38 hf n).le

theorem action_integrability38 : ActionIntegrability38 := action_circle_integrable38

-- This checks the full expanded target body. It is NOT a contour equality proof.
theorem action_independence_type_identity38 : ActionContourIndependence38 =
    (∀ (φ : PotPair), φ ∈ gkW →
      ∀ (C0 C1 : ℤ → ℂ) (R0 R1 : ℤ → ℝ),
        IsolatingFamily38 φ C0 R0 → IsolatingFamily38 φ C1 R1 →
        ∀ n : ℤ,
          (1 / (Real.pi : ℂ)) * circleIntegral
            (fun z : ℂ => z * deriv (discrim φ) z / canonRoot38 φ z) (C0 n) (R0 n) =
          (1 / (Real.pi : ℂ)) * circleIntegral
            (fun z : ℂ => z * deriv (discrim φ) z / canonRoot38 φ z) (C1 n) (R1 n)) := rfl

-- The full actual families discharge ALL hypotheses of the generic helper.
theorem action_raw_contour_realization38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C0 C1 : ℤ → ℂ) (R0 R1 : ℤ → ℝ)
    (h0 : IsolatingFamily38 φ C0 R0) (h1 : IsolatingFamily38 φ C1 R1) (n : ℤ) :
    CircleIntegrable (actionIntegrand38 φ) (C0 n) (R0 n) ∧
    CircleIntegrable (actionIntegrand38 φ) (C1 n) (R1 n) ∧
    circleIntegral (actionIntegrand38 φ) (C0 n) (R0 n) =
      circleIntegral (actionIntegrand38 φ) (C1 n) (R1 n) := by
  have hr := action_contour_radii_pos38 φ C0 C1 R0 R1 h0 h1 n
  exact NlsGge.Analysis.circleIntegral_eq_of_affine_circle_homotopy
    (isOpen_actionCutDomain38 φ hφ) (actionIntegrand_analytic38 φ hφ) hr.1 hr.2
    (fun t ht => action_contour_sphere_subset38 φ C0 C1 R0 R1 h0 h1 n t ht)

theorem action_contour_realization38 : ActionContourRealization38 := by
  intro φ hφ C0 C1 R0 R1 h0 h1 n
  have h := action_raw_contour_realization38 φ hφ C0 C1 R0 R1 h0 h1 n
  refine ⟨h.1, h.2.1, ?_⟩
  exact congrArg (fun v : ℂ => (1 / (Real.pi : ℂ)) * v) h.2.2

theorem action_contour_independence38 : ActionContourIndependence38 := by
  intro φ hφ C0 C1 R0 R1 h0 h1 n
  exact (action_contour_realization38 φ hφ C0 C1 R0 R1 h0 h1 n).2.2

end
end NlsGge.GK38
