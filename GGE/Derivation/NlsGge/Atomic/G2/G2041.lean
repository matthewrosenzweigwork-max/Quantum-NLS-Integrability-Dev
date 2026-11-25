import Mathlib
import NlsGge.Atomic.G2.G2040
import NlsGge.GK38.ActionRealBridge
import NlsGge.GK38.ContourActionDeformation
import NlsGge.GK38.IsolatingFamily
import NlsGge.GK38.PeriodicLabellingCanonical
import NlsGge.GK38.TauGamma

/- G2-041 PRODUCTION01 (proof development, AUTHOR; not self-reviewed). Target NlsGge/Atomic/G2/G2041.lean, namespace NlsGge.GKDefinitionDesign.
   Head G2_041 VERBATIM from newest design STATEMENTS/G2.md "## G2-041" (root/gpt6pro_followup11/...; no Pro round-13 BINDING_INDEX entry).
   Route (see G2041_ROUTE.md): equal discriminants give equal perChar, hence equal canonical cutoffs and equal lamSeq, hence equal tauN, gamma2 (tauN_value38/gamma2_value38),
   hence equal canonRoot38 and equal actionIntegrand38; the u-circle and the v-circle are homotopic in the u-cut domain (copy of contour_sphere_avoids_cuts38 for two potentials with the
   same gap segments), so gkActionC38 agrees termwise; the L2 mass identity (G2_040 part 2, HasSum) gives ||u||^2 = ||v||^2. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g2041_lamSeq_eq (u v : PotPair) (h : ∀ z : ℂ, discrim u z = discrim v z) :
    lamSeq u = lamSeq v := by
  have hD : discrim u = discrim v := funext h
  have hper : perChar u = perChar v := by unfold perChar; rw [hD]
  have hv : RootCountingAt38 (perChar u) 2 (canonicalCountingCutoff38 v) := by
    rw [hper]; exact (canonicalCountingCutoff_spec38 v).1
  calc lamSeq u = periodicCandidate38 (perChar u) (canonicalCountingCutoff38 v) :=
        lamSeq_eq_candidate38 u hv
    _ = lamSeq v := by rw [hper]; rfl

theorem g2041_canonRoot_eq (u v : PotPair) (hu : u ∈ gkW) (hv : v ∈ gkW)
    (h : ∀ z : ℂ, discrim u z = discrim v z) (z : ℂ) : canonRoot38 u z = canonRoot38 v z := by
  have hl := g2041_lamSeq_eq u v h
  have hm : ∀ n, lamMinus u n = lamMinus v n := fun n => by simp only [lamMinus, hl]
  have hp : ∀ n, lamPlus u n = lamPlus v n := fun n => by simp only [lamPlus, hl]
  have ht : ∀ n, tauN u n = tauN v n := fun n => by
    rw [tauN_value38 u hu, tauN_value38 v hv, hm, hp]
  have hg : ∀ n, gamma2 u n = gamma2 v n := fun n => by
    rw [gamma2_value38 u hu, gamma2_value38 v hv, hm, hp]
  simp only [canonRoot38, rootFactor38, ht, hg]

theorem g2041_integrand_eq (u v : PotPair) (hu : u ∈ gkW) (hv : v ∈ gkW)
    (h : ∀ z : ℂ, discrim u z = discrim v z) : actionIntegrand38 u = actionIntegrand38 v := by
  have hD : discrim u = discrim v := funext h
  funext z
  simp only [actionIntegrand38, hD, g2041_canonRoot_eq u v hu hv h z]

theorem g2041_sphere_avoids (u v : PotPair) (hl : lamSeq u = lamSeq v)
    (C0 C1 : ℤ → ℂ) (R0 R1 : ℤ → ℝ)
    (h0 : IsolatingFamily38 u C0 R0) (h1 : IsolatingFamily38 v C1 R1)
    (n : ℤ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ z ∈ sphere (contourCenter38 C0 C1 n t) (contourRadius38 R0 R1 n t),
      z ∉ gapSegments38 u := by
  intro z hz hcut
  obtain ⟨c0, N0, hg0, hs0⟩ := h0
  obtain ⟨c1, N1, hg1, hs1⟩ := h1
  obtain ⟨m, hzm⟩ := mem_iUnion.mp hcut
  have hm : lamMinus u m = lamMinus v m := by simp only [lamMinus, hl]
  have hp : lamPlus u m = lamPlus v m := by simp only [lamPlus, hl]
  have hb0 := (hs0.1 m).1 hzm
  have hb1 := (hs1.1 m).1 (by rw [← hm, ← hp]; exact hzm)
  have hnorm := mem_sphere_iff_norm.mp hz
  have hre : |z.re - (contourCenter38 C0 C1 n t).re| ≤ contourRadius38 R0 R1 n t := by
    simpa only [Complex.sub_re, hnorm] using Complex.abs_re_le_norm (z - contourCenter38 C0 C1 n t)
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · have hl0 := contour_left_bound38 C0 R0 c0 N0 hg0 hmn hb0
    have hl1 := contour_left_bound38 C1 R1 c1 N1 hg1 hmn hb1
    have hl := contour_combo_lt38 hl0 hl1 ht
    have hcalc : (1 - t) * z.re + t * z.re = z.re := by ring
    rw [hcalc] at hl
    have hc : (contourCenter38 C0 C1 n t).re =
        (1 - t) * (C0 n).re + t * (C1 n).re := by
      simp only [contourCenter38, Complex.add_re, Complex.smul_re, smul_eq_mul]
    rw [abs_le] at hre
    unfold contourRadius38 at hre
    rw [hc] at hre
    nlinarith [hre.1]
  · subst m
    have hb := contour_own_ball38 hb0 hb1 ht
    have hlt := mem_ball_iff_norm.mp hb
    exact (ne_of_lt hlt) hnorm
  · have hr0 := contour_right_bound38 C0 R0 c0 N0 hg0 hnm hb0
    have hr1 := contour_right_bound38 C1 R1 c1 N1 hg1 hnm hb1
    have hr := contour_combo_lt38 hr0 hr1 ht
    have hcalc : (1 - t) * z.re + t * z.re = z.re := by ring
    rw [hcalc] at hr
    have hc : (contourCenter38 C0 C1 n t).re =
        (1 - t) * (C0 n).re + t * (C1 n).re := by
      simp only [contourCenter38, Complex.add_re, Complex.smul_re, smul_eq_mul]
    rw [abs_le] at hre
    unfold contourRadius38 at hre
    rw [hc] at hre
    nlinarith [hre.2]

theorem g2041_action_eq (u v : PotPair) (hu : u ∈ gkW) (hv : v ∈ gkW)
    (h : ∀ z : ℂ, discrim u z = discrim v z) (n : ℤ) : gkActionC38 u n = gkActionC38 v n := by
  have hl := g2041_lamSeq_eq u v h
  have h0 := isolating_family38 u hu
  have h1 := isolating_family38 v hv
  have hint := NlsGge.Analysis.circleIntegral_eq_of_affine_circle_homotopy
    (isOpen_actionCutDomain38 u hu) (actionIntegrand_analytic38 u hu)
    (isolating_radius_pos38 h0 n) (isolating_radius_pos38 h1 n)
    (fun t ht z hz => g2041_sphere_avoids u v hl (discC u) (discC v) (discR u) (discR v)
      h0 h1 n t ht z hz)
  unfold gkActionC38 contourAction38
  rw [hint.2.2, g2041_integrand_eq u v hu hv h]

theorem G2_041 (u v : PhysicalL2)
    (h : ∀ z : ℂ, discrim (realSlice u) z = discrim (realSlice v) z) :
    ‖u‖ = ‖v‖ := by
  have heq : ∀ n : ℤ, actualGapActionAllE02_38 u n = actualGapActionAllE02_38 v n := by
    intro n
    have := g2041_action_eq (realSlice u) (realSlice v) (realSlice_mem_gkW u)
      (realSlice_mem_gkW v) h n
    rw [NlsGge.GK38.ActionRealBridge.action_real_bridge u n,
      NlsGge.GK38.ActionRealBridge.action_real_bridge v n] at this
    exact_mod_cast this
  have h1 := (G2_040.2 u).1
  have h2 := (G2_040.2 v).1
  have hsq : ‖u‖ ^ 2 = ‖v‖ ^ 2 := by
    refine h1.unique ?_
    have e : actualGapActionAllE02_38 u = actualGapActionAllE02_38 v := funext heq
    rw [e]; exact h2
  exact (pow_left_inj₀ (norm_nonneg u) (norm_nonneg v) two_ne_zero).1 hsq

end
end NlsGge.GKDefinitionDesign
