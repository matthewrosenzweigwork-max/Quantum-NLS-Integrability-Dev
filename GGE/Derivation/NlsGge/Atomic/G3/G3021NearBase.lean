import Mathlib
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.Atomic.G2.G2046
import NlsGge.Atomic.G2.G2019
import NlsGge.Atomic.G3.G3019
import NlsGge.Atomic.G3.G3ZetaHost
import NlsGge.ThirdConsultation.G3.G3M12Support
import NlsGge.ThirdConsultation.G3.G3S1Support

/- G3-021 supporting module NEARBASE (proof development, AUTHOR; not self-reviewed; NOT the G3_021 head).
   Target NlsGge/Atomic/G3/G3021NearBase.lean, namespace NlsGge.GKDefinitionDesign.
   Generic refactor of the "switch the roles of lambda^+ and lambda^-" step of GK 15.2: instead of mirroring the lamMinus-based
   estimates for lamPlus, the base point is the NEARER endpoint of the pair (lamMinus, lamPlus) to muSeq (ties go to lamMinus),
   chosen pointwise in phi.  Everything below is stated for this single base point `nearEnd`; the lower and upper cases are
   handled uniformly and no subsequence/type splitting is needed.
   Supporting definitions (not head names): nearEnd, farEnd, nearOmega, nearSegPoint, nearRatio, nearDensity.
   Facts: nearEnd is a root of perChar, lies in the isolating disc, gives tau = (far+near)/2 and gamma2 = (far-near)^2,
   the nearness inequality holds by construction, and nearEnd is continuous at every collapsed point of sourceW. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- The endpoint of the gap pair nearer to the Dirichlet eigenvalue (ties go to the lower endpoint). -/
def nearEnd (m : ℤ) (φ : PotPair) : ℂ :=
  if ‖muSeq φ m - lamMinus φ m‖ ≤ ‖muSeq φ m - lamPlus φ m‖ then lamMinus φ m else lamPlus φ m

/-- The other endpoint. -/
def farEnd (m : ℤ) (φ : PotPair) : ℂ :=
  lamMinus φ m + lamPlus φ m - nearEnd m φ

def nearOmega (m : ℤ) (φ : PotPair) : ℂ :=
  muSeq φ m - nearEnd m φ

def nearSegPoint (m : ℤ) (φ : PotPair) (t : ℝ) : ℂ :=
  nearEnd m φ + (t : ℂ) * nearOmega m φ

def nearRatio (n m : ℤ) (φ : PotPair) (t : ℝ) : ℂ :=
  (normalizedRoot n m φ - nearSegPoint m φ t) / standardRoot φ m (nearSegPoint m φ t)

def nearDensity (n m : ℤ) (φ : PotPair) (t : ℝ) : ℂ :=
  nearRatio n m φ t * betaZeta n m φ (nearSegPoint m φ t) * nearOmega m φ

namespace G3021N

theorem near_eq_or (m : ℤ) (φ : PotPair) :
    (nearEnd m φ = lamMinus φ m ∧ ‖muSeq φ m - lamMinus φ m‖ ≤ ‖muSeq φ m - lamPlus φ m‖) ∨
    (nearEnd m φ = lamPlus φ m ∧ ¬ ‖muSeq φ m - lamMinus φ m‖ ≤ ‖muSeq φ m - lamPlus φ m‖) := by
  by_cases h : ‖muSeq φ m - lamMinus φ m‖ ≤ ‖muSeq φ m - lamPlus φ m‖
  · exact Or.inl ⟨if_pos h, h⟩
  · exact Or.inr ⟨if_neg h, h⟩

theorem near_add_far (m : ℤ) (φ : PotPair) :
    nearEnd m φ + farEnd m φ = lamMinus φ m + lamPlus φ m := by
  unfold farEnd; ring

theorem far_eq_or (m : ℤ) (φ : PotPair) :
    (nearEnd m φ = lamMinus φ m ∧ farEnd m φ = lamPlus φ m ∧
      ‖muSeq φ m - lamMinus φ m‖ ≤ ‖muSeq φ m - lamPlus φ m‖) ∨
    (nearEnd m φ = lamPlus φ m ∧ farEnd m φ = lamMinus φ m ∧
      ‖muSeq φ m - lamPlus φ m‖ ≤ ‖muSeq φ m - lamMinus φ m‖) := by
  rcases near_eq_or m φ with ⟨h, h2⟩ | ⟨h, h2⟩
  · refine Or.inl ⟨h, ?_, h2⟩
    unfold farEnd; rw [h]; ring
  · refine Or.inr ⟨h, ?_, (not_le.1 h2).le⟩
    unfold farEnd; rw [h]; ring

theorem near_le_far (m : ℤ) (φ : PotPair) :
    ‖muSeq φ m - nearEnd m φ‖ ≤ ‖muSeq φ m - farEnd m φ‖ := by
  rcases far_eq_or m φ with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rw [h1, h2]; exact h3
  · rw [h1, h2]; exact h3

theorem far_sub_near_sq (m : ℤ) (φ : PotPair) :
    (farEnd m φ - nearEnd m φ) ^ 2 = (lamPlus φ m - lamMinus φ m) ^ 2 := by
  rcases far_eq_or m φ with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
  · rw [h1, h2]
  · rw [h1, h2]; ring

theorem norm_far_sub_near (m : ℤ) (φ : PotPair) :
    ‖farEnd m φ - nearEnd m φ‖ = ‖gap φ m‖ := by
  unfold gap
  rcases far_eq_or m φ with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
  · rw [h1, h2]
  · rw [h1, h2, ← norm_neg]; congr 1; ring

theorem tauN_eq_near_far (m : ℤ) (φ : PotPair) (hφ : φ ∈ gkW) :
    tauN φ m = (farEnd m φ + nearEnd m φ) / 2 := by
  rw [tauN_value38 φ hφ m, add_comm (farEnd m φ), near_add_far]
  ring

theorem gamma2_eq_near_far (m : ℤ) (φ : PotPair) (hφ : φ ∈ gkW) :
    gamma2 φ m = (farEnd m φ - nearEnd m φ) ^ 2 := by
  rw [gamma2_value38 φ hφ m, far_sub_near_sq]

theorem near_perChar_zero (m : ℤ) (φ : PotPair) : perChar φ (nearEnd m φ) = 0 := by
  rcases near_eq_or m φ with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; exact (lamSeq_enumeration38 φ).1 (2 * m)
  · rw [h]; exact (lamSeq_enumeration38 φ).1 (2 * m + 1)

theorem near_mem_ball {C : ℤ → ℂ} {R : ℤ → ℝ} (m : ℤ) (ψ : PotPair)
    (hspec : IsolatingSpectral38 ψ C R) : nearEnd m ψ ∈ ball (C m) (R m) := by
  rcases near_eq_or m ψ with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; exact (hspec.1 m).1 (left_mem_segment ℝ _ _)
  · rw [h]; exact (hspec.1 m).1 (right_mem_segment ℝ _ _)

theorem seg_mem {C : ℤ → ℂ} {R : ℤ → ℝ} (m : ℤ) (ψ : PotPair)
    (hspec : IsolatingSpectral38 ψ C R) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    nearSegPoint m ψ t ∈ ball (C m) (R m) := by
  have hL : nearEnd m ψ ∈ ball (C m) (R m) := near_mem_ball m ψ hspec
  have hM : muSeq ψ m ∈ ball (C m) (R m) := (hspec.1 m).2.1
  have h := (convex_ball (C m) (R m)).add_smul_sub_mem hL hM ht
  rw [Complex.real_smul] at h
  unfold nearSegPoint nearOmega
  exact h

theorem seg_continuous (m : ℤ) (ψ : PotPair) : Continuous (fun t : ℝ => nearSegPoint m ψ t) := by
  unfold nearSegPoint
  exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

theorem seg_one (m : ℤ) (ψ : PotPair) : nearSegPoint m ψ 1 = muSeq ψ m := by
  unfold nearSegPoint nearOmega
  rw [Complex.ofReal_one, one_mul]; ring

theorem near_collapsed_value (m : ℤ) (φ0 : PotPair) (hφ0 : φ0 ∈ sourceW) (hgap : gamma2 φ0 m = 0) :
    nearEnd m φ0 = tauN φ0 m := by
  have hl := g3s1_lam_eq φ0 (sourceFamily.W_gk hφ0) m hgap
  rw [hl.2]
  unfold nearEnd
  rw [if_pos (by rw [hl.1])]

theorem near_continuousAt (m : ℤ) (φ0 : PotPair) (hφ0 : φ0 ∈ sourceW) (hgap : gamma2 φ0 m = 0) :
    ContinuousAt (fun ψ : PotPair => nearEnd m ψ) φ0 := by
  have hgk0 : φ0 ∈ gkW := sourceFamily.W_gk hφ0
  have hc := angleActual_collapsed_endpoint_continuity38 φ0 hgk0 m hgap
  have hl := g3s1_lam_eq φ0 hgk0 m hgap
  have hn0 : nearEnd m φ0 = lamMinus φ0 m := by
    rw [near_collapsed_value m φ0 hφ0 hgap, hl.2]
  rw [Metric.continuousAt_iff']
  intro ε hε
  have h1 := Metric.continuousAt_iff'.1 hc.1 ε hε
  have h2 := Metric.continuousAt_iff'.1 hc.2 ε hε
  filter_upwards [h1, h2] with ψ hψ1 hψ2
  rw [hn0]
  rcases near_eq_or m ψ with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; exact hψ1
  · rw [h]; rw [hl.1] at hψ2; exact hψ2

theorem omega_tendsto (m : ℤ) (v : ℕ → PotPair) (φ0 : PotPair) (hφ0 : φ0 ∈ sourceW)
    (hgap : gamma2 φ0 m = 0) (hv : Tendsto v atTop (𝓝 φ0)) :
    Tendsto (fun j : ℕ => nearOmega m (v j)) atTop (𝓝 (muSeq φ0 m - tauN φ0 m)) := by
  have h1 := (near_continuousAt m φ0 hφ0 hgap).tendsto.comp hv
  rw [near_collapsed_value m φ0 hφ0 hgap] at h1
  exact (g3m1_muSeq_tendsto m v φ0 hφ0 hv).sub h1

theorem omega_ne (m : ℤ) (φ : PotPair) (hφ : φ ∈ sourceW) (hnot : φ ∉ endpointSet m) :
    nearOmega m φ ≠ 0 := by
  intro h
  unfold nearOmega at h
  have hμ : muSeq φ m = nearEnd m φ := sub_eq_zero.1 h
  apply hnot
  refine ⟨hφ, ?_⟩
  rw [hμ]
  exact near_perChar_zero m φ

theorem seg_continuousAt_joint (m : ℤ) (φ0 : PotPair) (t0 : ℝ)
    (h1 : ContinuousAt (fun ψ : PotPair => nearEnd m ψ) φ0)
    (h2 : ContinuousAt (fun ψ : PotPair => muSeq ψ m) φ0) :
    ContinuousAt (fun p : PotPair × ℝ => nearSegPoint m p.1 p.2) (φ0, t0) := by
  have hL : ContinuousAt (fun p : PotPair × ℝ => nearEnd m p.1) (φ0, t0) :=
    ContinuousAt.comp (f := fun p : PotPair × ℝ => p.1) (x := (φ0, t0)) h1 continuous_fst.continuousAt
  have hM : ContinuousAt (fun p : PotPair × ℝ => muSeq p.1 m) (φ0, t0) :=
    ContinuousAt.comp (f := fun p : PotPair × ℝ => p.1) (x := (φ0, t0)) h2 continuous_fst.continuousAt
  have hT : ContinuousAt (fun p : PotPair × ℝ => (p.2 : ℂ)) (φ0, t0) :=
    (Complex.continuous_ofReal.comp continuous_snd).continuousAt
  have h := hL.add (hT.mul (hM.sub hL))
  unfold nearSegPoint nearOmega
  exact h

end G3021N

end
end NlsGge.GKDefinitionDesign
