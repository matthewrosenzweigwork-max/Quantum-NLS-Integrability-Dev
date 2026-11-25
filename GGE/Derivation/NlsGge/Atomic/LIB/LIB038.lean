import NlsGge.Atomic.LIB.LIB037
import Mathlib.Analysis.SpecificLimits.Normed


/-!
# LIB-038: closed complex ZS realizations with a genuine resolvent point

For every complex L2 potential pair, the literal off-diagonal multiplication
composed with the actual free H1 resolvent is a bounded operator K. At the
explicit height R = 1 + 3‖φ‖² its norm is strictly below one. The Neumann series
converges in operator norm, and the inverse factors are ordered R0 ∘ (I-K)⁻¹.
Both inverse identities are proved on the actual four H1 boundary domains, and
the constructed inverse retains its genuine H1 image.

The full bounded inverse identifies the actual unbounded graph with a closed
equalizer. This proves closedness directly; no domain characterization,
maximality premise, H1 completeness premise, or real-type restriction is added.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace NlsGge.Atomic.LIB038
open NlsGge.Schur NlsGge.Atomic.Interval
open NlsGge.Atomic.LIB026 NlsGge.Atomic.LIB031 NlsGge.Atomic.LIB032
open NlsGge.Atomic.LIB033 NlsGge.Atomic.LIB037

lemma potentialProduct_add (φ : SourcePairL2) (f g : H1Pair) :
    potentialProduct φ (h1PairAdd f g) = potentialProduct φ f + potentialProduct φ g := by
  apply PiLp.ext
  intro b
  apply Lp.ext
  filter_upwards [potentialProduct_ae φ (h1PairAdd f g) b, potentialProduct_ae φ f b,
    potentialProduct_ae φ g b, Lp.coeFn_add (f (!b)).value (g (!b)).value,
    Lp.coeFn_add (potentialProduct φ f b) (potentialProduct φ g b)]
    with x h0 hf hg hin hout
  change potentialProduct φ (h1PairAdd f g) b x = (potentialProduct φ f b + potentialProduct φ g b) x
  rw [hout]
  simp only [Pi.add_apply]
  rw [h0, hf, hg]
  change φ b x * ((f (!b)).value + (g (!b)).value) x = _
  rw [hin]
  change φ b x * ((f (!b)).value x + (g (!b)).value x) = _
  ring
lemma potentialProduct_smul (φ : SourcePairL2) (c : ℂ) (f : H1Pair) :
    potentialProduct φ (h1PairSmul c f) = c • potentialProduct φ f := by
  apply PiLp.ext
  intro b
  apply Lp.ext
  filter_upwards [potentialProduct_ae φ (h1PairSmul c f) b, potentialProduct_ae φ f b,
    Lp.coeFn_smul c (f (!b)).value, Lp.coeFn_smul c (potentialProduct φ f b)]
    with x h0 hf hin hout
  change potentialProduct φ (h1PairSmul c f) b x = (c • potentialProduct φ f b) x
  rw [hout]
  change potentialProduct φ (h1PairSmul c f) b x = c * potentialProduct φ f b x
  rw [h0, hf]
  change φ b x * (c • (f (!b)).value) x = _
  rw [hin]
  change φ b x * (c * (f (!b)).value x) = _
  ring
lemma potentialProduct_zero_potential (f : H1Pair) : potentialProduct 0 f = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [norm_zero, zero_mul] using potentialProduct_norm_le (0 : SourcePairL2) f
lemma zsApply_eq_free_add (φ : SourcePairL2) (f : H1Pair) :
    zsApply φ f = zsApply 0 f + potentialProduct φ f := by
  rw [zsApply_eq_phase_add_potential φ f, zsApply_eq_phase_add_potential 0 f,
    potentialProduct_zero_potential, add_zero]

def perturbationLinear (φ : SourcePairL2) (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R) :
    SourcePairL2 →ₗ[ℂ] SourcePairL2 where
  toFun f := potentialProduct φ (freeZSResolventH1 bc R hR f)
  map_add' f g := by rw [freeZSResolventH1_add, potentialProduct_add]
  map_smul' c f := by rw [freeZSResolventH1_smul, potentialProduct_smul]; rfl
lemma perturbation_bound (φ : SourcePairL2) (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R)
    (f : SourcePairL2) : ‖perturbationLinear φ bc R hR f‖ ≤
      (‖φ‖ * (Real.sqrt 3 / Real.sqrt R)) * ‖f‖ := by
  calc
    _ ≤ ‖φ‖ * ‖pairRepresentative (freeZSResolventH1 bc R hR f)‖ :=
      potentialProduct_norm_le φ _
    _ ≤ ‖φ‖ * ((Real.sqrt 3 / Real.sqrt R) * ‖f‖) :=
      mul_le_mul_of_nonneg_left (freeZSResolvent_representative_bound bc R hR f) (norm_nonneg φ)
    _ = _ := by ring

def perturbationAt (φ : SourcePairL2) (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R) :
    SourcePairL2 →L[ℂ] SourcePairL2 :=
  (perturbationLinear φ bc R hR).mkContinuous (‖φ‖ * (Real.sqrt 3 / Real.sqrt R))
    (perturbation_bound φ bc R hR)
lemma perturbationAt_norm_le (φ : SourcePairL2) (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R) :
    ‖perturbationAt φ bc R hR‖ ≤ ‖φ‖ * (Real.sqrt 3 / Real.sqrt R) :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

def resolventHeight (φ : SourcePairL2) : ℝ := 1 + 3 * ‖φ‖ ^ 2
lemma resolventHeight_ge_one (φ : SourcePairL2) : 1 ≤ resolventHeight φ := by
  dsimp only [resolventHeight]
  nlinarith [sq_nonneg ‖φ‖]
lemma resolventHeight_small (φ : SourcePairL2) :
    ‖φ‖ * (Real.sqrt 3 / Real.sqrt (resolventHeight φ)) < 1 := by
  have hR : 0 < resolventHeight φ := by have h := resolventHeight_ge_one φ; linarith
  have hsq : (‖φ‖ * Real.sqrt 3) ^ 2 < (Real.sqrt (resolventHeight φ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hR.le]
    dsimp only [resolventHeight]
    nlinarith
  have hlt := (sq_lt_sq₀ (by positivity : 0 ≤ ‖φ‖ * Real.sqrt 3)
    (Real.sqrt_nonneg (resolventHeight φ))).mp hsq
  calc
    ‖φ‖ * (Real.sqrt 3 / Real.sqrt (resolventHeight φ)) =
      (‖φ‖ * Real.sqrt 3) / Real.sqrt (resolventHeight φ) := by ring
    _ < 1 := (div_lt_one (Real.sqrt_pos.mpr hR)).mpr hlt

def perturbation (φ : SourcePairL2) (bc : ZSBoundaryCondition) : SourcePairL2 →L[ℂ] SourcePairL2 :=
  perturbationAt φ bc (resolventHeight φ) (resolventHeight_ge_one φ)
lemma perturbation_norm_lt_one (φ : SourcePairL2) (bc : ZSBoundaryCondition) :
    ‖perturbation φ bc‖ < 1 :=
  (perturbationAt_norm_le φ bc _ _).trans_lt (resolventHeight_small φ)

def neumannUnit (φ : SourcePairL2) (bc : ZSBoundaryCondition) :
    (SourcePairL2 →L[ℂ] SourcePairL2)ˣ :=
  Units.oneSub (perturbation φ bc) (perturbation_norm_lt_one φ bc)
def neumannInverse (φ : SourcePairL2) (bc : ZSBoundaryCondition) : SourcePairL2 →L[ℂ] SourcePairL2 :=
  ↑(neumannUnit φ bc)⁻¹
lemma neumann_hasSum (φ : SourcePairL2) (bc : ZSBoundaryCondition) :
    HasSum (fun n : ℕ => perturbation φ bc ^ n) (neumannInverse φ bc) :=
  (summable_geometric_of_norm_lt_one (perturbation_norm_lt_one φ bc)).hasSum
lemma neumann_right_inverse (φ : SourcePairL2) (bc : ZSBoundaryCondition) :
    (1 - perturbation φ bc) * neumannInverse φ bc = 1 := (neumannUnit φ bc).val_inv
lemma neumann_left_inverse (φ : SourcePairL2) (bc : ZSBoundaryCondition) :
    neumannInverse φ bc * (1 - perturbation φ bc) = 1 := (neumannUnit φ bc).inv_val

def resolventPoint (φ : SourcePairL2) : ℂ := Complex.I * (resolventHeight φ : ℂ)
def complexZSResolvent (φ : SourcePairL2) (bc : ZSBoundaryCondition) :
    SourcePairL2 →L[ℂ] SourcePairL2 :=
  (freeZSResolvent bc (resolventHeight φ) (resolventHeight_ge_one φ)).comp (neumannInverse φ bc)
def complexZSResolventH1 (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    (f : SourcePairL2) : H1Pair :=
  freeZSResolventH1 bc (resolventHeight φ) (resolventHeight_ge_one φ) (neumannInverse φ bc f)
lemma complexZSResolventH1_value (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    (f : SourcePairL2) : h1PairValue (complexZSResolventH1 φ bc f) = complexZSResolvent φ bc f :=
  freeZSResolventH1_value _ _ _ _
lemma complexZSResolventH1_boundary (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    (f : SourcePairL2) : HasZSBoundaryCondition bc (complexZSResolventH1 φ bc f) :=
  freeZSResolventH1_boundary _ _ _ _
lemma neumann_right_apply (φ : SourcePairL2) (bc : ZSBoundaryCondition) (f : SourcePairL2) :
    neumannInverse φ bc f - perturbation φ bc (neumannInverse φ bc f) = f := by
  have h := congrArg (fun T : SourcePairL2 →L[ℂ] SourcePairL2 => T f) (neumann_right_inverse φ bc)
  exact h
lemma neumann_left_apply (φ : SourcePairL2) (bc : ZSBoundaryCondition) (f : SourcePairL2) :
    neumannInverse φ bc (f - perturbation φ bc f) = f := by
  have h := congrArg (fun T : SourcePairL2 →L[ℂ] SourcePairL2 => T f) (neumann_left_inverse φ bc)
  exact h

lemma free_right_H1 (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R) (f : SourcePairL2) :
    (Complex.I * (R : ℂ)) • h1PairValue (freeZSResolventH1 bc R hR f) -
      zsApply 0 (freeZSResolventH1 bc R hR f) = f := by
  rw [freeZSResolventH1_value, freeZSResolventH1_action, freeZSActionImage_eq]
  abel

/-- The right inverse is computed with the literal complex potential action. -/
lemma complex_right_H1 (φ : SourcePairL2) (bc : ZSBoundaryCondition) (f : SourcePairL2) :
    resolventPoint φ • h1PairValue (complexZSResolventH1 φ bc f) -
      zsApply φ (complexZSResolventH1 φ bc f) = f := by
  rw [zsApply_eq_free_add]
  change resolventPoint φ • h1PairValue (complexZSResolventH1 φ bc f) -
    (zsApply 0 (complexZSResolventH1 φ bc f) +
      perturbation φ bc (neumannInverse φ bc f)) = f
  rw [← sub_sub]
  rw [show resolventPoint φ • h1PairValue (complexZSResolventH1 φ bc f) -
      zsApply 0 (complexZSResolventH1 φ bc f) = neumannInverse φ bc f from
    free_right_H1 bc _ _ _]
  exact neumann_right_apply φ bc f

lemma free_left_H1 (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R)
    (g : H1Pair) (hg : HasZSBoundaryCondition bc g) :
    freeZSResolvent bc R hR ((Complex.I * (R : ℂ)) • h1PairValue g - zsApply 0 g) = h1PairValue g := by
  have h := freeZSResolvent_left_inverse bc R hR (⟨h1PairValue g, ⟨g, hg, rfl⟩⟩)
  rw [zsRealization_apply 0 bc g hg] at h
  exact h

/-- Actual H1 value injectivity identifies the free lift before multiplying by the potential. -/
lemma free_lift_left (bc : ZSBoundaryCondition) (R : ℝ) (hR : 1 ≤ R)
    (g : H1Pair) (hg : HasZSBoundaryCondition bc g) :
    freeZSResolventH1 bc R hR ((Complex.I * (R : ℂ)) • h1PairValue g - zsApply 0 g) = g := by
  apply h1PairValue_injective
  rw [freeZSResolventH1_value, free_left_H1 bc R hR g hg]

lemma perturbation_factorization (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    (g : H1Pair) (hg : HasZSBoundaryCondition bc g) :
    resolventPoint φ • h1PairValue g - zsApply φ g =
      (resolventPoint φ • h1PairValue g - zsApply 0 g) -
        perturbation φ bc (resolventPoint φ • h1PairValue g - zsApply 0 g) := by
  have hK : perturbation φ bc (resolventPoint φ • h1PairValue g - zsApply 0 g) =
      potentialProduct φ g := by
    change potentialProduct φ (freeZSResolventH1 bc (resolventHeight φ)
      (resolventHeight_ge_one φ) (resolventPoint φ • h1PairValue g - zsApply 0 g)) = _
    rw [show freeZSResolventH1 bc (resolventHeight φ) (resolventHeight_ge_one φ)
      (resolventPoint φ • h1PairValue g - zsApply 0 g) = g from free_lift_left bc _ _ g hg]
  rw [hK, zsApply_eq_free_add]
  abel

lemma complex_left_H1 (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    (g : H1Pair) (hg : HasZSBoundaryCondition bc g) :
    complexZSResolvent φ bc (resolventPoint φ • h1PairValue g - zsApply φ g) = h1PairValue g := by
  rw [perturbation_factorization φ bc g hg]
  change freeZSResolvent bc (resolventHeight φ) (resolventHeight_ge_one φ)
    (neumannInverse φ bc ((resolventPoint φ • h1PairValue g - zsApply 0 g) -
      perturbation φ bc (resolventPoint φ • h1PairValue g - zsApply 0 g))) = _
  rw [neumann_left_apply]
  exact free_left_H1 bc _ _ g hg

lemma complexZSResolvent_mem_domain (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    (f : SourcePairL2) : complexZSResolvent φ bc f ∈ (zsRealization φ bc).domain :=
  ⟨complexZSResolventH1 φ bc f, complexZSResolventH1_boundary φ bc f,
    complexZSResolventH1_value φ bc f⟩

lemma complexZSResolvent_action (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    (f : SourcePairL2) :
    zsRealization φ bc ⟨complexZSResolvent φ bc f, complexZSResolvent_mem_domain φ bc f⟩ =
      zsApply φ (complexZSResolventH1 φ bc f) := by
  change zsApply φ (domainLift ⟨complexZSResolvent φ bc f, complexZSResolvent_mem_domain φ bc f⟩) = _
  rw [domainLift_eq _ (complexZSResolventH1 φ bc f) (complexZSResolventH1_value φ bc f)]

/-- Full right inverse on the actual realization domain. -/
theorem complexZSResolvent_right_inverse (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    (f : SourcePairL2) : resolventPoint φ • complexZSResolvent φ bc f -
      zsRealization φ bc ⟨complexZSResolvent φ bc f, complexZSResolvent_mem_domain φ bc f⟩ = f := by
  rw [complexZSResolvent_action, ← complexZSResolventH1_value]
  exact complex_right_H1 φ bc f

set_option backward.isDefEq.respectTransparency false in
/-- Full left inverse for every vector of the actual H1 boundary domain. -/
theorem complexZSResolvent_left_inverse (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    (u : (zsRealization φ bc).domain) :
    complexZSResolvent φ bc (resolventPoint φ • (u : SourcePairL2) - zsRealization φ bc u) = u := by
  have h := complex_left_H1 φ bc (domainLift u) (domainLift_boundary u)
  simpa only [domainLift_value u] using! h

def HasBoundedResolvent (A : SourcePairL2 →ₗ.[ℂ] SourcePairL2) (z : ℂ) : Prop :=
  ∃ T : SourcePairL2 →L[ℂ] SourcePairL2,
    (∀ f : SourcePairL2, ∃ hf : T f ∈ A.domain, z • T f - A ⟨T f, hf⟩ = f) ∧
    (∀ u : A.domain, T (z • (u : SourcePairL2) - A u) = u)

theorem zs_complex_resolvent_at_height (φ : SourcePairL2) (bc : ZSBoundaryCondition) :
    HasBoundedResolvent (zsRealization φ bc) (resolventPoint φ) :=
  ⟨complexZSResolvent φ bc,
    (fun f => ⟨complexZSResolvent_mem_domain φ bc f, complexZSResolvent_right_inverse φ bc f⟩),
    complexZSResolvent_left_inverse φ bc⟩

theorem zs_complex_resolvent_nonempty (φ : SourcePairL2) (bc : ZSBoundaryCondition) :
    ∃ z : ℂ, HasBoundedResolvent (zsRealization φ bc) z :=
  ⟨resolventPoint φ, zs_complex_resolvent_at_height φ bc⟩

set_option backward.isDefEq.respectTransparency false in
lemma graph_eq_resolvent_equalizer (A : SourcePairL2 →ₗ.[ℂ] SourcePairL2) (z : ℂ)
    (T : SourcePairL2 →L[ℂ] SourcePairL2)
    (hr : ∀ f : SourcePairL2, ∃ hf : T f ∈ A.domain, z • T f - A ⟨T f, hf⟩ = f)
    (hl : ∀ u : A.domain, T (z • (u : SourcePairL2) - A u) = u) :
    (A.graph : Set (SourcePairL2 × SourcePairL2)) = {p | T (z • p.1 - p.2) = p.1} := by
  ext p
  rcases p with ⟨x,y⟩
  constructor
  · intro hp
    obtain ⟨u, hux, huy⟩ := (LinearPMap.mem_graph_iff A).mp hp
    change (u : SourcePairL2) = x at hux
    change A u = y at huy
    change T (z • x - y) = x
    rw [← hux, ← huy]
    exact hl u
  · intro hp
    change T (z • x - y) = x at hp
    obtain ⟨hmem, hact⟩ := hr (z • x - y)
    have hxmem : x ∈ A.domain := hp ▸ hmem
    have he : (⟨T (z • x - y), hmem⟩ : A.domain) = ⟨x, hxmem⟩ := Subtype.ext hp
    apply (LinearPMap.mem_graph_iff A).mpr
    refine ⟨⟨x, hxmem⟩, rfl, ?_⟩
    rw [he, hp] at hact
    exact sub_right_inj.mp hact

/-- A genuine full bounded inverse makes the literal unbounded graph a closed equalizer. -/
lemma HasBoundedResolvent.isClosed (A : SourcePairL2 →ₗ.[ℂ] SourcePairL2) (z : ℂ)
    (h : HasBoundedResolvent A z) : A.IsClosed := by
  obtain ⟨T, hr, hl⟩ := h
  change _root_.IsClosed (A.graph : Set (SourcePairL2 × SourcePairL2))
  rw [graph_eq_resolvent_equalizer A z T hr hl]
  have hc : Continuous (fun p : SourcePairL2 × SourcePairL2 => z • p.1 - p.2) :=
    (continuous_fst.const_smul z).sub continuous_snd
  exact isClosed_eq (T.continuous.comp hc) continuous_fst

theorem zs_complex_closed (φ : SourcePairL2) (bc : ZSBoundaryCondition) :
    (zsRealization φ bc).IsClosed :=
  HasBoundedResolvent.isClosed _ _ (zs_complex_resolvent_at_height φ bc)

theorem zs_complex_closed_and_resolvent (φ : SourcePairL2) (bc : ZSBoundaryCondition) :
    (zsRealization φ bc).IsClosed ∧ ∃ z : ℂ, HasBoundedResolvent (zsRealization φ bc) z :=
  ⟨zs_complex_closed φ bc, zs_complex_resolvent_nonempty φ bc⟩

theorem complexZSResolvent_H1_image (φ : SourcePairL2) (bc : ZSBoundaryCondition)
    (f : SourcePairL2) : ∃ g : H1Pair, HasZSBoundaryCondition bc g ∧
      h1PairValue g = complexZSResolvent φ bc f ∧
      resolventPoint φ • h1PairValue g - zsApply φ g = f :=
  ⟨complexZSResolventH1 φ bc f, complexZSResolventH1_boundary φ bc f,
    complexZSResolventH1_value φ bc f, complex_right_H1 φ bc f⟩

end NlsGge.Atomic.LIB038
