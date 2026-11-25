import NlsGge.Atomic.G1.G1100Support
import NlsGge.Atomic.G1.G1096
import NlsGge.Atomic.G1.G1097
import NlsGge.Atomic.G1.G1098
import NlsGge.Atomic.G1.G1099
import NlsGge.ThirdConsultation.G1.G1098RealBasis
import NlsGge.ThirdConsultation.G1.G1098Assembly
import NlsGge.GK38.Lib.CompactOps

/- G1-100 PRODUCTION01 (proof development, AUTHOR; not self-reviewed; semantic fidelity not checked).
   Target NlsGge/Atomic/G1/G1100.lean, namespace NlsGge.Atomic.G1100. Head VERBATIM from root/gpt6pro_followup7
   STATEMENTS/G1.md (section G1-100, line 699): `theorem G1_100 : Function.Injective normingDirichletMap`.
   Round 9 does not revise G1-100. Support module: NlsGge/Atomic/G1/G1100Support.lean.
   Route (Grebert-Kappeler 10.9, preserved): suppose normingDirichletMap u = normingDirichletMap v, A := mixedSquaredOperator u v.
   (1) G1_099: A - 1 is compact (vacuum is the identity). (2) G1_097: on the Hilbert basis of normalized reference
   columns the integrated brackets of the columns A d_k are zero except for the pairing (n,+)<->(n,-), where they are
   nonzero; the brackets are the real symplectic form Bform of the column classes (wedge_integral_eq, using that all
   mixed kernels are real-symmetric). (3) Lemma F.7 (NlsGge.GK38.Lib.lemmaF7_of_bilinear): A is an isomorphism and
   every vector is a convergent series of the columns A d_k. (4) G1_096: every conjugated column pairs to zero with
   u - v (pairing_eq), hence by the expansion star(u - v) pairs to zero with u - v, so u = v. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonMixed38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.G1098Basis NlsGge.Atomic.G1098Assembly NlsGge.Atomic.G1100Support

namespace NlsGge.Atomic.G1100
noncomputable section

/-- The wedge integral of two mixed kernels vanishes iff the real bracket of the columns does. -/
theorem bracket_zero_iff (u v : PhysicalL2) (k j : ℤ × Bool) :
    Bform (mixedColumn u v k.1 k.2) (mixedColumn u v j.1 j.2) = 0 ↔
      (∫ t in (0 : ℝ)..1,
        kernelWedge38 (mixedKernel u v k.1 k.2) (mixedKernel u v j.1 j.2) t) = 0 := by
  rw [show mixedColumn u v k.1 k.2 = (pairKernelL2Class38 (mixedKernel u v k.1 k.2)).1 from rfl,
    show mixedColumn u v j.1 j.2 = (pairKernelL2Class38 (mixedKernel u v j.1 j.2)).1 from rfl,
    wedge_integral_eq _ _ (mixedKernel_realSymmetric u v k.1 k.2)
      (mixedKernel_realSymmetric u v j.1 j.2)]
  have h2I : (-2 * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) Complex.I_ne_zero
  rw [mul_eq_zero, Complex.ofReal_eq_zero]
  constructor
  · intro h
    exact Or.inr h
  · rintro (h | h)
    · exact absurd h h2I
    · exact h

theorem wedge_integral_antisymm (K K' : PairKernelCont38) :
    (∫ t in (0 : ℝ)..1, kernelWedge38 K' K t) = -(∫ t in (0 : ℝ)..1, kernelWedge38 K K' t) := by
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro t _
  unfold kernelWedge38
  ring

/-- G1-100 (verbatim head of root/gpt6pro_followup7/handoff/definitions_design_20261027/STATEMENTS/G1.md line 699+;
Grebert-Kappeler, Section 10.9, Proposition 10.9). -/
theorem G1_100 : Function.Injective normingDirichletMap := by
  intro u v huv
  have h97 := NlsGge.GKDefinitionDesign.G1_097 u v huv
  have h96 := NlsGge.GKDefinitionDesign.G1_096 u v huv
  have h99 := NlsGge.Atomic.G1099.G1_099 u v
  have h98 := (NlsGge.Atomic.G1098.G1_098).2.1 u v
  set A : PhysicalL2 →L[ℝ] PhysicalL2 := mixedSquaredOperator u v with hAdef
  have hA : IsCompactOperator (A - 1 : PhysicalL2 →L[ℝ] PhysicalL2) := by
    have h0 := h99.1
    have hc := h99.2
    rw [h0] at hc
    exact hc
  -- the image of the normalized basis
  have hAd : ∀ k : ℤ × Bool, A (mixedRealBasis k) =
      (‖mixedReference k.1 k.2‖⁻¹ : ℝ) • mixedColumn u v k.1 k.2 := by
    intro k
    rw [mixedRealBasis_apply, mixedBasisVec_eq_smul, map_smul, h98 k.1 k.2]
  have hBd : ∀ k j : ℤ × Bool, Bform (A (mixedRealBasis k)) (A (mixedRealBasis j)) =
      (‖mixedReference k.1 k.2‖⁻¹ : ℝ) * (‖mixedReference j.1 j.2‖⁻¹ : ℝ) *
        Bform (mixedColumn u v k.1 k.2) (mixedColumn u v j.1 j.2) := by
    intro k j
    rw [hAd k, hAd j]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hpos : ∀ k : ℤ × Bool, (‖mixedReference k.1 k.2‖⁻¹ : ℝ) ≠ 0 := fun k =>
    inv_ne_zero (norm_mixedReference_pos k.1 k.2).ne'
  have hBzero : ∀ k j : ℤ × Bool,
      Bform (A (mixedRealBasis k)) (A (mixedRealBasis j)) = 0 ↔
        (∫ t in (0 : ℝ)..1,
          kernelWedge38 (mixedKernel u v k.1 k.2) (mixedKernel u v j.1 j.2) t) = 0 := by
    intro k j
    rw [hBd, ← bracket_zero_iff]
    constructor
    · intro h
      exact (mul_eq_zero.1 h).resolve_left (mul_ne_zero (hpos k) (hpos j))
    · intro h
      rw [h, mul_zero]
  -- the wedge integrals from G1-097
  have hW1 := fun m n => (h97.1 m n).1
  have hW2 := fun m n => (h97.1 m n).2.1
  have hW3 := fun m n => (h97.1 m n).2.2
  have hnz := h97.2
  have hσ : Function.Involutive (fun k : ℤ × Bool => (k.1, !k.2)) := by
    intro k
    simp
  have hB0 : ∀ k j : ℤ × Bool,
      Bform (A (mixedRealBasis k)) (A (mixedRealBasis j)) ≠ 0 → j = (k.1, !k.2) := by
    intro k j hne
    by_contra hj
    apply hne
    rw [hBzero]
    obtain ⟨m, a⟩ := k
    obtain ⟨n, b⟩ := j
    cases a <;> cases b
    · exact hW1 m n
    · have hmn : m ≠ n := fun h => hj (by subst h; rfl)
      simp only
      rw [hW3 m n, if_neg hmn]
    · have hmn : n ≠ m := fun h => hj (by subst h; rfl)
      simp only
      rw [wedge_integral_antisymm, hW3 n m, if_neg hmn, neg_zero]
    · exact hW2 m n
  have hB1 : ∀ k : ℤ × Bool,
      Bform (A (mixedRealBasis k)) (A (mixedRealBasis (k.1, !k.2))) ≠ 0 := by
    intro k
    rw [Ne, hBzero]
    obtain ⟨m, a⟩ := k
    cases a
    · simp only [Bool.not_false]
      rw [hW3 m m, if_pos rfl]
      exact hnz m
    · simp only [Bool.not_true]
      rw [wedge_integral_antisymm, hW3 m m, if_pos rfl, neg_eq_zero]
      exact hnz m
  have hd : ∀ h : PhysicalL2, ∃ ξ : ℤ × Bool → ℝ,
      HasSum (fun k => ξ k • mixedRealBasis k) h := fun h =>
    ⟨fun k => mixedRealBasis.repr h k, mixedRealBasis.hasSum_repr h⟩
  have hF7 := NlsGge.GK38.Lib.lemmaF7_of_bilinear A hA (fun k => mixedRealBasis k) hd Bform
    (fun k => (k.1, !k.2)) hσ hB0 hB1
  -- orthogonality of the conjugated columns to u - v (G1-096)
  have horth : ∀ k : ℤ × Bool,
      inner ℝ (star (mixedColumn u v k.1 k.2)) (u - v) = 0 := by
    intro k
    have h := h96 k.1 k.2
    rw [pairing_eq _ (mixedKernel_realSymmetric u v k.1 k.2), Complex.ofReal_eq_zero] at h
    exact (mul_eq_zero.1 h).resolve_left two_ne_zero
  set L : PhysicalL2 →L[ℝ] ℝ := ((innerSL ℝ).flip (u - v)).comp starLp.toContinuousLinearMap
    with hL
  have hLapply : ∀ x : PhysicalL2, L x = inner ℝ (star x) (u - v) := fun x => rfl
  obtain ⟨ξ, hξ⟩ := hF7.2 (star (u - v))
  have hsum := hξ.mapL L
  have hterm : (fun k : ℤ × Bool => L (ξ k • A (mixedRealBasis k))) = fun _ => 0 := by
    funext k
    rw [map_smul, hAd k, map_smul, hLapply, horth k, smul_zero, smul_zero]
  have hLs : L (star (u - v)) = 0 := by
    have hsum' : HasSum (fun k : ℤ × Bool => L (ξ k • A (mixedRealBasis k))) (L (star (u - v))) :=
      hsum
    rw [hterm] at hsum'
    exact hsum'.unique hasSum_zero
  rw [hLapply, star_star, real_inner_self_eq_norm_sq] at hLs
  have hnorm : ‖u - v‖ = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hLs
    exact this
  exact sub_eq_zero.1 (norm_eq_zero.1 hnorm)

end
end NlsGge.Atomic.G1100
