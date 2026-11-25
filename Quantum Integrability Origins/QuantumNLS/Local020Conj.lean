import Mathlib
import QuantumNLS.LocalSpectralReduced
import QuantumNLS.Local020AbsA
import QuantumNLS.Local020CoreA
import QuantumNLS.Local020Mul1
import QuantumNLS.Local020Entry
import QuantumNLS.Local020Refl

/-! LOCAL-020 stage S5c: componentwise conjugation `K` on `ℂ²` and on `H2 L = L²(0,L;ℂ²)`, as `AntiU` structures;
`K` carries the graph of `𝓛_u` to the graph of `-𝓛_{ū}` (`inter_conj`), `Kχ_{n,j} = χ_{-n,j}`, and the reduced matrices
satisfy `B_{-n}(ū) = -K B_n(u) K`, in particular `b_{-n}(ū) = - conj b_n(u)`. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Filter Topology QuantumNLS.LocalSpectral QuantumNLS.Local020Abs QuantumNLS.Local020AbsA
  QuantumNLS.Local020Mul1 ComplexConjugate
open scoped ENNReal InnerProductSpace

namespace QuantumNLS.Local020Conj

variable {L κ : ℝ}

/-- Componentwise conjugation on `ℂ²`. -/
def kE (v : E2) : E2 := vec2 (conj (v 0)) (conj (v 1))

theorem kE_apply (v : E2) (i : Fin 2) : kE v i = conj (v i) := by
  fin_cases i <;> simp [kE, vec2]

theorem kE_add (v w : E2) : kE (v + w) = kE v + kE w := by
  ext i; simp [kE_apply]

theorem kE_neg (v : E2) : kE (-v) = -kE v := by
  ext i; simp [kE_apply]

theorem kE_smul (c : ℂ) (v : E2) : kE (c • v) = conj c • kE v := by
  ext i; simp [kE_apply]

theorem kE_kE (v : E2) : kE (kE v) = v := by
  ext i; simp [kE_apply]

theorem norm_kE (v : E2) : ‖kE v‖ = ‖v‖ := by
  have h : ‖kE v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two, kE_apply]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

theorem inner_kE (v w : E2) : ⟪kE v, kE w⟫_ℂ = conj ⟪v, w⟫_ℂ := by
  simp only [kE, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two, vec2, map_add, map_mul]
  simp [mul_comm]

/-- `kE` as a real-linear isometry. -/
def kEL : E2 →ₗᵢ[ℝ] E2 where
  toFun := kE
  map_add' := kE_add
  map_smul' := fun r v => by
    have := kE_smul (r : ℂ) v
    rw [Complex.conj_ofReal] at this
    simpa [Complex.coe_smul] using this
  norm_map' := norm_kE

def AE2 : AntiU E2 where
  K := kEL
  smul := kE_smul
  invol := kE_kE
  inner := inner_kE

theorem memLp_kEf (f : H2 L) : MemLp (fun x => kE ((f : ℝ → E2) x)) 2 (μI L) := by
  have hm : AEStronglyMeasurable (fun x => kE ((f : ℝ → E2) x)) (μI L) :=
    kEL.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)
  have hg : MemLp (f : ℝ → E2) 2 (μI L) := Lp.memLp f
  have hle : ∀ᵐ x ∂(μI L), ‖kE ((f : ℝ → E2) x)‖ ≤ ‖(f : ℝ → E2) x‖ :=
    Eventually.of_forall (fun x => (norm_kE _).le)
  first
    | exact MemLp.mono hg hm hle
    | exact MemLp.of_le hg hm hle

def KLp (f : H2 L) : H2 L := (memLp_kEf f).toLp _

theorem KLp_ae (f : H2 L) : (KLp f : ℝ → E2) =ᵐ[μI L] fun x => kE ((f : ℝ → E2) x) :=
  (memLp_kEf f).coeFn_toLp

theorem KLp_add (f g : H2 L) : KLp (f + g) = KLp f + KLp g := by
  apply Lp.ext
  filter_upwards [KLp_ae (f + g), KLp_ae f, KLp_ae g, Lp.coeFn_add (KLp f) (KLp g), Lp.coeFn_add f g]
    with x h1 h2 h3 h4 h5
  simp only [Pi.add_apply] at h4 h5
  rw [h1, h4, h2, h3, h5, kE_add]

theorem KLp_smul (c : ℂ) (f : H2 L) : KLp (c • f) = conj c • KLp f := by
  apply Lp.ext
  filter_upwards [KLp_ae (c • f), KLp_ae f, Lp.coeFn_smul (conj c) (KLp f), Lp.coeFn_smul c f] with x h1 h2 h3 h4
  simp only [Pi.smul_apply] at h3 h4
  rw [h1, h3, h2, h4, kE_smul]

theorem norm_KLp (f : H2 L) : ‖KLp f‖ = ‖f‖ := by
  have hae : ∀ᵐ x ∂(μI L), ‖(KLp f : ℝ → E2) x‖ = ‖(f : ℝ → E2) x‖ := by
    filter_upwards [KLp_ae f] with x hx
    rw [hx, norm_kE]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (hae.mono fun _ hx => hx.le))
    (Lp.norm_le_norm_of_ae_le (hae.mono fun _ hx => hx.ge))

theorem KLp_KLp (f : H2 L) : KLp (KLp f) = f := by
  apply Lp.ext
  filter_upwards [KLp_ae (KLp f), KLp_ae f] with x h1 h2
  rw [h1, h2, kE_kE]

def AH : AntiU (H2 L) where
  K :=
    { toFun := KLp
      map_add' := KLp_add
      map_smul' := fun r f => by
        have := KLp_smul (r : ℂ) f
        rw [Complex.conj_ofReal] at this
        simpa [Complex.coe_smul] using this
      norm_map' := norm_KLp }
  smul := KLp_smul
  invol := KLp_KLp
  inner f g := by
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def, ← integral_conj]
    refine integral_congr_ae ?_
    filter_upwards [KLp_ae f, KLp_ae g] with x h1 h2
    show ⟪(KLp f : ℝ → E2) x, (KLp g : ℝ → E2) x⟫_ℂ = _
    rw [h1, h2, inner_kE]

theorem AH_apply (f : H2 L) : (AH (L := L)).K f = KLp f := rfl

theorem KLp_neg (f : H2 L) : KLp (-f) = -KLp f := by
  have := KLp_smul (-1 : ℂ) f
  simpa using this

theorem kE_single (j : Fin 2) : kE (EuclideanSpace.single j (1 : ℂ)) = EuclideanSpace.single j (1 : ℂ) := by
  ext i; simp [kE_apply, EuclideanSpace.single_apply]

theorem conj_rate (n : ℤ) (j : Fin 2) : conj (rate L n j) = -rate L n j := by
  unfold rate
  simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

theorem KLp_chi (n : ℤ) (j : Fin 2) : KLp (chi L n j) = chi L (-n) j := by
  apply Lp.ext
  filter_upwards [KLp_ae (chi L n j), (memLp_chiFun L n j).coeFn_toLp,
    (memLp_chiFun L (-n) j).coeFn_toLp] with x h1 h2 h3
  have e2 : (chi L n j : ℝ → E2) x = chiFun L n j x := h2
  have e3 : (chi L (-n) j : ℝ → E2) x = chiFun L (-n) j x := h3
  rw [h1, e2, e3]
  unfold chiFun
  rw [kE_smul, kE_single]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, conj_rate, Complex.conj_ofReal]
  rw [Local020Refl.rate_neg]

theorem embed_conj (n : ℤ) : embed L (-n) = cjT AE2 AH (embed L n) := by
  ext v : 1
  rw [cjT_apply, embed_apply, embed_apply]
  show _ = KLp (embed L n (kE v))
  rw [embed_apply, KLp_add, KLp_smul, KLp_smul, KLp_chi, KLp_chi]
  simp [kE_apply]

theorem lopPt_conj (κ : ℝ) (w : ℂ) (d g : E2) : lopPt κ (conj w) (kE d) (kE g) = -(kE (lopPt κ w d g)) := by
  unfold lopPt Jm kE
  have h2 : (starRingEnd ℂ) 2 = 2 := map_ofNat _ 2
  ext i; fin_cases i <;> simp [vec2, h2] <;> ring

theorem memLp_kE_comp {h : ℝ → E2} (hh : MemLp h 2 (μI L)) : MemLp (fun x => kE (h x)) 2 (μI L) := by
  have hm : AEStronglyMeasurable (fun x => kE (h x)) (μI L) :=
    kEL.continuous.comp_aestronglyMeasurable hh.aestronglyMeasurable
  have hle : ∀ᵐ x ∂(μI L), ‖kE (h x)‖ ≤ ‖h x‖ := Eventually.of_forall (fun x => (norm_kE _).le)
  first
    | exact MemLp.mono hh hm hle
    | exact MemLp.of_le hh hm hle

theorem kE_integral {h : ℝ → E2} {x : ℝ} (hi : IntervalIntegrable h volume 0 x) :
    ∫ s in (0 : ℝ)..x, kE (h s) = kE (∫ s in (0 : ℝ)..x, h s) := by
  have := ContinuousLinearMap.intervalIntegral_comp_comm (kEL.toContinuousLinearMap) hi
  exact this

theorem fwd (hL : 0 < L) (u : ℝ → ℂ) (σ : ℤˣ) {f φ : H2 L} (h : (f, φ) ∈ LuGraph L κ u σ) :
    (KLp f, -KLp φ) ∈ LuGraph L κ (fun x => conj (u x)) σ := by
  obtain ⟨g, d, hrep, hbc, hφ⟩ := h
  refine ⟨fun x => kE (g x), fun x => kE (d x), ⟨?_, memLp_kE_comp hrep.2.1, ?_⟩, ?_, ?_⟩
  · filter_upwards [KLp_ae f, hrep.1] with x a b
    rw [a, b]
  · intro x hx
    have hi := rep_intervalIntegrable hL.le hrep
    have hi' : IntervalIntegrable d volume 0 x := hi.mono_set (by
      rw [uIcc_of_le hL.le, uIcc_of_le hx.1]; exact Icc_subset_Icc_right hx.2)
    simp only
    rw [hrep.2.2 x hx, kE_add, kE_integral hi']
  · simp only
    rw [hbc, kE_smul]
    have : conj (((σ : ℤ) : ℂ)) = ((σ : ℤ) : ℂ) := map_intCast _ _
    rw [this]
  · filter_upwards [Lp.coeFn_neg (KLp φ), KLp_ae φ, hφ] with x a b c
    rw [a, Pi.neg_apply, b, c, lopPt_conj]

theorem inter_conj (hL : 0 < L) (u : ℝ → ℂ) (σ : ℤˣ) :
    InterA (LuGraph L κ u σ) (LuGraph L κ (fun x => conj (u x)) σ) (AH (L := L)) := by
  refine ⟨fun f φ => ⟨fun h => fwd hL u σ h, fun h => ?_⟩, fun f φ h => Local020Refl.LuGraph_neg h⟩
  have h' : (KLp f, -KLp φ) ∈ LuGraph L κ (fun x => conj (u x)) σ := h
  have h2 := fwd hL _ σ h'
  simp only [Complex.conj_conj] at h2
  rw [KLp_KLp, KLp_neg, KLp_KLp, neg_neg] at h2
  exact h2

theorem bentry_cjT (B : E2 →L[ℂ] E2) :
    QuantumNLS.Local020Entry.bentry (cjT AE2 AE2 B) = conj (QuantumNLS.Local020Entry.bentry B) := by
  unfold QuantumNLS.Local020Entry.bentry
  rw [cjT_apply]
  have h : AE2.K (vec2 1 0) = vec2 1 0 := by
    show kE (vec2 1 0) = vec2 1 0
    ext i; fin_cases i <;> simp [kE, vec2]
  rw [h]
  show kE (B (vec2 1 0)) 1 = _
  exact kE_apply _ 1

/-- **S5 (conjugation).**  For `u' = ū`: `b_{-n}(ū) = - conj b_n(u)`. -/
theorem conj_reduced (hL : 0 < L) (n : ℤ) (r : ℝ) (u : ℝ → ℂ) :
    (SmallCompression L κ (fun x => conj (u x)) (-n) r ↔ SmallCompression L κ u n r) ∧
    ∀ (h' : SmallCompression L κ (fun x => conj (u x)) (-n) r) (hh : SmallCompression L κ u n r),
      QuantumNLS.Local020Entry.bentry (reducedMatrix2 L κ (fun x => conj (u x)) (-n) r h') =
        -conj (QuantumNLS.Local020Entry.bentry (reducedMatrix2 L κ u n r hh)) := by
  have h : InterA (LuGraph L κ u (parity n)) (LuGraph L κ (fun x => conj (u x)) (parity (-n))) AH := by
    rw [Local020Refl.parity_neg' n]; exact inter_conj hL u (parity n)
  have hn : center L (-n) = -(conj (center L n)) := by
    unfold QuantumNLS.LocalSpectral.center
    rw [Local020Refl.pm_neg', Complex.conj_ofReal]; push_cast; ring
  obtain ⟨hs, hr⟩ := QuantumNLS.Local020CoreA.reduced_transportA (κ := κ) (KE := AE2) r h hn (embed_conj n)
  refine ⟨hs, fun h' hh => ?_⟩
  rw [hr h' hh]
  have e1 : QuantumNLS.Local020Entry.bentry ((pm L (-n) : ℂ) • ContinuousLinearMap.id ℂ E2) = 0 :=
    QuantumNLS.Local020Entry.bentry_id _
  rw [sub_eq_add_neg, QuantumNLS.Local020Entry.bentry_add, e1, zero_add]
  have : QuantumNLS.Local020Entry.bentry (-(cjT AE2 AE2 (reducedMatrix2 L κ u n r hh -
      (pm L n : ℂ) • ContinuousLinearMap.id ℂ E2))) =
      -conj (QuantumNLS.Local020Entry.bentry (reducedMatrix2 L κ u n r hh)) := by
    have hneg : ∀ A : E2 →L[ℂ] E2, QuantumNLS.Local020Entry.bentry (-A) = -QuantumNLS.Local020Entry.bentry A := by
      intro A; simp [QuantumNLS.Local020Entry.bentry]
    rw [hneg, bentry_cjT, QuantumNLS.Local020Entry.bentry_sub, QuantumNLS.Local020Entry.bentry_id, sub_zero]
  exact this

end QuantumNLS.Local020Conj

#print axioms QuantumNLS.Local020Conj.conj_reduced
#print axioms QuantumNLS.Local020Conj.inter_conj
