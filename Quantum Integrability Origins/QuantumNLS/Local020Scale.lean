import Mathlib
import QuantumNLS.LocalSpectralReduced
import QuantumNLS.Local020Abs

/-! LOCAL-020 stage S1: scaling.  `LuGraph L κ (s u) σ = LuGraph L (κ s²) u σ` for `s ≥ 0` (since
`√κ · s = √(κ s²)`), hence every object built from the graph (resolvent, Riesz projections, the dressed integral,
the compression, `SmallCompression`, the normalized isometry and the reduced matrix) at `(κ, s u)` is the one at
`(κ s², u)`.  Also: the graph depends on the potential only through its `μI L`-almost-everywhere class. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open MeasureTheory QuantumNLS.LocalSpectral

namespace QuantumNLS.Local020Scale

variable {L κ : ℝ}

theorem lopPt_scale {s : ℝ} (hs : 0 ≤ s) (w : ℂ) (d g : E2) :
    lopPt κ ((s : ℂ) * w) d g = lopPt (κ * s ^ 2) w d g := by
  have h1 : Real.sqrt (κ * s ^ 2) = Real.sqrt κ * s := by
    rw [Real.sqrt_mul' _ (sq_nonneg s), Real.sqrt_sq hs]
  unfold lopPt
  rw [h1]
  simp only [map_mul, Complex.conj_ofReal]
  push_cast
  congr 2 <;> congr 1 <;> ring

/-- **Scaling of the graph.** -/
theorem LuGraph_scale {s : ℝ} (hs : 0 ≤ s) (u : ℝ → ℂ) (σ : ℤˣ) :
    LuGraph L κ (fun x => (s : ℂ) * u x) σ = LuGraph L (κ * s ^ 2) u σ := by
  ext p
  unfold LuGraph
  simp only [Set.mem_setOf_eq, lopPt_scale hs]

/-- The graph depends on the potential only through its a.e. class. -/
theorem LuGraph_congr_ae {u u' : ℝ → ℂ} (h : u =ᵐ[μI L] u') (σ : ℤˣ) :
    LuGraph L κ u σ = LuGraph L κ u' σ := by
  ext p
  unfold LuGraph
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨g, hh, h1, h2, h3⟩
    refine ⟨g, hh, h1, h2, ?_⟩
    filter_upwards [h3, h] with x hx hux
    rw [hx, hux]
  · rintro ⟨g, hh, h1, h2, h3⟩
    refine ⟨g, hh, h1, h2, ?_⟩
    filter_upwards [h3, h] with x hx hux
    rw [hx, hux]

theorem resolvent_scale {s : ℝ} (hs : 0 ≤ s) (u : ℝ → ℂ) (σ : ℤˣ) (z : ℂ) :
    resolvent L κ (fun x => (s : ℂ) * u x) σ z = resolvent L (κ * s ^ 2) u σ z := by
  unfold QuantumNLS.LocalSpectral.resolvent IsResolvent
  rw [LuGraph_scale hs]

theorem rieszProj_scale {s : ℝ} (hs : 0 ≤ s) (u : ℝ → ℂ) (σ : ℤˣ) (n : ℤ) (r : ℝ) :
    rieszProj L κ (fun x => (s : ℂ) * u x) σ n r = rieszProj L (κ * s ^ 2) u σ n r := by
  unfold rieszProj
  simp only [resolvent_scale hs]

theorem dressedIntegral_scale {s : ℝ} (hs : 0 ≤ s) (u : ℝ → ℂ) (n : ℤ) (r : ℝ) :
    dressedIntegral L κ (fun x => (s : ℂ) * u x) n r = dressedIntegral L (κ * s ^ 2) u n r := by
  unfold dressedIntegral
  simp only [resolvent_scale hs]

theorem perturbedProj_scale {s : ℝ} (hs : 0 ≤ s) (u : ℝ → ℂ) (n : ℤ) (r : ℝ) :
    perturbedProj L κ (fun x => (s : ℂ) * u x) n r = perturbedProj L (κ * s ^ 2) u n r :=
  rieszProj_scale hs u _ n r

theorem compressionMatrix_scale {s : ℝ} (hs : 0 ≤ s) (u : ℝ → ℂ) (n : ℤ) (r : ℝ) :
    compressionMatrix L κ (fun x => (s : ℂ) * u x) n r = compressionMatrix L (κ * s ^ 2) u n r := by
  unfold compressionMatrix
  rw [perturbedProj_scale hs]

theorem smallCompression_scale {s : ℝ} (hs : 0 ≤ s) (u : ℝ → ℂ) (n : ℤ) (r : ℝ) :
    SmallCompression L κ (fun x => (s : ℂ) * u x) n r ↔ SmallCompression L (κ * s ^ 2) u n r := by
  unfold SmallCompression
  rw [compressionMatrix_scale hs]

/-- **S1 (scaling of the reduced matrix).** -/
theorem reducedMatrix2_scale {s : ℝ} (hs : 0 ≤ s) (u : ℝ → ℂ) (n : ℤ) (r : ℝ)
    (h : SmallCompression L κ (fun x => (s : ℂ) * u x) n r)
    (h' : SmallCompression L (κ * s ^ 2) u n r) :
    reducedMatrix2 L κ (fun x => (s : ℂ) * u x) n r h = reducedMatrix2 L (κ * s ^ 2) u n r h' := by
  unfold reducedMatrix2 normalizedIsometry2 invSqrtCompression
  rw [perturbedProj_scale hs, compressionMatrix_scale hs, dressedIntegral_scale hs]

end QuantumNLS.Local020Scale

#print axioms QuantumNLS.Local020Scale.LuGraph_scale
#print axioms QuantumNLS.Local020Scale.LuGraph_congr_ae
#print axioms QuantumNLS.Local020Scale.reducedMatrix2_scale
#print axioms QuantumNLS.Local020Scale.smallCompression_scale
