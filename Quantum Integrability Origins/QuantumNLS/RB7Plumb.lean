import Mathlib
import QuantumNLS.RF535Final
import QuantumNLS.RB7Bridge

/-!
# R-7B122087 `thm:hierarchy`, A8 plumbing: `RB7Chart.chart_dI` instantiated with the accepted global chart `RF535Final.global_actual_chart`

Printed: "Full Hilbert symplecticity, tested against smooth variations, identifies its derivative with `-i ∇I_{r+1}(u(t))`."

* `ChartFacts hκ`: the accepted chart of R-F5355ABD (`RF535Final.global_actual_chart`) in the form used by the hierarchy modules: `Φ : L² → ℓ²` with inverse `Ψ` (both real analytic),
  `|Φ_n(u)|² = I_n^{(κ)}(u)` (this is `RB7Moment.ChartData`), `Ψ ∘ Φ = id`, strong symplecticity `2 Im⟨DΦ(u)h, DΦ(u)k⟩ = 2 Im⟨h,k⟩` with `DΦ = fderiv ℝ Φ u`, and the bounded
  isomorphism `e = DΦ(u)` with `D(Φ⁻¹)(Φ u) = e⁻¹`.  `chartFacts_exists`: such data exist, for every `κ > 0`, from the accepted theorem alone (premise `[Fact (0 < L)]`).
* `dI_RF535`: for `F` `C²` and coordinatewise-rotation invariant on `h^S`, a smooth point `u` (its coordinates `Φ(u)` lie in `h^{2S}`) and `v := (DΦ(u))⁻¹(-iG)`, `G` the `ℓ²` coordinate
  gradient of `F` at `Φ(u)` (`Gl`): for every direction `h` whose chart curve `ε ↦ Φ(u + εh)` is continuous into `h^{2S}` (REG-015 homeomorphism clause, see `RB7Bridge.curve_continuous`)
  and every functional `I` with `I(u + εh) = F(Φ(u + εh))`:  `d/dε I(u + εh)|₀ = 2 Re⟨i v, h⟩` (DEF-015: `v = -i ∇I(u)` tested against `h`).  `v` depends only on `u`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology
open MeasureTheory

namespace QuantumNLS.RB7

open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight QuantumNLS.PhysicalTensor
open QuantumNLS.D01LocalPrimitive (K)

variable {L κ : ℝ} [Fact (0 < L)]

/-- The accepted global actual chart in the form used by the hierarchy modules. -/
structure ChartFacts (hκ : 0 < κ) extends ChartData (L := L) hκ where
  ana_Φ : ∀ u, AnalyticAt ℝ Φ u
  ana_Ψ : ∀ z, AnalyticAt ℝ Ψ z
  ΨΦ : ∀ u, Ψ (Φ u) = u
  symp : ∀ (u h k : L2T L), 2 * (inner ℂ (fderiv ℝ Φ u h) (fderiv ℝ Φ u k)).im = 2 * (inner ℂ h k).im
  iso : ∀ u, ∃ e : L2T L ≃L[ℝ] K, HasFDerivAt Φ (e : L2T L →L[ℝ] K) u ∧
    HasFDerivAt Ψ (e.symm : K →L[ℝ] L2T L) (Φ u)

/-- **The chart data exist**, from the accepted `RF535Final.global_actual_chart` (only `[Fact (0 < L)]`). -/
theorem chartFacts_exists (hκ : 0 < κ) : Nonempty (ChartFacts (L := L) hκ) := by
  obtain ⟨⟨d, CL, hd, hCL, Φloc, Ψloc, hloc⟩, hglob⟩ := QuantumNLS.RF535Final.global_actual_chart L
  have G := hglob d CL Φloc Ψloc hd hCL hloc κ hκ
  obtain ⟨_, Y, F, Φ, Ψ, _, _, _, _, _, _, _, hAΦ, hAΨ, hΨΦ, hΦΨ, hmass, _, hsymp, hiso, _, _, _, _, _, _, _⟩ := G
  exact ⟨{ Φ := Φ, Ψ := Ψ, ΦΨ := hΦΨ, mass := hmass, ana_Φ := hAΦ, ana_Ψ := hAΨ, ΨΦ := hΨΦ,
           symp := hsymp, iso := hiso }⟩

/-- The `ℓ²` coordinate gradient of `F` at `ζ ∈ h^{2S}` (`RB7Unif.Gs`, square summable). -/
def Gl {W U : PosWeight} (c : Cmp W U) {F : WSeq W → ℝ} (hF : ContDiff ℝ 2 F)
    (hinv : ∀ (u : ℤ → Circle) z, F (rot u z) = F z) (y : WSeq U) : lp (fun _ : ℤ => ℂ) 2 :=
  ⟨Gs F c y, memℓ2_of_summable _ (summable_Gs_sq c hF hinv y)⟩

theorem Gl_val {W U : PosWeight} (c : Cmp W U) {F : WSeq W → ℝ} (hF : ContDiff ℝ 2 F)
    (hinv : ∀ (u : ℤ → Circle) z, F (rot u z) = F z) (y : WSeq U) :
    ((Gl c hF hinv y : lp (fun _ : ℤ => ℂ) 2) : ℤ → ℂ) = Gs F c y := rfl

/-- **A8, instantiated with the accepted chart** (see the module docstring). -/
theorem dI_RF535 (hκ : 0 < κ) (C : ChartFacts (L := L) hκ) {S : ℝ} (hS : 0 ≤ S)
    {F : h02 L S → ℝ} (hF : ContDiff ℝ 2 F) (hinv : ∀ (u : ℤ → Circle) z, F (rot u z) = F z)
    (I : L2T L → ℝ) (u : L2T L) (ζ0 : h02 L (2 * S)) (hζ0 : ∀ n, ζ0.val n = C.Φ u n) :
    ∃ v : L2T L, fderiv ℝ C.Φ u v = -Complex.I • Gl (cmp_def002 (L := L) hS) hF hinv ζ0 ∧
      ∀ (h : L2T L) (ζ : ℝ → h02 L (2 * S)), Continuous ζ →
        (∀ (ε : ℝ) (n : ℤ), (ζ ε).val n = C.Φ (u + ε • h) n) →
        (∀ ε : ℝ, I (u + ε • h) = F (iWU (cmp_def002 (L := L) hS) (ζ ε))) →
        HasDerivAt (fun ε : ℝ => I (u + ε • h)) (2 * (inner ℂ (Complex.I • v) h).re) 0 := by
  obtain ⟨e, he, -⟩ := C.iso u
  have hD : fderiv ℝ C.Φ u = (e : L2T L →L[ℝ] K) := he.fderiv
  refine ⟨e.symm (-Complex.I • Gl (cmp_def002 (L := L) hS) hF hinv ζ0), ?_, ?_⟩
  · rw [hD]; simp
  · intro h ζ hζ hcoord hI
    have hζ00 : ζ 0 = ζ0 := by
      refine WSeq.ext (funext fun n => ?_)
      rw [hcoord 0 n, hζ0 n]
      simp
    have hv : (e : L2T L →L[ℝ] K) (e.symm (-Complex.I • Gl (cmp_def002 (L := L) hS) hF hinv ζ0)) =
        -Complex.I • Gl (cmp_def002 (L := L) hS) hF hinv ζ0 := by simp
    refine chart_dI (cmp_def002 (L := L) hS) hF hinv C.Φ I u h (e : L2T L →L[ℝ] K) he ?_ ζ hζ hcoord hI
      (Gl (cmp_def002 (L := L) hS) hF hinv ζ0) ?_ _ hv
    · intro a b
      have := C.symp u a b
      rwa [hD] at this
    · rw [Gl_val, hζ00]

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.chartFacts_exists
#print axioms QuantumNLS.RB7.dI_RF535
