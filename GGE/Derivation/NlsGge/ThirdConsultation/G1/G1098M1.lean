import NlsGge.Atomic.G1.G1062
import NlsGge.ThirdConsultation.G1.G1098Host
import NlsGge.ThirdConsultation.G1.G1098MixBL
import NlsGge.ThirdConsultation.G1.G1098PairCLM
import NlsGge.ThirdConsultation.G1.G1098StateAnalytic
import NlsGge.GK38.IsolatingDefs
import NlsGge.GK38.IsolatingTopology
import NlsGge.GK38.IsolatingFamily

/-! # G1-098 M1 (proof development, AUTHOR; not reviewed): per-coordinate analyticity of complex mixed columns.
Proves `M1_stmt` (proof development G1098Stmt_CHECK02): for all real centres `u₀ v₀`, the open set `gkW ×ˢ gkW`
contains `(realSlice u₀, realSlice v₀)` and every complex mixed column `complexMixedColumn · · n minus` is
analytic on it. Route: the minus branch of `complexMixedKernel`, joint analyticity through the bounded
bilinear `mixedSquareBL` (generic `psi_comp_analyticAt`), composition with the bounded linear map
`colCLM = fst ∘ pairKernelL2CLM38`. No hypothesis is added. This file needs the supporting bodies
H181 (a),(b),(c) modules and the G1098 host (imported; root packaging per proof development review). -/
set_option autoImplicit false
open Filter Topology MeasureTheory Set
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38 NlsGge.GKDefinitionDesign

namespace NlsGge.Atomic.G1098M1
noncomputable section

/-- The first component of the actual L2 class, as a bounded ℂ-linear map on the sup-norm kernel space. -/
def g1098M1_colCLM : PairKernelCont38 →L[ℂ] PhysicalL2 :=
  (ContinuousLinearMap.fst ℂ PhysicalL2 PhysicalL2).comp pairKernelL2CLM38

theorem g1098M1_complexMixedColumn_eq (φ ψ : PotPair) (n : ℤ) (minus : Bool) :
    complexMixedColumn φ ψ n minus = g1098M1_colCLM (complexMixedKernel φ ψ n minus) := rfl

theorem g1098M1_complexDirState_eq (φ : PotPair) (n : ℤ) :
    complexDirState φ n = state φ (muSeq φ n) ![1, 1] := rfl

theorem g1098M1_complexMixedKernel_false (φ ψ : PotPair) (n : ℤ) :
    complexMixedKernel φ ψ n false =
      mixedSquareBL (complexDirState φ n) (complexDirState ψ n) := by
  simp [complexMixedKernel, mixedSquareBL_apply]

theorem g1098M1_complexMixedKernel_true (φ ψ : PotPair) (n : ℤ) :
    complexMixedKernel φ ψ n true =
      Complex.I • (mixedSquareBL (complexDirState φ n) (complexTerminalState ψ n) +
        mixedSquareBL (complexDirState ψ n) (complexTerminalState φ n)) := by
  simp [complexMixedKernel, mixedSquareBL_apply]

theorem g1098M1_dir_fst (n : ℤ) (p : PotPair × PotPair) (hp : p ∈ gkW ×ˢ gkW) :
    AnalyticAt ℂ (fun q : PotPair × PotPair => complexDirState q.1 n) p :=
  (analyticOnNhd_state_muSeq_const n ![1, 1] p.1 hp.1).comp
    (analyticAt_fst : AnalyticAt ℂ (fun q : PotPair × PotPair => q.1) p)

theorem g1098M1_dir_snd (n : ℤ) (p : PotPair × PotPair) (hp : p ∈ gkW ×ˢ gkW) :
    AnalyticAt ℂ (fun q : PotPair × PotPair => complexDirState q.2 n) p :=
  (analyticOnNhd_state_muSeq_const n ![1, 1] p.2 hp.2).comp
    (analyticAt_snd : AnalyticAt ℂ (fun q : PotPair × PotPair => q.2) p)

theorem g1098M1_term_fst (n : ℤ) (p : PotPair × PotPair) (hp : p ∈ gkW ×ˢ gkW) :
    AnalyticAt ℂ (fun q : PotPair × PotPair => complexTerminalState q.1 n) p :=
  (analyticOnNhd_state_muSeq_terminal n p.1 hp.1).comp
    (analyticAt_fst : AnalyticAt ℂ (fun q : PotPair × PotPair => q.1) p)

theorem g1098M1_term_snd (n : ℤ) (p : PotPair × PotPair) (hp : p ∈ gkW ×ˢ gkW) :
    AnalyticAt ℂ (fun q : PotPair × PotPair => complexTerminalState q.2 n) p :=
  (analyticOnNhd_state_muSeq_terminal n p.2 hp.2).comp
    (analyticAt_snd : AnalyticAt ℂ (fun q : PotPair × PotPair => q.2) p)

/-- The complex mixed kernel is analytic in the pair of potentials on `gkW ×ˢ gkW`, for each `n`, `minus`. -/
theorem g1098M1_kernel_analyticAt (n : ℤ) (minus : Bool) (p : PotPair × PotPair)
    (hp : p ∈ gkW ×ˢ gkW) :
    AnalyticAt ℂ (fun q : PotPair × PotPair => complexMixedKernel q.1 q.2 n minus) p := by
  cases minus with
  | false =>
    have heq : (fun q : PotPair × PotPair => complexMixedKernel q.1 q.2 n false) =
        fun q => mixedSquareBL (complexDirState q.1 n) (complexDirState q.2 n) :=
      funext fun q => g1098M1_complexMixedKernel_false q.1 q.2 n
    rw [heq]
    exact psi_comp_analyticAt mixedSquareBL (g1098M1_dir_fst n p hp) (g1098M1_dir_snd n p hp)
  | true =>
    have heq : (fun q : PotPair × PotPair => complexMixedKernel q.1 q.2 n true) =
        fun q => Complex.I • (mixedSquareBL (complexDirState q.1 n) (complexTerminalState q.2 n) +
          mixedSquareBL (complexDirState q.2 n) (complexTerminalState q.1 n)) :=
      funext fun q => g1098M1_complexMixedKernel_true q.1 q.2 n
    rw [heq]
    have hA := psi_comp_analyticAt mixedSquareBL (g1098M1_dir_fst n p hp) (g1098M1_term_snd n p hp)
    have hB := psi_comp_analyticAt mixedSquareBL (g1098M1_dir_snd n p hp) (g1098M1_term_fst n p hp)
    have hs := AnalyticAt.const_smul (c := Complex.I) (hA.add hB)
    exact hs

/-- Each complex mixed column is analytic on `gkW ×ˢ gkW`. -/
theorem g1098M1_column_analyticOnNhd (n : ℤ) (minus : Bool) :
    AnalyticOnNhd ℂ (fun p : PotPair × PotPair => complexMixedColumn p.1 p.2 n minus) (gkW ×ˢ gkW) := by
  intro p hp
  have heq : (fun q : PotPair × PotPair => complexMixedColumn q.1 q.2 n minus) =
      g1098M1_colCLM ∘ (fun q : PotPair × PotPair => complexMixedKernel q.1 q.2 n minus) :=
    funext fun q => g1098M1_complexMixedColumn_eq q.1 q.2 n minus
  rw [heq]
  exact (g1098M1_colCLM.analyticAt _).comp (g1098M1_kernel_analyticAt n minus p hp)

/-- M1 (proof): the open set `gkW ×ˢ gkW` witnesses the statement for every real centre pair. -/
theorem g1098M1_proof : ∀ u₀ v₀ : PhysicalL2, ∃ U : Set (PotPair × PotPair), IsOpen U ∧
    (realSlice u₀, realSlice v₀) ∈ U ∧
    ∀ (n : ℤ) (minus : Bool),
      AnalyticOnNhd ℂ (fun p : PotPair × PotPair => complexMixedColumn p.1 p.2 n minus) U :=
  fun u₀ v₀ => ⟨gkW ×ˢ gkW, isOpen_gkW.prod isOpen_gkW,
    ⟨realSlice_mem_gkW u₀, realSlice_mem_gkW v₀⟩,
    fun n minus => g1098M1_column_analyticOnNhd n minus⟩

end
end NlsGge.Atomic.G1098M1

namespace NlsGge.Atomic.G1098M1

/-- M1 statement (proof development G1098Stmt_CHECK02, verbatim). -/
def M1_stmt : Prop :=
  ∀ u₀ v₀ : PhysicalL2, ∃ U : Set (PotPair × PotPair), IsOpen U ∧
    (realSlice u₀, realSlice v₀) ∈ U ∧
    ∀ (n : ℤ) (minus : Bool),
      AnalyticOnNhd ℂ (fun p : PotPair × PotPair => complexMixedColumn p.1 p.2 n minus) U

theorem M1_stmt_holds : M1_stmt := g1098M1_proof

end NlsGge.Atomic.G1098M1
