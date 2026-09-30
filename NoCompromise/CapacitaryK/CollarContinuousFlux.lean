module

public import NoCompromise.CapacitaryK.Calculus
public import NoCompromise.BV.StrictApprox
public import NoCompromise.Area.Linear
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

@[expose] public section

/-!
# Surface fluxes of continuous fields by uniform smooth approximation

Chapter 31 (`CapacitaryK`), collar endpoint step. A continuous vector field on
`ℝ³` is uniformly approximated on a compact set by smooth compactly supported
fields (`exists_contDiff_near_continuous`). Consequently, if the fluxes
`∫_{Σ_s} ⟪Z, ν⟫` of every `C¹` compactly supported field converge to
`∫_S ⟪Z, n⟫`, the surfaces lie in a fixed compact set, have uniformly bounded
area, and the normals have norm at most one, then the same convergence holds
for every continuous field (`tendsto_flux_of_continuous`).
-/

noncomputable section

open MeasureTheory Filter Metric Set
open scoped Topology ENNReal RealInnerProductSpace

namespace LiquidDrop.CapacitaryK

/-- Uniform approximation on a compact set of a continuous vector field on `ℝ³` by a
smooth compactly supported vector field. -/
theorem exists_contDiff_near_continuous {Y : E3 → E3} (hY : Continuous Y) {C : Set E3}
    (hC : IsCompact C) {ε : ℝ} (hε : 0 < ε) :
    ∃ Z : E3 → E3, ContDiff ℝ (⊤ : ℕ∞) Z ∧ HasCompactSupport Z ∧
      ∀ x ∈ C, ‖Y x - Z x‖ ≤ ε := by
  have hUC : UniformContinuousOn Y (cthickening 1 C) :=
    hC.cthickening.uniformContinuousOn_of_continuous hY.continuousOn
  rcases Metric.uniformContinuousOn_iff.mp hUC ε hε with ⟨δ, hδ, hYδ⟩
  rcases hY.exists_contDiff_dist_le_of_forall_mem_ball_dist_le (lt_min one_pos hδ) with
    ⟨g, hgc, hg⟩
  obtain ⟨ζ, hζ, hcζ, -, hone, -⟩ :=
    exists_smooth_cutoff_one_near_compact hC isOpen_univ (subset_univ C)
  refine ⟨fun x => ζ x • g x, hζ.smul hgc, hcζ.smul_right, fun x hx => ?_⟩
  have hζx : ζ x = 1 := hone.self_of_nhdsSet x hx
  change ‖Y x - ζ x • g x‖ ≤ ε
  rw [hζx, one_smul, ← dist_eq_norm, dist_comm]
  refine hg x ε fun y hy => ?_
  rw [mem_ball, lt_min_iff] at hy
  exact (hYδ y (mem_cthickening_of_dist_le y x 1 C hx hy.1.le) x
    (self_subset_cthickening C hx) hy.2).le

/-- A bounded-normal flux of a continuous field over a finite-measure set inside a
compact set is integrable. -/
theorem integrableOn_inner_of_continuous {μ : Measure E3} {T C : Set E3} {W m : E3 → E3}
    (hW : Continuous W) (hC : IsCompact C) (hTC : T ⊆ C) (hT : MeasurableSet T)
    (hTfin : μ T < ⊤) (hm : ∀ x ∈ T, ‖m x‖ ≤ 1)
    (hmm : AEStronglyMeasurable m (μ.restrict T)) :
    IntegrableOn (fun x => ⟪W x, m x⟫) T μ := by
  obtain ⟨K, hK⟩ := hC.exists_bound_of_continuousOn hW.continuousOn
  have : IsFiniteMeasure (μ.restrict T) := ⟨by rw [Measure.restrict_apply_univ]; exact hTfin⟩
  refine Integrable.of_bound (hW.aestronglyMeasurable.inner hmm) K ?_
  refine ae_restrict_of_forall_mem hT fun x hx => ?_
  have hKx := hK x (hTC hx)
  calc ‖⟪W x, m x⟫‖ ≤ ‖W x‖ * ‖m x‖ := norm_inner_le_norm _ _
    _ ≤ K * 1 := mul_le_mul hKx (hm x hx) (norm_nonneg _) ((norm_nonneg _).trans hKx)
    _ = K := mul_one K

/-- The flux difference of two continuous fields that are `η`-close on a compact set
containing the surface is at most `η` times the area. -/
theorem norm_setIntegral_inner_sub_le {μ : Measure E3} {T C : Set E3} {W V m : E3 → E3}
    (hW : Continuous W) (hV : Continuous V) (hC : IsCompact C) (hTC : T ⊆ C)
    (hT : MeasurableSet T) (hTfin : μ T < ⊤) (hm : ∀ x ∈ T, ‖m x‖ ≤ 1)
    (hmm : AEStronglyMeasurable m (μ.restrict T)) {η : ℝ}
    (hWV : ∀ x ∈ C, ‖W x - V x‖ ≤ η) :
    ‖(∫ x in T, ⟪W x, m x⟫ ∂μ) - ∫ x in T, ⟪V x, m x⟫ ∂μ‖ ≤ η * μ.real T := by
  rw [← integral_sub (integrableOn_inner_of_continuous hW hC hTC hT hTfin hm hmm)
    (integrableOn_inner_of_continuous hV hC hTC hT hTfin hm hmm)]
  refine norm_setIntegral_le_of_norm_le_const hTfin fun x hx => ?_
  rw [← inner_sub_left]
  calc ‖⟪W x - V x, m x⟫‖ ≤ ‖W x - V x‖ * ‖m x‖ := norm_inner_le_norm _ _
    _ ≤ η * 1 := mul_le_mul (hWV x (hTC hx)) (hm x hx) (norm_nonneg _)
        ((norm_nonneg _).trans (hWV x (hTC hx)))
    _ = η := mul_one η

/-- Transfer of flux convergence from `C¹` compactly supported fields to continuous fields,
for an arbitrary filter and measure. The surfaces `Sig s` eventually lie in a fixed compact
set `C`, are measurable with uniformly bounded measure, and carry measurable normals of norm
at most one; the limit surface `S ⊆ C` has finite measure and a measurable normal `n` of norm
at most one. -/
theorem tendsto_setIntegral_inner_of_continuous {ι : Type*} {l : Filter ι} {μ : Measure E3}
    {Sig : ι → Set E3} {S C : Set E3} {ν n : E3 → E3} (hC : IsCompact C)
    (hSigC : ∀ᶠ s in l, Sig s ⊆ C) (hSigm : ∀ᶠ s in l, MeasurableSet (Sig s))
    (hν : ∀ᶠ s in l, ∀ x ∈ Sig s, ‖ν x‖ ≤ 1)
    (hνm : ∀ᶠ s in l, AEStronglyMeasurable ν (μ.restrict (Sig s)))
    (hSC : S ⊆ C) (hSm : MeasurableSet S) (hn : ∀ x ∈ S, ‖n x‖ ≤ 1)
    (hnm : AEStronglyMeasurable n (μ.restrict S)) (hSfin : μ S < ⊤)
    (hA : ∃ A : ℝ, ∀ᶠ s in l, μ (Sig s) ≤ ENNReal.ofReal A)
    (hlim : ∀ Z : E3 → E3, ContDiff ℝ 1 Z → HasCompactSupport Z →
      Tendsto (fun s => ∫ x in Sig s, ⟪Z x, ν x⟫ ∂μ) l (𝓝 (∫ x in S, ⟪Z x, n x⟫ ∂μ)))
    {Y : E3 → E3} (hY : Continuous Y) :
    Tendsto (fun s => ∫ x in Sig s, ⟪Y x, ν x⟫ ∂μ) l (𝓝 (∫ x in S, ⟪Y x, n x⟫ ∂μ)) := by
  obtain ⟨A, hA⟩ := hA
  set B : ℝ := max A 0 + μ.real S + 1 with hB
  have hBpos : 0 < B := by
    have h1 : 0 ≤ max A 0 := le_max_right A 0
    have h2 : 0 ≤ μ.real S := measureReal_nonneg
    linarith
  rw [Metric.tendsto_nhds]
  intro ε hε
  set η : ℝ := ε / (2 * B) with hηdef
  have hη : 0 < η := by positivity
  have hηB : η * max A 0 + η * μ.real S + η = ε / 2 := by
    have : η * B = ε / 2 := by rw [hηdef]; field_simp
    rw [← this, hB]; ring
  obtain ⟨Z, hZ, hcZ, hYZ⟩ := exists_contDiff_near_continuous hY hC hη
  have hlimZ := Metric.tendsto_nhds.mp
    (hlim Z (hZ.of_le (by exact_mod_cast le_top)) hcZ) (ε / 2) (half_pos hε)
  have hS := norm_setIntegral_inner_sub_le hY hZ.continuous hC hSC hSm hSfin hn hnm hYZ
  filter_upwards [hlimZ, hSigC, hSigm, hν, hνm, hA] with s hs1 hs2 hs3 hs4 hs5 hs6
  have hfin : μ (Sig s) < ⊤ := hs6.trans_lt ENNReal.ofReal_lt_top
  have hreal : μ.real (Sig s) ≤ max A 0 := by
    calc μ.real (Sig s) = (μ (Sig s)).toReal := rfl
      _ ≤ (ENNReal.ofReal A).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hs6
      _ = max A 0 := ENNReal.toReal_ofReal'
  have hSigZ := norm_setIntegral_inner_sub_le hY hZ.continuous hC hs2 hs3 hfin hs4 hs5 hYZ
  have hηA : η * μ.real (Sig s) ≤ η * max A 0 := mul_le_mul_of_nonneg_left hreal hη.le
  rw [dist_eq_norm] at hs1 ⊢
  set F := ∫ x in Sig s, ⟪Y x, ν x⟫ ∂μ
  set G := ∫ x in Sig s, ⟪Z x, ν x⟫ ∂μ
  set L := ∫ x in S, ⟪Y x, n x⟫ ∂μ
  set M := ∫ x in S, ⟪Z x, n x⟫ ∂μ
  calc ‖F - L‖ = ‖(F - G) + (G - M) - (L - M)‖ := by congr 1; ring
    _ ≤ ‖(F - G) + (G - M)‖ + ‖L - M‖ := norm_sub_le _ _
    _ ≤ ‖F - G‖ + ‖G - M‖ + ‖L - M‖ := by gcongr; exact norm_add_le _ _
    _ < ε := by linarith

/-- `tendsto_setIntegral_inner_of_continuous` for normalized two-dimensional Hausdorff
measure and the filter `s → 1⁻`: convergence of the fluxes of all `C¹` compactly supported
fields through `Sig s` to the flux through `S` implies the same for every continuous field. -/
theorem tendsto_flux_of_continuous {Sig : ℝ → Set E3} {S C : Set E3} {ν n : E3 → E3}
    (hC : IsCompact C)
    (hSigC : ∀ᶠ s in 𝓝[<] (1 : ℝ), Sig s ⊆ C)
    (hSigm : ∀ᶠ s in 𝓝[<] (1 : ℝ), MeasurableSet (Sig s))
    (hν : ∀ᶠ s in 𝓝[<] (1 : ℝ), ∀ x ∈ Sig s, ‖ν x‖ ≤ 1)
    (hνm : ∀ᶠ s in 𝓝[<] (1 : ℝ),
      AEStronglyMeasurable ν ((hausdorffMeasure2 3).restrict (Sig s)))
    (hSC : S ⊆ C) (hSm : MeasurableSet S) (hn : ∀ x ∈ S, ‖n x‖ ≤ 1)
    (hnm : AEStronglyMeasurable n ((hausdorffMeasure2 3).restrict S))
    (hSfin : hausdorffMeasure2 3 S < ⊤)
    (hA : ∃ A : ℝ, ∀ᶠ s in 𝓝[<] (1 : ℝ), hausdorffMeasure2 3 (Sig s) ≤ ENNReal.ofReal A)
    (hlim : ∀ Z : E3 → E3, ContDiff ℝ 1 Z → HasCompactSupport Z →
      Tendsto (fun s => ∫ x in Sig s, ⟪Z x, ν x⟫ ∂(hausdorffMeasure2 3)) (𝓝[<] 1)
        (𝓝 (∫ x in S, ⟪Z x, n x⟫ ∂(hausdorffMeasure2 3))))
    {Y : E3 → E3} (hY : Continuous Y) :
    Tendsto (fun s => ∫ x in Sig s, ⟪Y x, ν x⟫ ∂(hausdorffMeasure2 3)) (𝓝[<] 1)
      (𝓝 (∫ x in S, ⟪Y x, n x⟫ ∂(hausdorffMeasure2 3))) :=
  tendsto_setIntegral_inner_of_continuous hC hSigC hSigm hν hνm hSC hSm hn hnm hSfin hA hlim hY

end LiquidDrop.CapacitaryK
