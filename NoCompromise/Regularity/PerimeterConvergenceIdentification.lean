import NoCompromise.Regularity.PerimeterConvergenceBalls
import Mathlib.Topology.Compactness.Lindelof

/-! # Identification of every positive weak limit with the actual perimeter -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology CompactlySupported
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Ordered measures agreeing finitely on an open neighborhood of every point are equal. -/
theorem measure_eq_of_le_of_local_finite_mass_eq {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    {μ ν : Measure X} (hle : μ ≤ ν)
    (hloc : ∀ x : X, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ μ V < ∞ ∧ μ V = ν V) :
    μ = ν := by
  choose V hVo hxV hfin heq using hloc
  have hcover : univ ⊆ ⋃ x, V x := fun x _ => mem_iUnion.mpr ⟨x, hxV x⟩
  obtain ⟨S, hS, hs⟩ := isLindelof_univ.elim_countable_subcover V hVo hcover
  apply Measure.ext_of_biUnion_eq_univ hS (univ_subset_iff.mp hs)
  intro x _
  let : IsFiniteMeasure (μ.restrict (V x)) := ⟨by simpa using hfin x⟩
  apply Measure.eq_of_le_of_measure_univ_eq (Measure.restrict_mono subset_rfl hle)
  simpa only [Measure.restrict_apply_univ] using heq x

/-- No positive perimeter mass is lost or gained in an admissible quasiminimal limit. -/
theorem localPerimeterMeasure_eq_of_weak_limit
    {U F : Set AmbientSpace} (hU : IsOpen U)
    {E : ℕ → Set AmbientSpace} {ω : ℕ → ℝ} {s : ℕ → ℝ≥0∞}
    (hE : ∀ j, IsOmegaMinimalAtScales (E j) (ω j) (s j))
    (hf : ∀ j, IsLocallyBVOn ((E j).indicator (fun _ => (1 : ℝ))) U)
    (hmF : NullMeasurableSet F volume)
    (hF : IsLocallyBVOn (F.indicator (fun _ => (1 : ℝ))) U)
    {ω₀ : ℝ} (hω : Tendsto ω atTop (𝓝 ω₀))
    (hscale : ∀ (x : AmbientSpace) (R : ℝ), 0 < R → closedBall x R ⊆ U →
      ∀ᶠ j in atTop, ENNReal.ofReal R ≤ s j)
    (hlim : ∀ K : Set AmbientSpace, IsCompact K → K ⊆ U →
      Tendsto (fun j => ∫ z in K,
        |(E j).indicator (fun _ => (1 : ℝ)) z - F.indicator (fun _ => (1 : ℝ)) z|)
        atTop (𝓝 0))
    (τ : Measure U) [τ.Regular]
    (hweak : ∀ φ : C_c(U, ℝ),
      Tendsto (fun j => ∫ z : U, φ z ∂localPerimeterMeasure hU (hf j))
        atTop (𝓝 (∫ z : U, φ z ∂τ))) :
    localPerimeterMeasure hU hF = τ := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let : (localPerimeterMeasure hU hF).Regular := (localPerimeterMeasure_data hU hF).1
  have hle := localPerimeterMeasure_le_of_weak_limit hU hf hF τ hweak hlim
  apply measure_eq_of_le_of_local_finite_mass_eq hle
  intro x
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x x.property
  let R := ε / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hRU : closedBall (x : AmbientSpace) R ⊆ U :=
    (closedBall_subset_ball (by dsimp [R]; linarith)).trans hεU
  have hae := (ae_local_measure_sphere_eq_zero τ (x : AmbientSpace)).and
    (ae_local_measure_sphere_eq_zero (localPerimeterMeasure hU hF) (x : AmbientSpace))
  obtain ⟨a, ha, hnull⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (show volume (Ioo (0 : ℝ) R) ≠ 0 by
      simpa only [Real.volume_Ioo, sub_zero, ne_eq, ENNReal.ofReal_eq_zero, not_le] using hR)
    (ae_restrict_of_ae hae)
  have hupper := weak_limit_local_ball_le_perimeter hU hE hf hmF hF hω hlim τ hweak
    (x : AmbientSpace) ha.1 ha.2 hRU (hscale x R hR hRU) hnull.1 hnull.2
  have hK : IsCompact ((Subtype.val : U → AmbientSpace) ⁻¹' closedBall x R) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' (isCompact_closedBall (x : AmbientSpace) R)
      (by simpa using hRU)
  refine ⟨Subtype.val ⁻¹' ball (x : AmbientSpace) a,
    isOpen_ball.preimage continuous_subtype_val, ?_, ?_, le_antisymm (hle _) hupper⟩
  · exact mem_ball_self ha.1
  · exact (measure_mono (preimage_mono
      ((ball_subset_ball ha.2.le).trans ball_subset_closedBall))).trans_lt hK.measure_lt_top

end LiquidDrop
