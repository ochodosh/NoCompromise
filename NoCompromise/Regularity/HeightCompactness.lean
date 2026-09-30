module

public import NoCompromise.Regularity.HeightCompactnessDensity
public import NoCompromise.Regularity.TangentCompactness

@[expose] public section

/-! # Actual BV compactness for uniformly bounded quasiminimality errors -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

theorem bounded_perimeterMeasure_quasiminimal_sequence
    {E : ℕ → Set AmbientSpace} {ω : ℕ → ℝ}
    (hE : ∀ j, IsOmegaMinimal (E j) (ω j)) (hω : ∀ j, ω j ≤ 1)
    {K : Set AmbientSpace} (hK : IsCompact K) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ j,
      canonicalPerimeterMeasure (E j) (hE j).locallyFinite (hE j).nullMeasurable K ≤ C := by
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun x : AmbientSpace => ball x (1 / 4 : ℝ)) (fun _ => isOpen_ball) (by
      intro x _
      exact mem_iUnion.mpr ⟨x, mem_ball_self (by norm_num)⟩)
  let B := ENNReal.ofReal ((4 * (4 * Real.pi + (4 * Real.pi / 3))) * (1 / 4 : ℝ) ^ 2)
  refine ⟨∑ _ ∈ t, B, ENNReal.sum_lt_top.mpr (fun _ _ => ENNReal.ofReal_lt_top), ?_⟩
  intro j
  let μ := canonicalPerimeterMeasure (E j) (hE j).locallyFinite (hE j).nullMeasurable
  have hE1 : IsOmegaMinimal (E j) 1 := (hE j).mono_error (hω j)
  calc
    μ K ≤ μ (⋃ x ∈ t, ball x (1 / 4 : ℝ)) := measure_mono ht
    _ ≤ ∑ x ∈ t, μ (ball x (1 / 4 : ℝ)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _ ∈ t, B := by
      apply Finset.sum_le_sum
      intro x _
      rw [canonicalPerimeterMeasure_open _ _ _ isOpen_ball]
      have hb := hE1.perimeterIn_ball_upper x (by norm_num : (0 : ℝ) < 1 / 4)
        (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)
      rw [← ENNReal.ofReal_toReal
        ((hE j).locallyFinite _ isOpen_ball isBounded_ball.isCompact_closure).ne]
      exact ENNReal.ofReal_le_ofReal (by simpa only [one_mul] using hb)

theorem bounded_perimeterIn_quasiminimal_sequence
    {E : ℕ → Set AmbientSpace} {ω : ℕ → ℝ}
    (hE : ∀ j, IsOmegaMinimal (E j) (ω j)) (hω : ∀ j, ω j ≤ 1)
    {A : Set AmbientSpace} (hA : IsOpen A) (hcA : IsCompact (closure A)) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ j, perimeterIn (E j) A ≤ C := by
  obtain ⟨C, hC, hb⟩ := bounded_perimeterMeasure_quasiminimal_sequence hE hω hcA
  refine ⟨C, hC, fun j => ?_⟩
  rw [← canonicalPerimeterMeasure_open _ (hE j).locallyFinite (hE j).nullMeasurable hA]
  exact (measure_mono subset_closure).trans (hb j)

/-- No finite total volume or perimeter is needed: the actual indicator
compactness is local on the whole ambient space. -/
theorem exists_quasiminimal_subsequence
    {E : ℕ → Set AmbientSpace} {ω : ℕ → ℝ}
    (hE : ∀ j, IsOmegaMinimal (E j) (ω j)) (hω : ∀ j, ω j ≤ 1) :
    ∃ F : Set AmbientSpace, MeasurableSet F ∧ HasLocallyFinitePerimeter F ∧
      ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ K : Set AmbientSpace, IsCompact K →
        Tendsto (fun j => ∫ x in K,
          |(E (k j)).indicator (fun _ => (1 : ℝ)) x - F.indicator (fun _ => (1 : ℝ)) x|)
          atTop (𝓝 0) := by
  apply bv_compactness_indicators_univ E (fun j => (hE j).locallyFinite)
    (fun j => (hE j).nullMeasurable)
  intro A hA hcA
  obtain ⟨C, hC, hb⟩ := bounded_perimeterIn_quasiminimal_sequence hE hω hA hcA
  refine ⟨volume.real A + C.toReal, fun j => ?_⟩
  exact add_le_add (integral_abs_indicator_one_le_volume (hE j).nullMeasurable hcA)
    (ENNReal.toReal_mono hC.ne (hb j))

end LiquidDrop
