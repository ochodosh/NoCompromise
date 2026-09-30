module

public import NoCompromise.BV.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

@[expose] public section

/-!
# Perimeter quasiminimality at specified scales

This definition is independent of energy, minimizers, and Coulomb estimates.
Competitors have only locally finite perimeter. Compact containment means that
the closure of the actual symmetric difference is compact and lies in the ball.
The definitions apply in every finite dimension, in particular for `n ≥ 2`.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal symmDiff
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Blueprint `def:omega-minimal`, with the scale allowed to be infinite. -/
structure IsOmegaMinimalAtScales {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n)))
    (ω : ℝ) (r₀ : ℝ≥0∞) : Prop where
  nonneg : 0 ≤ ω
  scale_pos : 0 < r₀
  nullMeasurable : NullMeasurableSet E volume
  locallyFinite : HasLocallyFinitePerimeter E
  comparison : ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r → ENNReal.ofReal r ≤ r₀ →
    ∀ F : Set (EuclideanSpace ℝ (Fin n)), NullMeasurableSet F volume →
      HasLocallyFinitePerimeter F → IsCompact (closure (F ∆ E)) →
      closure (F ∆ E) ⊆ ball x r →
      perimeterIn E (ball x r) ≤
        perimeterIn F (ball x r) + ENNReal.ofReal ω * volume (E ∆ F)

/-- Unqualified quasiminimality means unit scale. -/
def IsOmegaMinimal {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n))) (ω : ℝ) : Prop :=
  IsOmegaMinimalAtScales E ω 1

/-- Local perimeter minimization requires zero-error comparison at every finite scale. -/
def IsLocallyPerimeterMinimizing {n : ℕ} (E : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ R : ℝ, 0 < R → IsOmegaMinimalAtScales E 0 (ENNReal.ofReal R)

lemma IsOmegaMinimalAtScales.mono_scale {n : ℕ} {E : Set (EuclideanSpace ℝ (Fin n))}
    {ω : ℝ} {r₀ r₁ : ℝ≥0∞} (hE : IsOmegaMinimalAtScales E ω r₀)
    (hpos : 0 < r₁) (hle : r₁ ≤ r₀) : IsOmegaMinimalAtScales E ω r₁ := by
  refine ⟨hE.nonneg, hpos, hE.nullMeasurable, hE.locallyFinite, ?_⟩
  intro x r hr hrr F hmF hpF hc hsub
  exact hE.comparison x r hr (hrr.trans hle) F hmF hpF hc hsub

/-- Infinite-scale zero quasiminimality is exactly local perimeter minimization. -/
theorem isLocallyPerimeterMinimizing_iff {n : ℕ} {E : Set (EuclideanSpace ℝ (Fin n))} :
    IsLocallyPerimeterMinimizing E ↔ IsOmegaMinimalAtScales E 0 ∞ := by
  constructor
  · intro h
    have h1 := h 1 (by norm_num)
    refine ⟨h1.nonneg, by simp, h1.nullMeasurable, h1.locallyFinite, ?_⟩
    intro x r hr _ F hmF hpF hc hs
    exact (h r hr).comparison x r hr le_rfl F hmF hpF hc hs
  · intro h R hR
    exact h.mono_scale (ENNReal.ofReal_pos.mpr hR) le_top

/-- The three-dimensional volume-error bound recorded in the definition. -/
theorem IsOmegaMinimalAtScales.perimeterIn_ball_le_cubic
    {E : Set AmbientSpace} {ω : ℝ} {r₀ : ℝ≥0∞}
    (hE : IsOmegaMinimalAtScales E ω r₀) (x : AmbientSpace) {r : ℝ}
    (hr : 0 < r) (hrr : ENNReal.ofReal r ≤ r₀)
    {F : Set AmbientSpace} (hmF : NullMeasurableSet F volume)
    (hpF : HasLocallyFinitePerimeter F) (hc : IsCompact (closure (F ∆ E)))
    (hs : closure (F ∆ E) ⊆ ball x r) :
    perimeterIn E (ball x r) ≤ perimeterIn F (ball x r) +
      ENNReal.ofReal (ω * ((4 * Real.pi / 3) * r ^ 3)) := by
  apply (hE.comparison x r hr hrr F hmF hpF hc hs).trans
  apply add_le_add le_rfl
  have hsub : E ∆ F ⊆ ball x r := by
    rw [symmDiff_comm]
    exact subset_closure.trans hs
  calc
    ENNReal.ofReal ω * volume (E ∆ F) ≤ ENNReal.ofReal ω * volume (ball x r) :=
      mul_le_mul' le_rfl (measure_mono hsub)
    _ = _ := by
      rw [EuclideanSpace.volume_ball_fin_three]
      rw [← ENNReal.ofReal_pow hr.le,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ r ^ 3),
        ← ENNReal.ofReal_mul hE.nonneg]
      congr 1
      ring

end LiquidDrop
