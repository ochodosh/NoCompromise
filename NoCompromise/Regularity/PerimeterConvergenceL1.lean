module

public import NoCompromise.Regularity.PerimeterConvergenceLocal

@[expose] public section

/-! # Indicator L¹ convergence and the actual symmetric-difference cost -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology symmDiff
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma volume_symmDiff_inter_eq_ofReal_l1 {n : ℕ}
    {E F A : Set (EuclideanSpace ℝ (Fin n))}
    (hmE : NullMeasurableSet E volume) (hmF : NullMeasurableSet F volume)
    (hiE : IntegrableOn (E.indicator (fun _ => (1 : ℝ))) A)
    (hiF : IntegrableOn (F.indicator (fun _ => (1 : ℝ))) A) :
    volume ((E ∆ F) ∩ A) = ENNReal.ofReal (∫ z in A,
      |E.indicator (fun _ => (1 : ℝ)) z - F.indicator (fun _ => (1 : ℝ)) z|) := by
  rw [← Measure.restrict_apply₀ ((hmE.symmDiff hmF).mono Measure.restrict_le_self),
    ← eLpNorm_indicator_sub_eq_symmDiff (hmE.mono Measure.restrict_le_self)
      (hmF.mono Measure.restrict_le_self),
    eLpNorm_one_eq_lintegral_enorm (hiE.sub hiF).aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm (hiE.sub hiF)]
  simp only [Pi.sub_apply, Real.norm_eq_abs]

lemma tendsto_volume_symmDiff_inter_of_l1 {n : ℕ}
    {E : ℕ → Set (EuclideanSpace ℝ (Fin n))} {F A : Set (EuclideanSpace ℝ (Fin n))}
    (hmE : ∀ j, NullMeasurableSet (E j) volume) (hmF : NullMeasurableSet F volume)
    (hiE : ∀ j, IntegrableOn ((E j).indicator (fun _ => (1 : ℝ))) A)
    (hiF : IntegrableOn (F.indicator (fun _ => (1 : ℝ))) A)
    (ht : Tendsto (fun j => ∫ z in A,
      |(E j).indicator (fun _ => (1 : ℝ)) z - F.indicator (fun _ => (1 : ℝ)) z|)
        atTop (𝓝 0)) :
    Tendsto (fun j => volume ((E j ∆ F) ∩ A)) atTop (𝓝 0) := by
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def, ENNReal.ofReal_zero,
    ← volume_symmDiff_inter_eq_ofReal_l1 (hmE _) hmF (hiE _) hiF] using h

lemma tendsto_eLpNorm_indicator_sub_one_of_l1 {n : ℕ}
    {E : ℕ → Set (EuclideanSpace ℝ (Fin n))} {F A : Set (EuclideanSpace ℝ (Fin n))}
    (hmE : ∀ j, NullMeasurableSet (E j) volume) (hmF : NullMeasurableSet F volume)
    (hiE : ∀ j, IntegrableOn ((E j).indicator (fun _ => (1 : ℝ))) A)
    (hiF : IntegrableOn (F.indicator (fun _ => (1 : ℝ))) A)
    (ht : Tendsto (fun j => ∫ z in A,
      |(E j).indicator (fun _ => (1 : ℝ)) z - F.indicator (fun _ => (1 : ℝ)) z|)
        atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm
      ((E j).indicator (fun _ => (1 : ℝ)) - F.indicator (fun _ => (1 : ℝ)))
        1 (volume.restrict A)) atTop (𝓝 0) := by
  simpa only [eLpNorm_indicator_sub_eq_symmDiff (hmE _ |>.mono Measure.restrict_le_self)
    (hmF.mono Measure.restrict_le_self), Measure.restrict_apply₀
      ((hmE _ |>.symmDiff hmF).mono Measure.restrict_le_self)] using
    tendsto_volume_symmDiff_inter_of_l1 hmE hmF hiE hiF ht

lemma volume_symmDiff_inter_triangle {n : ℕ}
    {E F G A : Set (EuclideanSpace ℝ (Fin n))}
    (hmE : NullMeasurableSet E volume) (hmF : NullMeasurableSet F volume)
    (hmG : NullMeasurableSet G volume) :
    volume ((E ∆ G) ∩ A) ≤ volume ((E ∆ F) ∩ A) + volume ((F ∆ G) ∩ A) := by
  simpa only [Measure.restrict_apply₀ ((hmE.symmDiff hmG).mono Measure.restrict_le_self),
    Measure.restrict_apply₀ ((hmE.symmDiff hmF).mono Measure.restrict_le_self),
    Measure.restrict_apply₀ ((hmF.symmDiff hmG).mono Measure.restrict_le_self)] using
    (measure_symmDiff_le (μ := volume.restrict A) E F G)

end LiquidDrop
