module

public import NoCompromise.Regularity.DeformationStrip
public import NoCompromise.BV.Algebra

@[expose] public section

/-!
# Quantitative bounds for cuts at fixed planes

The surface cost is bounded using the actual one-sided BV trace. The estimate
holds at every cutting height, including heights carrying original perimeter
mass, and imposes no global finite-volume or finite-perimeter condition.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The actual trace inherits a genuine bound on the original function. -/
lemma IsLocallyBVOn.norm_flatBVLeftTrace_le {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ)
    {B : ℝ} (hb : ∀ z, ‖f z‖ ≤ B) (a : ℝ) :
    ∀ᵐ x : EuclideanSpace ℝ (Fin n), ‖flatBVLeftTrace f a x‖ ≤ B := by
  filter_upwards [hf.ae_line_oneSided_traces] with x hx
  have hm := (hx a).1.mem_closed (S := Icc (-B) B) isClosed_Icc
    (ae_of_all _ fun t => abs_le.mp (by simpa only [Real.norm_eq_abs] using hb (graphAppendN x t)))
  exact abs_le.mpr hm

lemma IsLocallyBVOn.norm_flatCutSurfaceDensity_le {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ)
    {B : ℝ} (hb : ∀ z, ‖f z‖ ≤ B) (a : ℝ) :
    ∀ᵐ z ∂flatHyperplaneMeasure n a, ‖flatCutSurfaceDensity f a z‖ ≤ B := by
  rw [flatHyperplaneMeasure,
    (isClosedEmbedding_graphAppendN n a).measurableEmbedding.ae_map_iff]
  filter_upwards [hf.norm_flatBVLeftTrace_le hb a] with x hx
  simpa [flatCutSurfaceDensity, norm_smul] using hx

/-- An actual bounded BV function gains at most its bound times the flat area
when it is cut below any fixed coordinate plane. -/
theorem IsLocallyBVOn.variation_indicator_lowerHalfspace_le {n : ℕ}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ)
    {B : ℝ} (hb : ∀ z, ‖f z‖ ≤ B) (a : ℝ)
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hU : IsOpen U) :
    variation ({z | z (Fin.last n) < a}.indicator f) U ≤
      variation f U + ENNReal.ofReal B * flatHyperplaneMeasure n a U := by
  classical
  obtain ⟨μ, σ, _, _, _, hn, hσ, hp, hv⟩ := hf.exists_ambient_scalar_polar
  let H : Set (EuclideanSpace ℝ (Fin (n + 1))) := {z | z (Fin.last n) < a}
  have hH : MeasurableSet H :=
    measurableSet_lt (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last n)).measurable measurable_const
  let μs : Bool → Measure (EuclideanSpace ℝ (Fin (n + 1))) :=
    fun b => if b then flatHyperplaneMeasure n a else μ.restrict H
  let σs : Bool → EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun b => if b then flatCutSurfaceDensity f a else σ
  have hσs : ∀ b, LocallyIntegrable (σs b) (μs b) := by
    intro b
    cases b
    · exact hσ.mono_measure Measure.restrict_le_self
    · exact hf.locallyIntegrable_flatCutSurfaceDensity a
  have hp' : ∀ (i : Fin (n + 1))
      (φ : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin (n + 1))) ℝ),
      ContDiff ℝ 1 φ → -(∫ z, (H.indicator f) z *
        fderiv ℝ φ z (EuclideanSpace.single i 1)) =
        ∑ b, ∫ z, φ z * σs b z i ∂μs b := by
    intro i φ hφ
    simpa only [μs, σs, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, add_comm] using
      hf.flat_cut_coordinate_measure_pairing hσ hp a i φ hφ
  have hv' := variation_le_sum_lintegral_of_divergence_pairing
    (fun X hX hcX => integral_divergence_eq_sum_of_coordinate_pairings
      ((locallyIntegrableOn_univ.mp hf.1).indicator hH) hσs hp' hX hcX) U
  have hbulk : (∫⁻ z in U, ‖σ z‖ₑ ∂μ.restrict H) ≤ μ U := by
    calc
      _ = ∫⁻ _z in U, (1 : ℝ≥0∞) ∂μ.restrict H := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_of_ae (ae_restrict_of_ae hn)] with z hz
        rw [← ofReal_norm, hz, ENNReal.ofReal_one]
      _ = μ.restrict H U := by simp
      _ ≤ μ U := Measure.restrict_le_self U
  have hsurf : (∫⁻ z in U, ‖flatCutSurfaceDensity f a z‖ₑ ∂flatHyperplaneMeasure n a) ≤
      ENNReal.ofReal B * flatHyperplaneMeasure n a U := by
    calc
      _ ≤ ∫⁻ _z in U, ENNReal.ofReal B ∂flatHyperplaneMeasure n a := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_of_ae (hf.norm_flatCutSurfaceDensity_le hb a)] with z hz
        simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hz
      _ = _ := by simp
  simp only [μs, σs, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte] at hv'
  rw [hv U hU]
  exact hv'.trans ((add_le_add hsurf hbulk).trans_eq (add_comm _ _))

/-- A lower-halfspace cut of an indicator has cost at most one copy of the
interface area, without assuming a trace or a good cutting height. -/
theorem perimeterIn_inter_lowerHalfspace_le {n : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) (a : ℝ)
    {U : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hU : IsOpen U) :
    perimeterIn (E ∩ {z | z (Fin.last n) < a}) U ≤
      perimeterIn E U + flatHyperplaneMeasure n a U := by
  have hf := hE.isLocallyBVOn_indicator hmE univ
  have hb : ∀ z, ‖E.indicator (fun _ => (1 : ℝ)) z‖ ≤ 1 := by
    intro z
    by_cases hz : z ∈ E <;> simp [hz]
  have h := hf.variation_indicator_lowerHalfspace_le hb a hU
  have he : ({z | z (Fin.last n) < a}.indicator (E.indicator (fun _ => (1 : ℝ)))) =
      (E ∩ {z | z (Fin.last n) < a}).indicator (fun _ => (1 : ℝ)) := by
    ext z
    by_cases hz : z ∈ E <;> by_cases ha : z (Fin.last n) < a <;> simp [hz, ha]
  simpa only [he, ENNReal.ofReal_one, one_mul, perimeterIn] using h

lemma variation_sub_le_local {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    (hf : LocallyIntegrableOn f U) (hg : LocallyIntegrableOn g U) :
    variation (fun z => f z - g z) U ≤ variation f U + variation g U := by
  have h := variation_add_le hf hg.neg
  change variation (fun z => f z + -g z) U ≤
    variation f U + variation (fun z => -g z) U at h
  rw [variation_neg] at h
  simpa only [sub_eq_add_neg] using h

end LiquidDrop
