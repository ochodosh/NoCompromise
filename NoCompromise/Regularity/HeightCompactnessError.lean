module

public import NoCompromise.Regularity.HeightCompactness
public import NoCompromise.Regularity.Excess
public import NoCompromise.Sobolev.PlanarGN
public import NoCompromise.DeGiorgi.BlowupPolar

@[expose] public section

/-! # Small quadratic normal excess controls the actual linear polar error -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

lemma integral_norm_normal_error_le
    {E : Set AmbientSpace} (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) {U : Set AmbientSpace}
    (hbU : Bornology.IsBounded U) (ν : AmbientSpace) :
    (∫ x in U, ‖reducedNormal E hE hmE x - ν‖
      ∂canonicalPerimeterMeasure E hE hmE) ≤
        Real.sqrt ((canonicalPerimeterMeasure E hE hmE U).toReal) *
          Real.sqrt (normalExcessIntegral E hE hmE U ν) := by
  let μ := canonicalPerimeterMeasure E hE hmE
  let σ := reducedNormal E hE hmE
  have hp := reducedBoundary_outwardPerimeterPolar E hE hmE
  have harea := canonicalPerimeterMeasure_eq_reducedBoundary_area E hE hmE
  let : IsFiniteMeasureOnCompacts μ := (canonicalPerimeterPolar E hE hmE).finiteOnCompacts
  let : IsFiniteMeasure (μ.restrict U) := isFiniteMeasure_restrict.mpr hbU.measure_lt_top.ne
  have hunit : ∀ᵐ x ∂μ.restrict U, ‖σ x‖ = 1 := by
    simpa only [μ, σ, harea] using ae_restrict_of_ae (s := U) hp.norm_ae
  have hG : MemLp (fun x => σ x - ν) 2 (μ.restrict U) := by
    apply MemLp.of_bound
      ((measurable_reducedNormal E hE hmE).sub measurable_const).aestronglyMeasurable
      (1 + ‖ν‖)
    filter_upwards [hunit] with x hx
    exact (norm_sub_le _ _).trans (by rw [hx])
  have h1 : MemLp (fun _ : AmbientSpace => (1 : ℝ)) 2 (μ.restrict U) := memLp_const 1
  have hcs := integral_norm_smul_le_lpNorm_two_mul h1 hG
  rw [lpNorm_two_eq_sqrt_integral_norm_sq h1, lpNorm_two_eq_sqrt_integral_norm_sq hG] at hcs
  simpa only [one_smul, norm_one, one_pow, integral_const, smul_eq_mul, mul_one,
    Measure.real, Measure.restrict_apply_univ, μ, σ, harea, normalExcessIntegral] using hcs

theorem tendsto_integral_normal_error_of_excess
    {E : ℕ → Set AmbientSpace} {ω : ℕ → ℝ}
    (hE : ∀ j, IsOmegaMinimal (E j) (ω j)) (hω : ∀ j, ω j ≤ 1)
    {U : Set AmbientSpace} (hbU : Bornology.IsBounded U) (ν : AmbientSpace)
    (he : Tendsto (fun j => normalExcessIntegral (E j) (hE j).locallyFinite
      (hE j).nullMeasurable U ν) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x in U, ‖reducedNormal (E j) (hE j).locallyFinite
      (hE j).nullMeasurable x - ν‖
        ∂canonicalPerimeterMeasure (E j) (hE j).locallyFinite (hE j).nullMeasurable)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := bounded_perimeterMeasure_quasiminimal_sequence hE hω
    hbU.isCompact_closure
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    (g := fun j => Real.sqrt C.toReal * Real.sqrt
      (normalExcessIntegral (E j) (hE j).locallyFinite (hE j).nullMeasurable U ν))
  · intro j
    apply (integral_norm_normal_error_le (hE j).locallyFinite (hE j).nullMeasurable hbU ν).trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact Real.sqrt_le_sqrt (ENNReal.toReal_mono hC.ne
      ((measure_mono subset_closure).trans (hb j)))
  · simpa only [Real.sqrt_zero, mul_zero] using he.sqrt.const_mul (Real.sqrt C.toReal)

end LiquidDrop
