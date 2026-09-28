import NoCompromise.Regularity.ZeroExcessMollification

/-! # Localizing the genuine polar identity for constant normals -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal CompactlySupported
namespace LiquidDrop

/-- The subtype polar decomposition on U supplies precisely the local test
identity; no perimeter outside U is assumed. -/
lemma IsDistributionalPolarRepresentation.hasLocalConstantIndicatorPolar
    {E U : Set AmbientSpace} {ρ : Measure U} {σ : U → AmbientSpace} {ν : AmbientSpace}
    (h : IsDistributionalPolarRepresentation (E.indicator (fun _ => (1 : ℝ))) U ρ σ)
    (hσ : σ =ᵐ[ρ] fun _ => -ν) :
    HasLocalConstantIndicatorPolar E U (Measure.map Subtype.val ρ) ν := by
  intro i φ hφ hsφ
  have ht := h.test_eq i φ hφ hsφ
  have hzero : (∫ x in U, E.indicator (fun _ => (1 : ℝ)) x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      ∫ x, E.indicator (fun _ => (1 : ℝ)) x *
        fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [fderiv_of_notMem_tsupport ℝ (fun hh => hx (hsφ hh)), zero_apply, mul_zero]
  rw [hzero] at ht
  have hm : AEStronglyMeasurable (fun x : AmbientSpace => φ x * (-ν i))
      (Measure.map (Subtype.val : U → AmbientSpace) ρ) :=
    (φ.continuous.mul_const (-ν i)).aestronglyMeasurable
  rw [integral_map measurable_subtype_coe.aemeasurable hm]
  apply ht.trans
  apply integral_congr_ae
  filter_upwards [hσ] with x hx
  simp only [hx, PiLp.neg_apply]

/-- Constancy of the genuine ambient outward normal only inside U supplies the
same local distributional identity. -/
lemma IsAmbientOutwardPerimeterPolar.hasLocalConstantIndicatorPolar
    {E U : Set AmbientSpace} {μ : Measure AmbientSpace}
    {σ : AmbientSpace → AmbientSpace} {ν : AmbientSpace}
    (h : IsAmbientOutwardPerimeterPolar E μ σ) (hU : MeasurableSet U)
    (hσ : σ =ᵐ[μ.restrict U] fun _ => ν) :
    HasLocalConstantIndicatorPolar E U μ ν := by
  intro i φ hφ hsφ
  apply (h.coordinate_eq i φ hφ).trans
  apply integral_congr_ae
  have he := (ae_restrict_iff' hU).mp hσ
  filter_upwards [he] with x hx
  by_cases hxU : x ∈ U
  · rw [hx hxU]
  · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hxU (hsφ hh))
    simp only [hz, zero_mul]

end LiquidDrop
