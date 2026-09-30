module

public import NoCompromise.BV.CompactC1Tests
public import NoCompromise.BV.WeightedRadialFlux

@[expose] public section

/-!
# A common exceptional set for weighted radial flux tests

Compact C¹ test jets allow the individual radial identities to hold
simultaneously for every compactly supported C¹ scalar test function.
-/

noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma integral_comap_subtype_eq_of_zero_off {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (q : EuclideanSpace ℝ (Fin n) → ℝ) (hq : ∀ x ∉ K, q x = 0) :
    (∫ x : K, q x ∂μ.comap Subtype.val) = ∫ x, q x ∂μ :=
  (integral_subtype_comap hK q).trans (setIntegral_eq_integral_of_forall_compl_eq_zero hq)

/-- On a fixed compact support the weighted radial identity holds for all C¹
tests outside one null set of radii. -/
theorem IsAmbientOutwardPerimeterPolar.ae_all_weighted_radial_tests_on_compact
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {ν : AmbientSpace → AmbientSpace}
    (h : IsAmbientOutwardPerimeterPolar E μ ν) (hE : NullMeasurableSet E volume)
    (c : AmbientSpace) {K : Set AmbientSpace} (hK : IsCompact K) (i : Fin 3) :
    ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), ∀ φ : CompactC1Test K,
      (∫ x in ball c r, φ.val x * (-ν x i) ∂μ) +
        (∫ x in ball c r, (densityOne E).indicator
          (fun y => fderiv ℝ φ.val y (EuclideanSpace.single i 1)) x) =
          weightedSphericalSectionFlux E c φ.val i r := by
  classical
  let := h.finiteOnCompacts
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F (r : ℝ) (v : C(K, ℝ) × (Fin 3 → C(K, ℝ))) : ℝ := if 0 < r then
    (∫ x : K, (-ν x i) * v.1 x ∂(μ.restrict (ball c r)).comap Subtype.val) +
    (∫ x : K, (densityOne E).indicator (fun _ => (1 : ℝ)) x * v.2 i x
      ∂(volume.restrict (ball c r)).comap Subtype.val) -
    (∫ x : K, ((densityOne E).indicator (fun y => (y - c) i / r) x) * v.1 x
      ∂((hausdorffMeasure2 3).restrict (sphere c r)).comap Subtype.val) else 0
  have hF (r : ℝ) : Continuous (F r) := by
    by_cases hr : 0 < r
    · have hi₀ : Integrable (fun x : K => -ν x i)
          ((μ.restrict (ball c r)).comap Subtype.val) := by
        apply (integrableOn_iff_comap_subtypeVal (f := fun x => -ν x i)
          (μ := μ.restrict (ball c r)) hK.measurableSet).mp
        have hi := ((h.locallyIntegrable.neg.mono_measure
          (Measure.restrict_le_self (s := ball c r))).integrableOn_isCompact hK)
        simpa only [Function.comp_def, PiLp.neg_apply] using!
          (EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp hi
      have hi₁ : Integrable (fun x : K => (densityOne E).indicator (fun _ => (1 : ℝ)) x)
          ((volume.restrict (ball c r)).comap Subtype.val) := by
        apply (integrableOn_iff_comap_subtypeVal
          (f := (densityOne E).indicator (fun _ => (1 : ℝ)))
          (μ := volume.restrict (ball c r)) hK.measurableSet).mp
        exact ((continuous_const : Continuous (fun _ : AmbientSpace => (1 : ℝ))).continuousOn
          ).integrableOn_compact hK |>.indicator (measurableSet_densityOne hE)
      let : IsFiniteMeasure ((hausdorffMeasure2 3).restrict (sphere c r)) := ⟨by
        rw [Measure.restrict_apply_univ, hausdorffMeasure2_sphere c hr]
        exact ENNReal.ofReal_lt_top⟩
      have hi₂ : Integrable (fun x : K =>
          (densityOne E).indicator (fun y => (y - c) i / r) x)
          (((hausdorffMeasure2 3).restrict (sphere c r)).comap Subtype.val) := by
        apply (integrableOn_iff_comap_subtypeVal
          (f := (densityOne E).indicator (fun y => (y - c) i / r))
          (μ := (hausdorffMeasure2 3).restrict (sphere c r)) hK.measurableSet).mp
        exact ((show Continuous (fun y : AmbientSpace => (y - c) i / r) by fun_prop
          ).continuousOn.integrableOn_compact hK).indicator (measurableSet_densityOne hE)
      simpa only [F, ite_eq_left hr, Function.comp_def, Pi.add_apply, Pi.sub_apply] using!
        (((continuous_integral_mul_continuousMap hi₀).comp continuous_fst).add
          ((continuous_integral_mul_continuousMap hi₁).comp
            ((continuous_apply i).comp continuous_snd))).sub
          ((continuous_integral_mul_continuousMap hi₂).comp continuous_fst)
    · simpa only [F, ite_eq_right hr] using (continuous_const : Continuous (fun _ => (0 : ℝ)))
  have heval (r : ℝ) (hr : 0 < r) (φ : CompactC1Test K) :
      F r (compactC1TestJet K φ) =
        (∫ x in ball c r, φ.val x * (-ν x i) ∂μ) +
        (∫ x in ball c r, (densityOne E).indicator
          (fun y => fderiv ℝ φ.val y (EuclideanSpace.single i 1)) x) -
          weightedSphericalSectionFlux E c φ.val i r := by
    have hz (x : AmbientSpace) (hx : x ∉ K) : x ∉ tsupport φ.val :=
      fun hh => hx (φ.property.2 hh)
    have h₀ := integral_comap_subtype_eq_of_zero_off hK.measurableSet
      (μ.restrict (ball c r)) (fun x => (-ν x i) * φ.val x)
      (fun x hx => by rw [image_eq_zero_of_notMem_tsupport (hz x hx), mul_zero])
    have h₁ := integral_comap_subtype_eq_of_zero_off hK.measurableSet
      (volume.restrict (ball c r))
      (fun x => (densityOne E).indicator (fun _ => (1 : ℝ)) x *
        fderiv ℝ φ.val x (EuclideanSpace.single i 1))
      (fun x hx => by rw [fderiv_of_notMem_tsupport ℝ (hz x hx)]; simp)
    have h₂ := integral_comap_subtype_eq_of_zero_off hK.measurableSet
      ((hausdorffMeasure2 3).restrict (sphere c r))
      (fun x => (densityOne E).indicator (fun y => (y - c) i / r) x * φ.val x)
      (fun x hx => by rw [image_eq_zero_of_notMem_tsupport (hz x hx), mul_zero])
    simp only [F, ite_eq_left hr, compactC1TestJet, ContinuousMap.coe_mk]
    rw [h₀, h₁, h₂]
    congr 2
    · apply integral_congr_ae
      exact ae_of_all _ fun x => mul_comm _ _
    · apply integral_congr_ae
      exact ae_of_all _ fun x => by by_cases hx : x ∈ densityOne E <;> simp [hx]
    · funext x
      by_cases hx : x ∈ densityOne E <;> simp [hx, mul_comm]
  have ha : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), ∀ φ : CompactC1Test K,
      F r (compactC1TestJet K φ) = 0 := by
    apply ae_all_compactC1_tests_of_continuous hK F hF
    intro φ
    filter_upwards [h.ae_weighted_integral_ball_eq_sphericalSectionFlux hE c φ.val
      φ.property.1 i, ae_restrict_mem measurableSet_Ioi] with r hr hrp
    rw [heval r hrp φ, hr, sub_self]
  filter_upwards [ha, ae_restrict_mem measurableSet_Ioi] with r hr hrp
  intro φ
  exact sub_eq_zero.mp (heval r hrp φ ▸ hr φ)

/-- One null set of radii works simultaneously for every compactly supported C¹
test and all three derivative coordinates. -/
theorem IsAmbientOutwardPerimeterPolar.ae_all_weighted_radial_tests
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {ν : AmbientSpace → AmbientSpace}
    (h : IsAmbientOutwardPerimeterPolar E μ ν) (hE : NullMeasurableSet E volume)
    (c : AmbientSpace) :
    ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)),
      ∀ (φ : CompactlySupportedContinuousMap AmbientSpace ℝ), ContDiff ℝ 1 φ →
        ∀ i : Fin 3,
          (∫ x in ball c r, φ x * (-ν x i) ∂μ) +
            (∫ x in ball c r, (densityOne E).indicator
              (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x) =
              weightedSphericalSectionFlux E c φ i r := by
  have hall : ∀ k : ℕ, ∀ i : Fin 3, ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)),
      ∀ φ : CompactC1Test (closedBall (0 : AmbientSpace) (k : ℝ)),
        (∫ x in ball c r, φ.val x * (-ν x i) ∂μ) +
          (∫ x in ball c r, (densityOne E).indicator
            (fun y => fderiv ℝ φ.val y (EuclideanSpace.single i 1)) x) =
            weightedSphericalSectionFlux E c φ.val i r :=
    fun k i => h.ae_all_weighted_radial_tests_on_compact hE c (isCompact_closedBall 0 k) i
  have ha := ae_all_iff.mpr (fun k => ae_all_iff.mpr (hall k))
  filter_upwards [ha] with r hr
  intro φ hφ i
  obtain ⟨R, hR⟩ := φ.hasCompactSupport.isBounded.subset_closedBall (0 : AmbientSpace)
  obtain ⟨k, hk⟩ := exists_nat_gt R
  have hs : tsupport φ ⊆ closedBall (0 : AmbientSpace) (k : ℝ) :=
    hR.trans (closedBall_subset_closedBall hk.le)
  exact hr k i ⟨φ, hφ, hs⟩

end LiquidDrop
