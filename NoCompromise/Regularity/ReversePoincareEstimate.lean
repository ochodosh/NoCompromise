module

public import NoCompromise.Regularity.ReversePoincareComparison
public import NoCompromise.Regularity.ReversePoincareMoment
public import NoCompromise.Regularity.ReversePoincareRadii

@[expose] public section

/-! # Quantitative reverse Poincaré at the original geometric scale -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The actual comparison and signed flux identity give explicit universal
constants. The slab width may be any width allowed by the genuine configuration. -/
theorem IsOmegaMinimal.reverse_poincare_explicit
    {E : Set AmbientSpace} {ω r c η : ℝ} (hE : IsOmegaMinimal E ω)
    (h : IsSlabCapConfiguration E hE.locallyFinite hE.nullMeasurable r c η)
    (hr1 : r ≤ 1 / Real.sqrt 2) :
    cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 (r / 2)
      (EuclideanSpace.single 2 1) ≤
      (128 * Real.pi ^ 2 / r ^ 4) *
        (∫ x in standardCylinder r ∩ reducedBoundary E hE.locallyFinite hE.nullMeasurable,
          (x 2 - c) ^ 2 ∂hausdorffMeasure2 3) + (256 * Real.pi / 3) * ω * r := by
  have hω := hE.nonneg
  have hr := h.1.1
  have hr0 := hr.ne'
  let μ := canonicalPerimeterMeasure E hE.locallyFinite hE.nullMeasurable
  let : IsFiniteMeasureOnCompacts μ :=
    (canonicalPerimeterPolar E hE.locallyFinite hE.nullMeasurable).finiteOnCompacts
  obtain ⟨τ, hτ, hzero⟩ := exists_regular_horizontal_radius μ r
    (a := 3 * r / 4) (b := r) (by linarith)
  have hστ : r / 2 < τ := by linarith [hτ.1]
  let H := ∫ x in standardCylinder r ∩ reducedBoundary E hE.locallyFinite hE.nullMeasurable,
    (x 2 - c) ^ 2 ∂hausdorffMeasure2 3
  have hH : 0 ≤ H := integral_nonneg fun _ => sq_nonneg _
  let K := Real.pi ^ 2 / (τ - r / 2) ^ 2
  have hK : 0 ≤ K := by positivity
  let V := (32 * Real.pi / 3) * r ^ 3
  have hV : 0 ≤ V := by positivity
  have hb := hE.perimeter_core_le_disk_add_height h hr1 (half_pos hr) hστ hτ.2 hzero
  rw [lintegral_surface_height_moment_eq] at hb
  have hb' : perimeterIn E (cylindricalCore r (r / 2)) ≤
      ENNReal.ofReal (Real.pi * (r / 2) ^ 2 + K * H + ω * V) := by
    calc
      _ ≤ ENNReal.ofReal (Real.pi * (r / 2) ^ 2) +
          ENNReal.ofReal K * ENNReal.ofReal H + ENNReal.ofReal ω * ENNReal.ofReal V :=
        hb.trans (add_le_add le_rfl (mul_le_mul' le_rfl (volume_cylindricalCore_le hr)))
      _ = _ := by
        rw [← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_mul hE.nonneg,
          ← ENNReal.ofReal_add (by positivity : 0 ≤ Real.pi * (r / 2) ^ 2),
          ← ENNReal.ofReal_add (by positivity : 0 ≤ Real.pi * (r / 2) ^ 2 + K * H)]
        all_goals positivity
  have hbr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb'
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * (r / 2) ^ 2 + K * H + ω * V)]
    at hbr
  have hd : (perimeterIn E (cylindricalCore r (r / 2))).toReal -
      Real.pi * (r / 2) ^ 2 ≤ K * H + ω * V := by linarith
  have hs : cylinder 0 (r / 2) (EuclideanSpace.single 2 1) ⊆
      cylindricalCore r (r / 2) := by
    rw [← standardCylinder_eq_cylinder]
    intro x hx
    exact ⟨hx.1, hx.1.trans (by linarith), hx.2.trans (by linarith)⟩
  have hn := normalExcessIntegral_mono E hE.locallyFinite hE.nullMeasurable
    ((isBounded_standardCylinder r).subset
      (show cylindricalCore r (r / 2) ⊆ standardCylinder r from inter_subset_right))
    hs (EuclideanSpace.single 2 1)
  have hf := h.normalExcess_core_eq_perimeter_defect (half_pos hr) (by linarith)
  have hcoeff : K ≤ 16 * Real.pi ^ 2 / r ^ 2 := by
    have hg : (r / 4) ^ 2 ≤ (τ - r / 2) ^ 2 := by
      apply (sq_le_sq₀ (by positivity) (sub_pos.mpr hστ).le).mpr
      linarith [hτ.1]
    calc
      K ≤ Real.pi ^ 2 / (r / 4) ^ 2 :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hg
      _ = _ := by field_simp; ring
  calc
    _ = normalExcessIntegral E hE.locallyFinite hE.nullMeasurable
        (cylinder 0 (r / 2) (EuclideanSpace.single 2 1)) (EuclideanSpace.single 2 1) /
          (r / 2) ^ 2 := rfl
    _ ≤ normalExcessIntegral E hE.locallyFinite hE.nullMeasurable
        (cylindricalCore r (r / 2)) (EuclideanSpace.single 2 1) / (r / 2) ^ 2 :=
      div_le_div_of_nonneg_right hn (sq_nonneg _)
    _ = (8 / r ^ 2) * ((perimeterIn E (cylindricalCore r (r / 2))).toReal -
        Real.pi * (r / 2) ^ 2) := by
      rw [← hf]
      field_simp
      ring
    _ ≤ (8 / r ^ 2) * (K * H + ω * V) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ ≤ (8 / r ^ 2) * ((16 * Real.pi ^ 2 / r ^ 2) * H + ω * V) := by gcongr
    _ = _ := by dsimp [V, H]; field_simp; ring

end LiquidDrop
