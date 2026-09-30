module

public import NoCompromise.DeGiorgi.ReducedPerimeter
public import NoCompromise.Sobolev.RelativeScaling
public import NoCompromise.BV.RadialVolume
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

@[expose] public section

/-!
# Conditional density inequalities from spherical flux

Relative isoperimetry and the defining normal-flux comparison imply the lower
radial differential inequalities used in density estimates. Complementation
negates the ambient polar field and uses the same perimeter measure; no
reduced-boundary complement theorem or perimeter cut identity is needed.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Complementation preserves the perimeter measure and reverses its outward field. -/
theorem IsAmbientOutwardPerimeterPolar.compl {E : Set AmbientSpace}
    {μ : Measure AmbientSpace} {ν : AmbientSpace → AmbientSpace}
    (h : IsAmbientOutwardPerimeterPolar E μ ν) (hE : NullMeasurableSet E volume) :
    IsAmbientOutwardPerimeterPolar Eᶜ μ (-ν) := by
  refine ⟨h.regular, h.finiteOnCompacts, h.measurable.neg, ?_, ?_, ?_, ?_⟩
  · simpa only [Pi.neg_apply, norm_neg] using h.norm_ae
  · intro O hO
    rw [perimeterIn_compl hE hO]
    exact h.open_eq O hO
  · intro i φ hφ
    have hcont := hφ.continuous_fderiv one_ne_zero
    have hi : Integrable (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
      (hcont.clm_apply continuous_const).integrable_of_hasCompactSupport
        (φ.hasCompactSupport.fderiv_apply ℝ _)
    have hz : (∫ x, fderiv ℝ φ x (EuclideanSpace.single i 1)) = 0 := by
      have hz := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
        (μ := volume) (f := fun _ : AmbientSpace => (1 : ℝ)) (g := (φ : AmbientSpace → ℝ))
        (v := EuclideanSpace.single i 1) (by simp) (by simpa using hi)
        (by simpa using hφ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport)
        (fun _ _ => differentiableAt_const _) (fun x _ => hφ.differentiable one_ne_zero x)
      simpa using hz
    have heq : (fun x => Eᶜ.indicator (fun _ => (1 : ℝ)) x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1) -
          E.indicator (fun _ => (1 : ℝ)) x *
            fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
      funext x
      by_cases hx : x ∈ E <;> simp [hx]
    have hEi : Integrable (fun x => E.indicator (fun _ => (1 : ℝ)) x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
      have he : (fun x => E.indicator (fun _ => (1 : ℝ)) x *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) =
          E.indicator (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
        funext x
        by_cases hx : x ∈ E <;> simp [hx]
      rw [he]
      exact hi.indicator₀ hE
    rw [heq, integral_sub hi hEi,
      hz, zero_sub, neg_neg]
    simpa only [Pi.neg_apply, PiLp.neg_apply, neg_neg, mul_neg, integral_neg] using
      congrArg Neg.neg (h.coordinate_eq i φ hφ)
  · intro X hX hcX
    rw [setIntegral_compl₀ hE (integrable_divergenceN hX hcX),
      integral_divergenceN_eq_zero hX hcX, zero_sub, h.divergence_eq X hX hcX]
    simp only [Pi.neg_apply, inner_neg_right, integral_neg]

/-- The original ball derivative is also bounded by the complementary section area. -/
theorem ae_abs_perimeterDerivativeBall_apply_le_compl_sectionArea
    (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
    (hmE : NullMeasurableSet E volume) (x : AmbientSpace) :
    ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), ∀ i : Fin 3,
      |perimeterDerivativeBall E hE hmE x r i| ≤
        (hausdorffMeasure2 3 (densityOne Eᶜ ∩ sphere x r)).toReal := by
  have hc := (canonicalPerimeterPolar E hE hmE).compl hmE
  have heq : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), ∀ i : Fin 3,
      -perimeterDerivativeBall E hE hmE x r i = sphericalSectionFlux Eᶜ x i r := by
    rw [ae_all_iff]
    intro i
    filter_upwards [hc.ae_integral_ball_eq_sphericalSectionFlux hmE.compl x i] with r hr
    simpa only [perimeterDerivativeBall_apply, Pi.neg_apply, PiLp.neg_apply,
      neg_neg, integral_neg] using hr
  filter_upwards [heq, ae_restrict_mem measurableSet_Ioi] with r hr hrpos
  intro i
  calc
    |perimeterDerivativeBall E hE hmE x r i| = ‖sphericalSectionFlux Eᶜ x i r‖ := by
      rw [← hr i, norm_neg, Real.norm_eq_abs]
    _ ≤ _ := norm_sphericalSectionFlux_le_sectionArea hmE.compl x i hrpos

/-- Both the set and its complement control the same perimeter mass at small radii. -/
theorem reduced_perimeter_le_six_sectionArea (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x : AmbientSpace} (hx : x ∈ reducedBoundary E hE hmE) :
    ∃ δ > 0, ∀ᵐ r : ℝ, 0 < r → r ≤ δ →
      (canonicalPerimeterMeasure E hE hmE).real (ball x r) ≤
        6 * (hausdorffMeasure2 3 (densityOne E ∩ sphere x r)).toReal ∧
      (canonicalPerimeterMeasure E hE hmE).real (ball x r) ≤
        6 * (hausdorffMeasure2 3 (densityOne Eᶜ ∩ sphere x r)).toReal := by
  obtain ⟨δ, hδ, hcomp⟩ := normal_flux_comparison E hE hmE hx
  refine ⟨δ, hδ, ?_⟩
  have hcoords := (ae_restrict_iff' measurableSet_Ioi).mp
    (ae_abs_perimeterDerivativeBall_apply_le_sectionArea E hE hmE x)
  have hc_coords := (ae_restrict_iff' measurableSet_Ioi).mp
    (ae_abs_perimeterDerivativeBall_apply_le_compl_sectionArea E hE hmE x)
  filter_upwards [hcoords, hc_coords] with r hrE hrEc
  intro hr hrd
  have hb (B : ℝ) (hB : ∀ i : Fin 3, |perimeterDerivativeBall E hE hmE x r i| ≤ B) :
      (canonicalPerimeterMeasure E hE hmE).real (ball x r) ≤ 6 * B := by
    have ha := abs_inner_le_three_mul_of_coordinate_bound
      (norm_reducedNormal E hE hmE hx) hB
    have hflux := hcomp r hr hrd
    have hn := neg_le_abs (inner ℝ (reducedNormal E hE hmE x)
      (perimeterDerivativeBall E hE hmE x r))
    linarith
  exact ⟨hb _ (hrE hr), hb _ (hrEc hr)⟩

/-- Ball volumes split into the set and its complement, with the exact cubic coefficient. -/
lemma volume_sides_ball_real {E : Set AmbientSpace} (hE : NullMeasurableSet E volume)
    (x : AmbientSpace) {r : ℝ} (hr : 0 ≤ r) :
    (volume (E ∩ ball x r)).toReal + (volume (ball x r \ E)).toReal =
      (4 * Real.pi / 3) * r ^ 3 := by
  have hf : volume (ball x r) ≠ ∞ :=
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall x r).measure_lt_top).ne
  have h := measureReal_inter_add_sdiff₀ (s := ball x r) hE hf
  simp only [measureReal_def] at h
  rw [EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)] at h
  simpa only [measureReal_def, inter_comm] using h.trans (by ring)

/-- The universal relative-isoperimetric inequality in real-valued ball notation. -/
theorem relative_isoperimetric_ball_three_real :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
      (hmE : NullMeasurableSet E volume) (x : AmbientSpace) (r : ℝ), 0 < r →
      (min (volume (E ∩ ball x r)).toReal (volume (ball x r \ E)).toReal) ^ (2 / 3 : ℝ) ≤
        C * (canonicalPerimeterMeasure E hE hmE).real (ball x r) := by
  obtain ⟨C, hC, hI⟩ := relative_isoperimetric_ball_three
  refine ⟨C, hC, fun E hE hmE x r hr => ?_⟩
  have hf : volume (ball x r) ≠ ∞ :=
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall x r).measure_lt_top).ne
  have hleft := measure_ne_top_of_subset (inter_subset_right : E ∩ ball x r ⊆ ball x r) hf
  have hright := measure_ne_top_of_subset (sdiff_subset : ball x r \ E ⊆ ball x r) hf
  have hp : perimeterIn E (ball x r) ≠ ∞ :=
    (hE _ isOpen_ball isBounded_ball.isCompact_closure).ne
  have hi := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hp)
    (hI x r hr E hmE)
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_min hleft hright, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hC.le] at hi
  simpa only [measureReal_def, canonicalPerimeterMeasure_open E hE hmE isOpen_ball] using hi

/-- Both radial volumes add to the volume of the ball. -/
lemma radialVolume_add_compl {E : Set AmbientSpace} (hE : NullMeasurableSet E volume)
    (x : AmbientSpace) {r : ℝ} (hr : 0 ≤ r) :
    radialVolume E x r + radialVolume Eᶜ x r = (4 * Real.pi / 3) * r ^ 3 := by
  have heq : Eᶜ ∩ ball x r = ball x r \ E := by ext; simp [and_comm]
  simpa only [radialVolume, heq] using volume_sides_ball_real hE x hr

/-- A single universal coefficient controls both spherical-section areas whenever the
corresponding ball volume is at most half of the full ball volume. -/
theorem density_section_inequalities :
    ∃ c : ℝ, 0 < c ∧ ∀ (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
      (hmE : NullMeasurableSet E volume) (x : AmbientSpace), x ∈ reducedBoundary E hE hmE →
      ∃ δ > 0, ∀ᵐ r : ℝ, 0 < r → r ≤ δ →
        (radialVolume E x r ≤ (2 * Real.pi / 3) * r ^ 3 →
          c * radialVolume E x r ^ (2 / 3 : ℝ) ≤ radialSectionArea E x r) ∧
        (radialVolume Eᶜ x r ≤ (2 * Real.pi / 3) * r ^ 3 →
          c * radialVolume Eᶜ x r ^ (2 / 3 : ℝ) ≤ radialSectionArea Eᶜ x r) := by
  obtain ⟨C, hC, hI⟩ := relative_isoperimetric_ball_three_real
  refine ⟨1 / (6 * C), by positivity, fun E hE hmE x hx => ?_⟩
  obtain ⟨δ, hδ, hflux⟩ := reduced_perimeter_le_six_sectionArea E hE hmE hx
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hflux] with r hflux
  intro hr hrd
  have heq : Eᶜ ∩ ball x r = ball x r \ E := by ext; simp [and_comm]
  have hi : (min (radialVolume E x r) (radialVolume Eᶜ x r)) ^ (2 / 3 : ℝ) ≤
      C * (canonicalPerimeterMeasure E hE hmE).real (ball x r) := by
    simpa only [radialVolume, heq] using hI E hE hmE x r hr
  have hsum := radialVolume_add_compl hmE x hr.le
  have hp := hflux hr hrd
  have hleft : (canonicalPerimeterMeasure E hE hmE).real (ball x r) ≤
      6 * radialSectionArea E x r := hp.1
  have hright : (canonicalPerimeterMeasure E hE hmE).real (ball x r) ≤
      6 * radialSectionArea Eᶜ x r := hp.2
  constructor
  · intro hs
    have hmin : radialVolume E x r ≤ radialVolume Eᶜ x r := by linarith
    rw [min_eq_left hmin] at hi
    have h := hi.trans (mul_le_mul_of_nonneg_left hleft hC.le)
    rw [one_div, ← div_eq_inv_mul]
    apply (div_le_iff₀ (by positivity : 0 < 6 * C)).mpr
    nlinarith
  · intro hs
    have hmin : radialVolume Eᶜ x r ≤ radialVolume E x r := by linarith
    rw [min_eq_right hmin] at hi
    have h := hi.trans (mul_le_mul_of_nonneg_left hright hC.le)
    rw [one_div, ← div_eq_inv_mul]
    apply (div_le_iff₀ (by positivity : 0 < 6 * C)).mpr
    nlinarith

/-- Geometric hypotheses for the cubic lower-barrier lemma, with genuine radial derivatives.
The positive constants are independent of the set and the reduced point. -/
theorem exists_density_differential_inequalities :
    ∃ b : ℝ, 0 < b ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (E : Set AmbientSpace) (hE : HasLocallyFinitePerimeter E)
        (hmE : NullMeasurableSet E volume) (x : AmbientSpace), x ∈ reducedBoundary E hE hmE →
        ∃ δ > 0, ∀ᵐ r : ℝ, 0 < r → r ≤ δ →
          (radialVolume E x r ≤ b * r ^ 3 →
            c * radialVolume E x r ^ (2 / 3 : ℝ) ≤ deriv (radialVolume E x) r) ∧
          (radialVolume Eᶜ x r ≤ b * r ^ 3 →
            c * radialVolume Eᶜ x r ^ (2 / 3 : ℝ) ≤ deriv (radialVolume Eᶜ x) r) := by
  obtain ⟨c, hc, hbound⟩ := density_section_inequalities
  refine ⟨2 * Real.pi / 3, by positivity, c, hc, fun E hE hmE x hx => ?_⟩
  obtain ⟨δ, hδ, hb⟩ := hbound E hE hmE x hx
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hb, ae_deriv_radialVolume hmE x, ae_deriv_radialVolume hmE.compl x]
    with r hr hderiv hderivc
  intro hrpos hrd
  rw [hderiv hrpos, hderivc hrpos]
  exact hr hrpos hrd

end LiquidDrop
