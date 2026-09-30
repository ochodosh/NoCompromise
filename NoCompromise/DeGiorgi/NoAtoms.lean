module

public import NoCompromise.DeGiorgi.Reduced
public import NoCompromise.BV.StrictApprox

@[expose] public section

/-!
# The perimeter measure has no point atoms

Shrinking smooth tests have gradient integral of order radius squared in three
space dimensions. The distributional identity and dominated convergence then
force each coordinate of a possible polar atom to vanish.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma gradient_comp_sub {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (a x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => f (y - a)) x = gradient f (x - a) := by
  apply PiLp.ext
  intro i
  simp only [gradient_apply_eq_fderiv_single, fderiv_comp_sub]

/-- Exact scaling of the total gradient of a scalar test in three dimensions. -/
lemma integral_norm_gradient_dilate_translate {f : AmbientSpace → ℝ}
    (hf : ContDiff ℝ 1 f) (a : AmbientSpace) {c : ℝ} (hc : 0 < c) :
    (∫ x, ‖gradient (fun y => f (c • (y - a))) x‖) =
      c⁻¹ ^ 2 * ∫ x, ‖gradient f x‖ := by
  simp_rw [gradient_comp_sub (fun y => f (c • y)), gradient_comp_const_smul hf,
    norm_smul, Real.norm_of_nonneg hc.le]
  rw [integral_const_mul,
    integral_sub_right_eq_self (fun z : AmbientSpace => ‖gradient f (c • z)‖) a,
    Measure.integral_comp_smul_of_nonneg volume
      (fun z : AmbientSpace => ‖gradient f z‖) c (hR := hc.le)]
  simp only [AmbientSpace, finrank_euclideanSpace_fin, smul_eq_mul]
  field_simp

/-- Fixed-center smooth tests shrinking to a point. -/
def atomTest (a : AmbientSpace) (j : ℕ) : AmbientSpace → ℝ :=
  let φ : ContDiffBump (0 : AmbientSpace) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  fun y => φ (((j : ℝ) + 1) • (y - a))

lemma atomTest_contDiff (a : AmbientSpace) (j : ℕ) : ContDiff ℝ 1 (atomTest a j) := by
  exact (ContDiffBump.contDiff _).comp ((contDiff_id.sub contDiff_const).const_smul _)

lemma atomTest_hasCompactSupport (a : AmbientSpace) (j : ℕ) :
    HasCompactSupport (atomTest a j) := by
  let φ : ContDiffBump (0 : AmbientSpace) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  exact (φ.hasCompactSupport.comp_homeomorph
    (Homeomorph.smulOfNeZero _ (by positivity : (j : ℝ) + 1 ≠ 0))).comp_homeomorph
      (Homeomorph.subRight a)

lemma atomTest_bounds (a y : AmbientSpace) (j : ℕ) :
    0 ≤ atomTest a j y ∧ atomTest a j y ≤ 1 :=
  ⟨ContDiffBump.nonneg _, ContDiffBump.le_one _⟩

lemma atomTest_eq_zero_of_dist (a y : AmbientSpace) (j : ℕ)
    (h : 2 ≤ ((j : ℝ) + 1) * dist y a) : atomTest a j y = 0 := by
  apply ContDiffBump.zero_of_le_dist
  simpa only [dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (j : ℝ) + 1),
    ← dist_eq_norm_sub] using h

lemma atomTest_eq_zero_outside (a y : AmbientSpace) (j : ℕ)
    (h : y ∉ closedBall a 2) : atomTest a j y = 0 := by
  apply atomTest_eq_zero_of_dist
  have hd : 2 < dist y a := by simpa only [mem_closedBall, not_le] using h
  nlinarith [Nat.cast_nonneg (α := ℝ) j]

lemma tendsto_atomTest (a y : AmbientSpace) :
    Tendsto (fun j => atomTest a j y) atTop
      (𝓝 (({a} : Set AmbientSpace).indicator (fun _ => (1 : ℝ)) y)) := by
  by_cases hy : y = a
  · subst y
    have heq (j) : atomTest a j a = 1 := by
      apply ContDiffBump.one_of_mem_closedBall
      simp
    simpa only [heq, mem_singleton, indicator_of_mem] using
      (tendsto_const_nhds (x := (1 : ℝ)))
  · have hd : 0 < dist y a := dist_pos.mpr hy
    have ht : Tendsto (fun j : ℕ => ((j : ℝ) + 1) * dist y a) atTop atTop :=
      Filter.Tendsto.atTop_mul_const hd
        (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    have hz : ∀ᶠ j : ℕ in atTop, atomTest a j y = 0 :=
      (ht.eventually (eventually_ge_atTop 2)).mono fun j hj => atomTest_eq_zero_of_dist a y j hj
    simpa only [indicator_of_notMem (show y ∉ ({a} : Set AmbientSpace) from hy)] using
      (tendsto_const_nhds (x := (0 : ℝ))).congr' (hz.mono fun _ h => h.symm)

lemma tendsto_integral_norm_gradient_atomTest (a : AmbientSpace) :
    Tendsto (fun j => ∫ x, ‖gradient (atomTest a j) x‖) atTop (𝓝 0) := by
  let φ : ContDiffBump (0 : AmbientSpace) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  have heq (j : ℕ) : (∫ x, ‖gradient (atomTest a j) x‖) =
      ((j : ℝ) + 1)⁻¹ ^ 2 * ∫ x, ‖gradient φ x‖ :=
    integral_norm_gradient_dilate_translate φ.contDiff a (by positivity)
  simp_rw [heq]
  have ht : Tendsto (fun j : ℕ => ((j : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [zero_pow (by norm_num : 2 ≠ 0), zero_mul] using
    (ht.pow 2).mul_const (∫ x, ‖gradient φ x‖)

/-- Shrinking tests detect exactly the mass of a singleton, for locally integrable densities. -/
lemma tendsto_integral_atomTest_mul (μ : Measure AmbientSpace)
    [IsFiniteMeasureOnCompacts μ] {f : AmbientSpace → ℝ}
    (hf : Measurable f) (hi : LocallyIntegrable f μ) (a : AmbientSpace) :
    Tendsto (fun j => ∫ x, atomTest a j x * f x ∂μ) atTop
      (𝓝 (μ.real {a} * f a)) := by
  have hib : Integrable ((closedBall a 2).indicator (fun x => ‖f x‖)) μ :=
    (integrable_indicator_iff isClosed_closedBall.measurableSet).mpr
      (hi.integrableOn_isCompact (isCompact_closedBall a 2)).norm
  have ht : Tendsto (fun j => ∫ x, atomTest a j x * f x ∂μ) atTop
      (𝓝 (∫ x, ({a} : Set AmbientSpace).indicator f x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      ((closedBall a 2).indicator (fun x => ‖f x‖))
    · intro j
      exact ((atomTest_contDiff a j).continuous.measurable.mul hf).aestronglyMeasurable
    · exact hib
    · intro j
      apply Eventually.of_forall
      intro x
      by_cases hx : x ∈ closedBall a 2
      · rw [indicator_of_mem hx, norm_mul, Real.norm_of_nonneg (atomTest_bounds a x j).1]
        exact mul_le_of_le_one_left (norm_nonneg _) (atomTest_bounds a x j).2
      · rw [atomTest_eq_zero_outside a x j hx, zero_mul, norm_zero,
          indicator_of_notMem hx]
    · apply Eventually.of_forall
      intro x
      have h := (tendsto_atomTest a x).mul_const (f x)
      convert h using 1
      by_cases hx : x = a <;> simp [hx]
  simpa only [integral_indicator (measurableSet_singleton a), integral_singleton,
    smul_eq_mul] using ht

/-- The distributional derivative tested against shrinking cutoffs tends to zero. -/
lemma IsAmbientOutwardPerimeterPolar.tendsto_atomTest_pairing
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {ν : AmbientSpace → AmbientSpace}
    (h : IsAmbientOutwardPerimeterPolar E μ ν) (a : AmbientSpace) (i : Fin 3) :
    Tendsto (fun j => ∫ x, atomTest a j x * (-ν x i) ∂μ) atTop (𝓝 0) := by
  have hbound (j : ℕ) : ‖∫ x, atomTest a j x * (-ν x i) ∂μ‖ ≤
      ∫ x, ‖gradient (atomTest a j) x‖ := by
    let φ : CompactlySupportedContinuousMap AmbientSpace ℝ :=
      ⟨⟨atomTest a j, (atomTest_contDiff a j).continuous⟩, atomTest_hasCompactSupport a j⟩
    have hp := h.coordinate_eq i φ (atomTest_contDiff a j)
    change -(∫ x, E.indicator (fun _ => (1 : ℝ)) x *
      fderiv ℝ (atomTest a j) x (EuclideanSpace.single i 1)) =
        ∫ x, atomTest a j x * (-ν x i) ∂μ at hp
    rw [← hp, norm_neg]
    apply (norm_integral_le_integral_norm _).trans
    have hig : Integrable (gradient (atomTest a j)) :=
      (continuous_gradient_of_contDiff (atomTest_contDiff a j)).integrable_of_hasCompactSupport
        ((atomTest_hasCompactSupport a j).of_isClosed_subset (isClosed_tsupport _)
          (tsupport_gradient_subset _))
    apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hig.norm
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ E
    · simpa only [indicator_of_mem hx, one_mul, φ, CompactlySupportedContinuousMap.coe_mk,
        ContinuousMap.coe_mk, ← gradient_apply_eq_fderiv_single] using
        PiLp.norm_apply_le (gradient (atomTest a j) x) i
    · simp only [indicator_of_notMem hx, zero_mul, norm_zero, norm_nonneg]
  exact squeeze_zero_norm hbound (tendsto_integral_norm_gradient_atomTest a)

/-- A locally finite-perimeter set in three dimensions has no perimeter point masses. -/
theorem IsAmbientOutwardPerimeterPolar.measure_singleton
    {E : Set AmbientSpace} {μ : Measure AmbientSpace} {ν : AmbientSpace → AmbientSpace}
    (h : IsAmbientOutwardPerimeterPolar E μ ν) (a : AmbientSpace) : μ {a} = 0 := by
  let := h.finiteOnCompacts
  by_contra ha
  have hpos : 0 < μ.real {a} :=
    ENNReal.toReal_pos ha (isCompact_singleton.measure_lt_top (μ := μ)).ne
  have hνa : ‖ν a‖ = 1 := by
    obtain ⟨x, hx, hnorm⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae ha
      (ae_restrict_of_ae h.norm_ae)
    simpa only [mem_singleton_iff.mp hx] using hnorm
  have hzero (i : Fin 3) : ν a i = 0 := by
    have hmeas : Measurable (fun x => -ν x i) :=
      ((EuclideanSpace.proj (𝕜 := ℝ) i).measurable.comp h.measurable).neg
    have hiloc : LocallyIntegrable (fun x => -ν x i) μ :=
      locallyIntegrable_of_ae_norm_le (C := 1) μ hmeas.aestronglyMeasurable
        (h.norm_ae.mono fun x hx => by
          simpa only [norm_neg, hx] using PiLp.norm_apply_le (ν x) i)
    have hz := tendsto_nhds_unique (tendsto_integral_atomTest_mul μ hmeas hiloc a)
      (h.tendsto_atomTest_pairing a i)
    exact neg_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hpos.ne')
  have hz : ν a = 0 := PiLp.ext fun i => hzero i
  simp only [hz, norm_zero, zero_ne_one] at hνa

/-- The actual canonical perimeter measure has no point atoms. -/
theorem canonicalPerimeterMeasure_nullSingletonClass (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume) :
    NullSingletonClass (canonicalPerimeterMeasure E hE hmE) :=
  ⟨(canonicalPerimeterPolar E hE hmE).measure_singleton⟩

end LiquidDrop
