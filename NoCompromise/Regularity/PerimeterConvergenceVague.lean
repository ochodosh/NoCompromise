import NoCompromise.Regularity.PerimeterConvergenceMeasures
import NoCompromise.Measure.WeakStarBalls
import NoCompromise.Measure.RadialMeasures

/-!
# Local weak convergence and continuity balls inside the domain

A compact cutoff turns measures on the open subtype into genuine finite ambient
measures. Its value is one on the ball under consideration, so the proved
ambient continuity-ball theorem gives the actual local ball masses.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology CompactlySupported
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Extend a compactly weighted subtype measure to the ambient Euclidean space. -/
def cutoffAmbientMeasure {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (μ : Measure U) (φ : C_c(U, ℝ)) : Measure (EuclideanSpace ℝ (Fin n)) :=
  Measure.map Subtype.val (μ.withDensity (fun z => ENNReal.ofReal (φ z)))

lemma finite_cutoffAmbientMeasure {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (μ : Measure U) [IsFiniteMeasureOnCompacts μ] (φ : C_c(U, ℝ))
    (hn : ∀ z, 0 ≤ φ z) : IsFiniteMeasure (cutoffAmbientMeasure μ φ) := by
  have hi : Integrable (fun z => φ z) μ :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  let : IsFiniteMeasure (μ.withDensity fun z => ENNReal.ofReal (φ z)) :=
    isFiniteMeasure_withDensity
      ((hasFiniteIntegral_iff_ofReal (Eventually.of_forall hn)).mp hi.2).ne
  unfold cutoffAmbientMeasure
  infer_instance

lemma integral_cutoffAmbientMeasure {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (μ : Measure U) (φ : C_c(U, ℝ)) (hn : ∀ z, 0 ≤ φ z)
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ} (hψ : Measurable ψ) :
    (∫ z, ψ z ∂cutoffAmbientMeasure μ φ) = ∫ z : U, φ z * ψ z ∂μ := by
  have hm : Measurable (fun z : U => ENNReal.ofReal (φ z)) := by fun_prop
  rw [cutoffAmbientMeasure, integral_map measurable_subtype_coe.aemeasurable
    hψ.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hm
      (by simp)]
  simp only [ENNReal.toReal_ofReal (hn _), smul_eq_mul]

lemma cutoffAmbientMeasure_apply_of_one {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (μ : Measure U) (φ : C_c(U, ℝ)) {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA : MeasurableSet A) (hφ : ∀ z : U, (z : EuclideanSpace ℝ (Fin n)) ∈ A → φ z = 1) :
    cutoffAmbientMeasure μ φ A = μ (Subtype.val ⁻¹' A) := by
  rw [cutoffAmbientMeasure, Measure.map_apply measurable_subtype_coe hA,
    withDensity_apply _ (hA.preimage measurable_subtype_coe)]
  calc
    _ = ∫⁻ _z : U in Subtype.val ⁻¹' A, (1 : ℝ≥0∞) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (hA.preimage measurable_subtype_coe)] with z hz
      simp only [hφ z hz, ENNReal.ofReal_one]
    _ = _ := by simp

/-- Multiply a compact subtype test by a continuous ambient test. -/
def mulAmbientCC {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (φ : C_c(U, ℝ)) (ψ : C_c(EuclideanSpace ℝ (Fin n), ℝ)) : C_c(U, ℝ) where
  toFun z := φ z * ψ z
  continuous_toFun := φ.continuous.mul (ψ.continuous.comp continuous_subtype_val)
  hasCompactSupport' := φ.hasCompactSupport.mul_right

lemma tendsto_integral_cutoffAmbientMeasure {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (μs : ℕ → Measure U) (μ : Measure U)
    (hweak : ∀ ψ : C_c(U, ℝ),
      Tendsto (fun j => ∫ z, ψ z ∂μs j) atTop (𝓝 (∫ z, ψ z ∂μ)))
    (φ : C_c(U, ℝ)) (hn : ∀ z, 0 ≤ φ z)
    (ψ : C_c(EuclideanSpace ℝ (Fin n), ℝ)) :
    Tendsto (fun j => ∫ z, ψ z ∂cutoffAmbientMeasure (μs j) φ) atTop
      (𝓝 (∫ z, ψ z ∂cutoffAmbientMeasure μ φ)) := by
  have hm : Measurable (fun z => ψ z) := ψ.continuous.measurable
  simp only [integral_cutoffAmbientMeasure _ φ hn hm]
  exact hweak (mulAmbientCC φ ψ)

/-- Local vague convergence gives the real masses of every interior continuity ball. -/
theorem tendsto_local_real_ball_of_compact_test_convergence {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (μs : ℕ → Measure U) (μ : Measure U)
    [∀ j, IsFiniteMeasureOnCompacts (μs j)] [IsFiniteMeasureOnCompacts μ]
    (hweak : ∀ φ : C_c(U, ℝ),
      Tendsto (fun j => ∫ z, φ z ∂μs j) atTop (𝓝 (∫ z, φ z ∂μ)))
    (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    (hRU : closedBall x r ⊆ U) (hnull : μ (Subtype.val ⁻¹' sphere x r) = 0) :
    Tendsto (fun j => (μs j).real (Subtype.val ⁻¹' ball x r)) atTop
      (𝓝 (μ.real (Subtype.val ⁻¹' ball x r))) := by
  obtain ⟨ψ, hψK, hcψ, hsψ, hbψ⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen (isCompact_closedBall x r) hU hRU
  let Ψ : C_c(EuclideanSpace ℝ (Fin n), ℝ) := ⟨ψ, hcψ⟩
  let φ : C_c(U, ℝ) := restrictSupportedCC ⟨Ψ, hsψ⟩
  have hn (z : U) : 0 ≤ φ z := (hbψ z).1
  let : ∀ j, IsFiniteMeasure (cutoffAmbientMeasure (μs j) φ) :=
    fun j => finite_cutoffAmbientMeasure (μs j) φ hn
  let : IsFiniteMeasure (cutoffAmbientMeasure μ φ) := finite_cutoffAmbientMeasure μ φ hn
  have hφb : ∀ z : U, (z : EuclideanSpace ℝ (Fin n)) ∈ ball x r → φ z = 1 :=
    fun z hz => hψK (ball_subset_closedBall hz)
  have hφs : ∀ z : U, (z : EuclideanSpace ℝ (Fin n)) ∈ sphere x r → φ z = 1 :=
    fun z hz => hψK (sphere_subset_closedBall hz)
  have hnull' : cutoffAmbientMeasure μ φ (sphere x r) = 0 := by
    rw [cutoffAmbientMeasure_apply_of_one μ φ isClosed_sphere.measurableSet hφs]
    exact hnull
  have h := tendsto_real_ball_of_compact_test_convergence
    (fun j => cutoffAmbientMeasure (μs j) φ) (cutoffAmbientMeasure μ φ)
    (tendsto_integral_cutoffAmbientMeasure μs μ hweak φ hn) x hr hnull'
  simpa only [measureReal_def,
    cutoffAmbientMeasure_apply_of_one _ φ measurableSet_ball hφb] using h

/-- The extended-real masses converge as well; finiteness follows from compact containment. -/
theorem tendsto_local_ball_of_compact_test_convergence {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (μs : ℕ → Measure U) (μ : Measure U)
    [∀ j, IsFiniteMeasureOnCompacts (μs j)] [IsFiniteMeasureOnCompacts μ]
    (hweak : ∀ φ : C_c(U, ℝ),
      Tendsto (fun j => ∫ z, φ z ∂μs j) atTop (𝓝 (∫ z, φ z ∂μ)))
    (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    (hRU : closedBall x r ⊆ U) (hnull : μ (Subtype.val ⁻¹' sphere x r) = 0) :
    Tendsto (fun j => μs j (Subtype.val ⁻¹' ball x r)) atTop
      (𝓝 (μ (Subtype.val ⁻¹' ball x r))) := by
  have hK : IsCompact ((Subtype.val : U → EuclideanSpace ℝ (Fin n)) ⁻¹' closedBall x r) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' (isCompact_closedBall x r)
      (by simpa using hRU)
  have hf (ρ : Measure U) [IsFiniteMeasureOnCompacts ρ] :
      ρ (Subtype.val ⁻¹' ball x r) ≠ ∞ :=
    ((measure_mono (preimage_mono ball_subset_closedBall)).trans_lt hK.measure_lt_top).ne
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_local_real_ball_of_compact_test_convergence hU μs μ hweak x hr hRU hnull)
  simpa only [Function.comp_def, measureReal_def, ENNReal.ofReal_toReal (hf _)] using h

end LiquidDrop
