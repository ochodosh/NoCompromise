import NoCompromise.DeGiorgi.BlowupScaling
import NoCompromise.DeGiorgi.ReducedPerimeter
import NoCompromise.DeGiorgi.ReducedDensity
import NoCompromise.BV.Compactness

/-!
# Compactness of blow-ups at reduced points

The quadratic perimeter bound supplies uniform local BV bounds for every
sequence of positive scales tending to zero. Compactness is applied to the
actual dilated indicator functions.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

lemma perimeterIn_blowupSet_ball_real (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    (x : AmbientSpace) {r : ℝ} (hr : 0 < r) (R : ℝ) :
    (perimeterIn (blowupSet E x r) (ball 0 R)).toReal =
      (r⁻¹) ^ 2 * (canonicalPerimeterMeasure E hE hmE).real (ball x (r * R)) := by
  rw [perimeterIn_blowupSet_ball (by norm_num) E x hr R]
  simp only [show 3 - 1 = 2 by rfl, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg (r⁻¹)), measureReal_def,
    canonicalPerimeterMeasure_open E hE hmE isOpen_ball]

/-- The rescaled perimeter of each fixed ball is eventually bounded independently of scale. -/
theorem eventually_perimeterIn_blowupSet_ball_le (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x : AmbientSpace} (hx : x ∈ reducedBoundary E hE hmE)
    {r : ℕ → ℝ} (hr : ∀ j, 0 < r j) (ht : Tendsto r atTop (𝓝 0))
    {R : ℝ} (hR : 0 < R) :
    ∀ᶠ j in atTop, (perimeterIn (blowupSet E x (r j)) (ball 0 R)).toReal ≤
      (96 * Real.pi) * R ^ 2 := by
  obtain ⟨δ, hδ, hb⟩ := reduced_perimeter_upper_bound_real E hE hmE hx
  have hsmall : ∀ᶠ j in atTop, r j * R < δ := by
    have h := (ht.mul_const R).eventually (Iio_mem_nhds (show 0 * R < δ by simpa using hδ))
    exact h
  filter_upwards [hsmall] with j hj
  rw [perimeterIn_blowupSet_ball_real E hE hmE x (hr j)]
  calc
    _ ≤ (r j)⁻¹ ^ 2 * ((96 * Real.pi) * (r j * R) ^ 2) :=
      mul_le_mul_of_nonneg_left (hb _ (mul_pos (hr j) hR) hj.le) (sq_nonneg _)
    _ = (96 * Real.pi) * R ^ 2 := by field_simp [(hr j).ne']

/-- Uniform local perimeter bounds for an arbitrary sequence of vanishing positive scales. -/
theorem bounded_perimeterIn_blowupSet (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x : AmbientSpace} (hx : x ∈ reducedBoundary E hE hmE)
    {r : ℕ → ℝ} (hr : ∀ j, 0 < r j) (ht : Tendsto r atTop (𝓝 0))
    {A : Set AmbientSpace} (hcA : IsCompact (closure A)) :
    ∃ C : ℝ, ∀ j, (perimeterIn (blowupSet E x (r j)) A).toReal ≤ C := by
  obtain ⟨R, hR, hAR⟩ := hcA.isBounded.subset_ball_lt 0 (0 : AmbientSpace)
  have hAB : A ⊆ ball (0 : AmbientSpace) R := subset_closure.trans hAR
  have hle (j) : (perimeterIn (blowupSet E x (r j)) A).toReal ≤
      (perimeterIn (blowupSet E x (r j)) (ball 0 R)).toReal := by
    apply ENNReal.toReal_mono
      ((hE.blowupSet (by norm_num) x (hr j)) _ isOpen_ball
        isBounded_ball.isCompact_closure).ne
    exact variation_mono isOpen_ball.measurableSet hAB
  have hb : atTop.IsBoundedUnder (· ≤ ·)
      (fun j => (perimeterIn (blowupSet E x (r j)) A).toReal) := by
    refine ⟨(96 * Real.pi) * R ^ 2, ?_⟩
    change ∀ᶠ j in atTop, (perimeterIn (blowupSet E x (r j)) A).toReal ≤ _
    filter_upwards [eventually_perimeterIn_blowupSet_ball_le E hE hmE hx hr ht hR]
      with j hj
    exact (hle j).trans hj
  obtain ⟨C, hC⟩ := hb.bddAbove_range
  exact ⟨C, fun j => hC (mem_range_self j)⟩

lemma integral_abs_indicator_one_le_volume {n : ℕ}
    {E A : Set (EuclideanSpace ℝ (Fin n))} (hE : NullMeasurableSet E volume)
    (hcA : IsCompact (closure A)) :
    (∫ x in A, |E.indicator (fun _ => (1 : ℝ)) x|) ≤ volume.real A := by
  have hi' := (locallyIntegrable_indicator_one hE).integrableOn_isCompact hcA
  have hi := hi'.mono_set (subset_closure : A ⊆ closure A)
  have hfin : volume A < ∞ := (measure_mono subset_closure).trans_lt hcA.measure_lt_top
  let : IsFiniteMeasure (volume.restrict A) := ⟨by simpa using hfin⟩
  calc
    _ ≤ ∫ _x in A, (1 : ℝ) := by
      apply integral_mono_ae hi.abs (integrable_const _)
      exact Eventually.of_forall fun x => by by_cases hx : x ∈ E <;> simp [hx]
    _ = volume.real A := by simp

/-- Every blow-up sequence at a reduced point has a locally L¹ convergent subsequence
whose limit is a measurable set with locally finite perimeter. -/
theorem exists_blowup_subsequence (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x : AmbientSpace} (hx : x ∈ reducedBoundary E hE hmE)
    {r : ℕ → ℝ} (hr : ∀ j, 0 < r j) (ht : Tendsto r atTop (𝓝 0)) :
    ∃ F : Set AmbientSpace, MeasurableSet F ∧ HasLocallyFinitePerimeter F ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ K : Set AmbientSpace, IsCompact K →
        Tendsto (fun j => ∫ y in K,
          |(blowupSet E x (r (σ j))).indicator (fun _ => (1 : ℝ)) y -
            F.indicator (fun _ => (1 : ℝ)) y|) atTop (𝓝 0) := by
  apply bv_compactness_indicators_univ (fun j => blowupSet E x (r j))
    (fun j => hE.blowupSet (by norm_num) x (hr j))
    (fun j => nullMeasurableSet_blowupSet hmE x (hr j))
  intro A _ hcA
  obtain ⟨C, hC⟩ := bounded_perimeterIn_blowupSet E hE hmE hx hr ht hcA
  refine ⟨volume.real A + C, fun j => ?_⟩
  exact add_le_add (integral_abs_indicator_one_le_volume
    (nullMeasurableSet_blowupSet hmE x (hr j)) hcA) (hC j)

end LiquidDrop
