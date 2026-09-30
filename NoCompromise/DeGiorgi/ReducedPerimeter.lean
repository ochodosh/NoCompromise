module

public import NoCompromise.DeGiorgi.NormalFlux
public import NoCompromise.DeGiorgi.RadialFlux

@[expose] public section

/-!
# Quadratic perimeter bounds near reduced points

A uniform surface-flux bound at almost every radius combines with the defining
normal-flux comparison. Selecting a good radius between r and 2r extends the
estimate to every small positive radius, without any sphere-nullness premise.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

lemma abs_inner_le_three_mul_of_coordinate_bound {ν v : AmbientSpace} {B : ℝ}
    (hν : ‖ν‖ = 1) (hv : ∀ i : Fin 3, |v i| ≤ B) :
    |inner ℝ ν v| ≤ 3 * B := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
  calc
    _ = |∑ i : Fin 3, ν i * v i| := by congr 1; apply Finset.sum_congr rfl; intros; ring
    _ ≤ ∑ i : Fin 3, |ν i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, B := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      have hi : |ν i| ≤ 1 := by
        simpa only [Real.norm_eq_abs, hν] using PiLp.norm_apply_le ν i
      exact (mul_le_mul_of_nonneg_right hi (abs_nonneg _)).trans (by simpa using hv i)
    _ = 3 * B := by simp

/-- An almost-everywhere quadratic bound controls every smaller radius. -/
lemma measure_ball_quadratic_bound_of_ae {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasureOnCompacts μ]
    (x : EuclideanSpace ℝ (Fin n)) {C δ : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ s : ℝ, 0 < s → s ≤ δ → μ.real (ball x s) ≤ C * s ^ 2)
    {r : ℝ} (hr : 0 < r) (hrδ : r ≤ δ / 2) :
    μ.real (ball x r) ≤ (4 * C) * r ^ 2 := by
  have hvol : volume (Ioo r (2 * r)) ≠ 0 := by
    rw [Real.volume_Ioo, ne_eq, ENNReal.ofReal_eq_zero]
    linarith
  obtain ⟨s, hs, hbs⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hvol
    (ae_restrict_of_ae hb)
  have hsr : s ≤ 2 * r := hs.2.le
  have hspos : 0 < s := hr.trans hs.1
  have hsd : s ≤ δ := by linarith
  have hfinite : μ (ball x s) ≠ ∞ :=
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall x s).measure_lt_top).ne
  calc
    μ.real (ball x r) ≤ μ.real (ball x s) :=
      ENNReal.toReal_mono hfinite (measure_mono (ball_subset_ball hs.1.le))
    _ ≤ C * s ^ 2 := hbs hspos hsd
    _ ≤ C * (2 * r) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hspos.le hsr 2) hC
    _ = (4 * C) * r ^ 2 := by ring

/-- A universal quadratic bound holds at every reduced point and every small radius. -/
theorem reduced_perimeter_upper_bound_real (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x : AmbientSpace} (hx : x ∈ reducedBoundary E hE hmE) :
    ∃ δ > 0, ∀ r, 0 < r → r ≤ δ →
      (canonicalPerimeterMeasure E hE hmE).real (ball x r) ≤ (96 * Real.pi) * r ^ 2 := by
  let μ := canonicalPerimeterMeasure E hE hmE
  let := (canonicalPerimeterPolar E hE hmE).finiteOnCompacts
  obtain ⟨δ, hδ, hcomp⟩ := normal_flux_comparison E hE hmE hx
  have hcoords := (ae_restrict_iff' measurableSet_Ioi).mp
    (ae_abs_perimeterDerivativeBall_apply_le E hE hmE x)
  have hb : ∀ᵐ r : ℝ, 0 < r → r ≤ δ → μ.real (ball x r) ≤ (24 * Real.pi) * r ^ 2 := by
    filter_upwards [hcoords] with r hcoord
    intro hr hrd
    have ha := abs_inner_le_three_mul_of_coordinate_bound
      (norm_reducedNormal E hE hmE hx) (hcoord hr)
    calc
      μ.real (ball x r) ≤ -2 * inner ℝ (reducedNormal E hE hmE x)
          (perimeterDerivativeBall E hE hmE x r) := hcomp r hr hrd
      _ ≤ 2 * |inner ℝ (reducedNormal E hE hmE x)
          (perimeterDerivativeBall E hE hmE x r)| := by
        linarith [neg_le_abs (inner ℝ (reducedNormal E hE hmE x)
          (perimeterDerivativeBall E hE hmE x r))]
      _ ≤ 2 * (3 * (4 * Real.pi * r ^ 2)) := mul_le_mul_of_nonneg_left ha (by norm_num)
      _ = (24 * Real.pi) * r ^ 2 := by ring
  refine ⟨δ / 2, by positivity, fun r hr hrd => ?_⟩
  have h := measure_ball_quadratic_bound_of_ae μ x (C := 24 * Real.pi) (by positivity)
    hb hr hrd
  convert h using 1
  ring

/-- The actual extended-valued perimeter measure satisfies the blueprint's upper bound. -/
theorem reduced_perimeter_upper_bound (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x : AmbientSpace} (hx : x ∈ reducedBoundary E hE hmE) :
    ∃ δ > 0, ∀ r, 0 < r → r ≤ δ →
      canonicalPerimeterMeasure E hE hmE (ball x r) ≤ ENNReal.ofReal ((96 * Real.pi) * r ^ 2) := by
  let := (canonicalPerimeterPolar E hE hmE).finiteOnCompacts
  obtain ⟨δ, hδ, hb⟩ := reduced_perimeter_upper_bound_real E hE hmE hx
  refine ⟨δ, hδ, fun r hr hrd => ?_⟩
  have hm : canonicalPerimeterMeasure E hE hmE (ball x r) ≠ ∞ :=
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall x r).measure_lt_top).ne
  rw [← ENNReal.ofReal_toReal hm]
  exact ENNReal.ofReal_le_ofReal (hb r hr hrd)

end LiquidDrop
