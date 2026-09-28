import NoCompromise.Elliptic.BoundaryNeumannQuotientEnergy

/-! Uniform energy of the actual tangential quotients, from Caccioppoli. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- The energy constant is fixed before the original data, direction and step.
Only C¹,α norms of the original solution and source enter the bound. -/
theorem boundary_neumann_quotient_h1_bound {α lam cap M N : ℝ}
    (hα : 0 < α) (hlam : 0 < lam) (hM : 0 ≤ M) (_hN : 0 ≤ N) :
    ∃ E ≥ 0, ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3))
      (H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (w : EuclideanSpace ℝ (Fin 3) → ℝ),
      BoundaryNeumannClosedData α lam cap M N A H w →
      ∀ (i : Fin 3) (s : ℝ), i ≠ Fin.last 2 → s ≠ 0 → |s| < 1 / 16 →
      (∫ x in boundaryHalfBall (3 / 4),
        ‖coordinateDifferenceQuotient i s (gradient w) x‖ ^ 2) ≤ E := by
  obtain ⟨C, hC, henergy⟩ := boundary_neumann_caccioppoli (cap := cap) hlam
  obtain ⟨K, hK, hholder⟩ := boundary_neumann_quotient_datum_holder hα hM
  let V := boundaryHalfBall (7 / 8 : ℝ)
  let m := volume.real V
  refine ⟨C * (m * N ^ 2 + m * (K * N) ^ 2), by dsimp [m]; positivity, ?_⟩
  intro A H w d i s hi hs0 hs
  let q := coordinateDifferenceQuotient i s w
  let D := coordinateDifferenceQuotient i s (gradient w)
  let G := boundaryNeumannQuotientDatum A (gradient w) H i s
  have hsV : |s| ≤ 1 - (7 / 8 : ℝ) := by linarith
  have hq := d.quotient_h1 hi hsV
  have heq := (d.quotient_equation hα hi hsV).1
  obtain ⟨hw, hbw⟩ := d.solution.mono subset_closure
  have hseg : ∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1,
      x + t • (s • EuclideanSpace.single i 1) ∈ boundaryHalfBall 1 :=
    fun _ hx _ ht => boundary_nondiv_segment_mem_halfBall hi hsV hx ht
  have hqh := nondiv_coordinateDifferenceQuotient_holder
    (isOpen_boundaryHalfBall 1) hw i hs0 hseg
  have hqb (x) (hx : x ∈ V) : ‖q x‖ ≤ N :=
    (hqh.1.nondiv_norm_le hx).trans (hqh.2.trans (hw.derivative_norm_le.trans
      (hbw.trans ((le_add_of_nonneg_right d.source.norm_nonneg).trans d.norm_bound))))
  have hGb0 := (hholder A H w d.coefficient d.source d.solution d.coefficient_norm
    (7 / 8) s i hi hs0 hsV).1
  have hGb (x) (hx : x ∈ V) : ‖G x‖ ≤ K * N :=
    (hGb0 x (subset_closure hx)).trans (mul_le_mul_of_nonneg_left d.norm_bound hK.le)
  have hGc := boundary_neumann_quotient_datum_continuous hα
    d.coefficient d.source d.solution hi hsV
  let : IsFiniteMeasure (volume.restrict V) :=
    ⟨by simpa [V] using boundaryHalfBall_volume_lt_top (7 / 8 : ℝ)⟩
  have hGLp : MemLp G 2 (volume.restrict V) := by
    apply MemLp.of_bound ((hGc.mono subset_closure).aestronglyMeasurable
      (isOpen_boundaryHalfBall _).measurableSet) (K * N)
    filter_upwards [ae_restrict_mem (isOpen_boundaryHalfBall (7 / 8 : ℝ)).measurableSet] with x hx
    exact hGb x hx
  have hqint : (∫ x in V, q x ^ 2) ≤ m * N ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      nondiv_integral_norm_sq_le (isOpen_boundaryHalfBall _).measurableSet
        (isBounded_ball.subset inter_subset_left) hq.memLp_function hqb
  have hGint : (∫ x in V, ‖G x‖ ^ 2) ≤ m * (K * N) ^ 2 :=
    nondiv_integral_norm_sq_le (isOpen_boundaryHalfBall _).measurableSet
      (isBounded_ball.subset inter_subset_left) hGLp hGb
  have hsub : V ⊆ closure (boundaryHalfBall 1) :=
    (boundaryHalfBall_mono (by norm_num : (7 / 8 : ℝ) ≤ 1)).trans subset_closure
  have hAc := d.coefficient.contDiff.continuousOn.mono hsub
  have hb := henergy A q D G (hAc.aestronglyMeasurable (isOpen_boundaryHalfBall _).measurableSet)
    (by
      filter_upwards [ae_restrict_mem (isOpen_boundaryHalfBall (7 / 8 : ℝ)).measurableSet] with x hx
      intro v
      rw [real_inner_comm]
      exact d.elliptic x (hsub hx) v)
    (by
      filter_upwards [ae_restrict_mem (isOpen_boundaryHalfBall (7 / 8 : ℝ)).measurableSet] with x hx
      exact d.coefficient_bound x (hsub hx)) hq hGLp heq
  exact hb.trans (mul_le_mul_of_nonneg_left (add_le_add hqint hGint) hC.le)

end LiquidDrop
