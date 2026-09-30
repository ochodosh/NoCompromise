module

public import NoCompromise.Sobolev.W11Pullback

@[expose] public section

/-!
# L¹ bounds for the actual reflected weak-gradient field

The indicator extension agrees almost everywhere after folding, since the
coordinate hyperplane has zero volume. This gives the two-sheet bound for
arbitrary vector-valued data and its adjoint derivative pullback.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace LiquidDrop

lemma indicator_halfCube_comp_coordinateFold_ae_vector {n : ℕ} {F : Type*} [Zero F]
    (i : Fin n) {r R : ℝ} (hrR : r ≤ R) (g : EuclideanSpace ℝ (Fin n) → F) :
    ((coordinateHalfCube i R).indicator g ∘ coordinateFold i) =ᵐ[
      volume.restrict (coordinateCube n r)] (g ∘ coordinateFold i) := by
  filter_upwards [ae_restrict_of_ae (ae_coordinate_ne_zero i),
    ae_restrict_mem (isOpen_coordinateCube n r).measurableSet] with x hx hxQ
  exact indicator_of_mem (coordinateFold_mem_halfCube (coordinateCube_mono hrR hxQ) hx) g

theorem integrableOn_coordinateFold_halfCube_vector {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] (i : Fin n) {r R : ℝ} (hrR : r ≤ R)
    {g : EuclideanSpace ℝ (Fin n) → F} (hg : IntegrableOn g (coordinateHalfCube i R)) :
    IntegrableOn (g ∘ coordinateFold i) (coordinateCube n r) ∧
      (∫ x in coordinateCube n r, ‖g (coordinateFold i x)‖) ≤
        2 * ∫ x in coordinateHalfCube i R, ‖g x‖ := by
  let g0 := (coordinateHalfCube i R).indicator g
  have hg0 : Integrable g0 := hg.integrable_indicator (isOpen_coordinateHalfCube i R).measurableSet
  have hae := indicator_halfCube_comp_coordinateFold_ae_vector i hrR g
  have hi := (integrable_comp_coordinateFold i hg0).integrableOn (s := coordinateCube n r)
  refine ⟨hi.congr hae, ?_⟩
  have hb := integral_norm_comp_shiftedCoordinateFold_le i 0
    (isOpen_coordinateCube n r).measurableSet (mapsTo_univ _ _) hg0.integrableOn
  calc
    _ = ∫ x in coordinateCube n r, ‖g0 (coordinateFold i x)‖ :=
      integral_congr_ae (hae.fun_comp (fun y => ‖y‖)).symm
    _ ≤ 2 * ∫ x, ‖g0 x‖ := by
      simpa only [shiftedCoordinateFold_zero, Measure.restrict_univ] using hb
    _ = _ := by
      simp only [g0, norm_indicator_eq_indicator_norm,
        integral_indicator (isOpen_coordinateHalfCube i R).measurableSet]

theorem integrableOn_adjoint_coordinateFold_halfCube {n : ℕ}
    (i : Fin n) {r R : ℝ} (hrR : r ≤ R)
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hG : IntegrableOn G (coordinateHalfCube i R)) :
    IntegrableOn (fun x => (fderiv ℝ (coordinateFold i) x).adjoint
      (G (coordinateFold i x))) (coordinateCube n r) ∧
      (∫ x in coordinateCube n r, ‖(fderiv ℝ (coordinateFold i) x).adjoint
        (G (coordinateFold i x))‖) ≤ 2 * ∫ x in coordinateHalfCube i R, ‖G x‖ := by
  obtain ⟨hi, hb⟩ := integrableOn_coordinateFold_halfCube_vector i hrR hG
  obtain ⟨hi', hb'⟩ := integrable_fderiv_adjoint_apply (lipschitzWith_coordinateFold i) hi
  simp only [NNReal.coe_one, one_mul] at hb'
  exact ⟨hi', hb'.trans hb⟩

end LiquidDrop
