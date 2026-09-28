import NoCompromise.BV.CoareaCoordinates
import NoCompromise.DeGiorgi.HalfspacePairing
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Lipschitz graphs from uniform cone bounds

A bound of height differences by projected differences makes height single-valued
on the projected set. Scalar Lipschitz extension then supplies a global graph
containing the original set. No measurability of that set is required.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal
namespace LiquidDrop

lemma lipschitzWith_graphMapN {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) : LipschitzWith (1 + K) (graphMapN f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := hf.dist_le_mul x y
  simp only [dist_eq_norm, Real.norm_eq_abs] at hh ⊢
  have heq := norm_graphMapN_sub_sq f x y
  have hbound : ‖graphMapN f x - graphMapN f y‖ ≤ ‖x - y‖ + |f x - f y| := by
    rw [Real.norm_eq_abs] at heq
    nlinarith [norm_nonneg (x - y), norm_nonneg (graphMapN f x - graphMapN f y),
      abs_nonneg (f x - f y)]
  simp only [NNReal.coe_add, NNReal.coe_one]
  nlinarith

/-- A set with uniformly Lipschitz height differences is contained in a global graph. -/
theorem exists_lipschitz_graph_of_projection_bound {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin (n + 1)))) {K : ℝ≥0}
    (hS : ∀ x ∈ S, ∀ y ∈ S,
      |x (Fin.last n) - y (Fin.last n)| ≤
        K * ‖graphProjectionN n x - graphProjectionN n y‖) :
    ∃ f : EuclideanSpace ℝ (Fin n) → ℝ,
      LipschitzWith K f ∧ S ⊆ range (graphMapN f) := by
  classical
  let f (p : EuclideanSpace ℝ (Fin n)) : ℝ :=
    if hp : p ∈ graphProjectionN n '' S then hp.choose (Fin.last n) else 0
  have hval (x : EuclideanSpace ℝ (Fin (n + 1))) (hx : x ∈ S) :
      f (graphProjectionN n x) = x (Fin.last n) := by
    have hp : graphProjectionN n x ∈ graphProjectionN n '' S := mem_image_of_mem _ hx
    simp only [f, dite_eq_left hp]
    have hb := hS hp.choose hp.choose_spec.1 x hx
    rw [hp.choose_spec.2, sub_self, norm_zero, mul_zero] at hb
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hb)
  have hf : LipschitzOnWith K f (graphProjectionN n '' S) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro p ⟨x, hx, rfl⟩ q ⟨y, hy, rfl⟩
    rw [hval x hx, hval y hy, Real.dist_eq, dist_eq_norm]
    exact hS x hx y hy
  obtain ⟨g, hg, hfg⟩ := hf.extend_real
  refine ⟨g, hg, ?_⟩
  intro x hx
  refine ⟨graphProjectionN n x, ?_⟩
  have hh : g (graphProjectionN n x) = x (Fin.last n) :=
    (hfg (mem_image_of_mem _ hx)).symm.trans (hval x hx)
  change graphAppendN (graphProjectionN n x) (g (graphProjectionN n x)) = x
  rw [hh, graphAppendN_projection]

/-- A cone of aperture at most one half around the horizontal plane gives a
one-Lipschitz height function. -/
theorem exists_lipschitz_graph_of_half_cone {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hS : ∀ x ∈ S, ∀ y ∈ S,
      |x (Fin.last n) - y (Fin.last n)| ≤ (1 / 2 : ℝ) * ‖x - y‖) :
    ∃ f : EuclideanSpace ℝ (Fin n) → ℝ,
      LipschitzWith 1 f ∧ S ⊆ range (graphMapN f) := by
  apply exists_lipschitz_graph_of_projection_bound S
  intro x hx y hy
  have hb := hS x hx y hy
  have heq := norm_sq_graphProjectionN (x - y)
  rw [map_sub] at heq
  change ‖x - y‖ ^ 2 = ‖graphProjectionN n x - graphProjectionN n y‖ ^ 2 +
    (x (Fin.last n) - y (Fin.last n)) ^ 2 at heq
  simp only [NNReal.coe_one, one_mul]
  have habs := sq_abs (x (Fin.last n) - y (Fin.last n))
  nlinarith [norm_nonneg (x - y), norm_nonneg (graphProjectionN n x - graphProjectionN n y),
    abs_nonneg (x (Fin.last n) - y (Fin.last n))]

/-- The graph-containment conclusion is invariant under orthogonal changes of frame. -/
theorem exists_rotated_lipschitz_graph_of_half_cone {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin (n + 1))))
    {ν : EuclideanSpace ℝ (Fin (n + 1))} (hν : ‖ν‖ = 1)
    (hS : ∀ x ∈ S, ∀ y ∈ S, |inner ℝ ν (x - y)| ≤ (1 / 2 : ℝ) * ‖x - y‖) :
    ∃ (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
      (f : EuclideanSpace ℝ (Fin n) → ℝ),
      e (EuclideanSpace.single (Fin.last n) 1) = ν ∧ LipschitzWith 1 f ∧
      S ⊆ range (fun p => e (graphMapN f p)) := by
  obtain ⟨e, he⟩ := exists_line_direction_frame hν
  have hc : ∀ x ∈ e ⁻¹' S, ∀ y ∈ e ⁻¹' S,
      |x (Fin.last n) - y (Fin.last n)| ≤ (1 / 2 : ℝ) * ‖x - y‖ := by
    intro x hx y hy
    have h := hS (e x) hx (e y) hy
    rw [← map_sub, inner_frame_eq_last e he, e.norm_map] at h
    exact h
  obtain ⟨f, hf, hcover⟩ := exists_lipschitz_graph_of_half_cone (e ⁻¹' S) hc
  refine ⟨e, f, he, hf, ?_⟩
  intro x hx
  have hpre : e.symm x ∈ e ⁻¹' S := by simpa only [mem_preimage, e.apply_symm_apply] using hx
  obtain ⟨p, hp⟩ := hcover hpre
  refine ⟨p, ?_⟩
  change e (graphMapN f p) = x
  rw [hp, e.apply_symm_apply]

/-- Uniform cone control supplies a global Lipschitz parametrization containing the set. -/
theorem exists_lipschitz_param_of_half_cone {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin (n + 1))))
    {ν : EuclideanSpace ℝ (Fin (n + 1))} (hν : ‖ν‖ = 1)
    (hS : ∀ x ∈ S, ∀ y ∈ S, |inner ℝ ν (x - y)| ≤ (1 / 2 : ℝ) * ‖x - y‖) :
    ∃ f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + 1)),
      LipschitzWith 2 f ∧ S ⊆ range f := by
  obtain ⟨e, g, he, hg, hc⟩ := exists_rotated_lipschitz_graph_of_half_cone S hν hS
  refine ⟨fun p => e (graphMapN g p), ?_, hc⟩
  apply LipschitzWith.of_dist_le_mul
  intro p q
  change dist (e (graphMapN g p)) (e (graphMapN g q)) ≤ (2 : ℝ≥0) * dist p q
  rw [e.dist_map]
  have hb := (lipschitzWith_graphMapN hg).dist_le_mul p q
  norm_num only [NNReal.coe_add, NNReal.coe_one] at hb
  exact hb

end LiquidDrop
