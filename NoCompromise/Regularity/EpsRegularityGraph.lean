module

public import NoCompromise.Regularity.SlabCap
public import NoCompromise.BV.CoareaCoordinates

@[expose] public section

/-!
# The boundary is one Lipschitz graph in the quarter cylinder

Blueprint `thm:eps-regularity`, Step 3, the set-theoretic conclusion. Suppose a
set `S` (in the application, the topological boundary of the density-one
representative) satisfies the two-point cone estimate in the quarter cylinder
and meets every vertical line over the half disk at a height below `r / 8`.
Then `S ∩ C_{r/4}` is exactly the graph of a `1`-Lipschitz height function over
the base disk of radius `r / 4`. No exceptional-slice assumption is made: the
graph is the whole of `S` in the cylinder.
-/

noncomputable section
open Set Metric
namespace LiquidDrop

/-- Blueprint `thm:eps-regularity`, Step 3: a cone estimate and vertical
crossings make `S ∩ C_{r/4}` the graph of a `1`-Lipschitz function. -/
theorem boundary_graph_of_cone_crossing {S : Set AmbientSpace} {r : ℝ} (hr : 0 < r)
    (hcone : ∀ p ∈ S ∩ standardCylinder (r / 4), ∀ q ∈ S ∩ standardCylinder (r / 4),
      |q 2 - p 2| ≤ ‖graphProjectionN 2 q - graphProjectionN 2 p‖)
    (hcross : ∀ x' : EuclideanSpace ℝ (Fin 2), ‖x'‖ < r / 2 →
      ∃ t : ℝ, |t| < r / 8 ∧ graphAppendN x' t ∈ S) :
    ∃ f : EuclideanSpace ℝ (Fin 2) → ℝ,
      (∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (r / 4), |f x'| < r / 8) ∧
      (∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (r / 4),
        ∀ y' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (r / 4), |f x' - f y'| ≤ ‖x' - y'‖) ∧
      S ∩ standardCylinder (r / 4) =
        (fun x' => graphAppendN x' (f x')) '' ball (0 : EuclideanSpace ℝ (Fin 2)) (r / 4) := by
  classical
  let f : EuclideanSpace ℝ (Fin 2) → ℝ := fun x' =>
    if h : ‖x'‖ < r / 2 then Classical.choose (hcross x' h) else 0
  have hlast : ∀ (x' : EuclideanSpace ℝ (Fin 2)) (t : ℝ), graphAppendN x' t 2 = t :=
    fun x' t => graphAppendN_last x' t
  have hf : ∀ x' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (r / 4),
      |f x'| < r / 8 ∧ graphAppendN x' (f x') ∈ S ∩ standardCylinder (r / 4) := by
    intro x' hx'
    have hn : ‖x'‖ < r / 4 := by simpa using hx'
    have h2 : ‖x'‖ < r / 2 := by linarith
    have hfx : f x' = Classical.choose (hcross x' h2) := by simp only [f, dif_pos h2]
    obtain ⟨ht, hS⟩ := Classical.choose_spec (hcross x' h2)
    rw [← hfx] at ht hS
    refine ⟨ht, hS, ?_, ?_⟩
    · simpa only [graphProjectionN_append] using hn
    · rw [hlast]; linarith
  refine ⟨f, fun x' hx' => (hf x' hx').1, ?_, ?_⟩
  · intro x' hx' y' hy'
    have h := hcone _ (hf y' hy').2 _ (hf x' hx').2
    simpa only [hlast, graphProjectionN_append] using h
  · ext q
    constructor
    · intro hq
      have hpq : graphProjectionN 2 q ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (r / 4) := by
        simpa using hq.2.1
      refine ⟨graphProjectionN 2 q, hpq, ?_⟩
      have h := hcone _ (hf _ hpq).2 q hq
      simp only [hlast, graphProjectionN_append, sub_self, norm_zero] at h
      have heq : q 2 = f (graphProjectionN 2 q) := by
        have := abs_nonneg (q 2 - f (graphProjectionN 2 q))
        have h0 : |q 2 - f (graphProjectionN 2 q)| = 0 := le_antisymm h this
        linarith [abs_eq_zero.mp h0]
      simp only
      rw [← heq]
      exact graphAppendN_projection q
    · rintro ⟨x', hx', rfl⟩
      exact (hf x' hx').2

end LiquidDrop
