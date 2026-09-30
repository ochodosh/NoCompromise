module

public import NoCompromise.Regularity.GraphTwoPoint
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

/-! # Actual graph selection and Lipschitz extension from a two-point estimate -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology
namespace LiquidDrop

lemma graph_projection_injOn_of_height_bound {S : Set AmbientSpace} {γ : ℝ}
    (hS : ∀ p ∈ S, ∀ q ∈ S,
      |p 2 - q 2| ≤ γ * dist (graphProjectionN 2 p) (graphProjectionN 2 q)) :
    InjOn (graphProjectionN 2) S := by
  intro p hp q hq he
  have hh := hS p hp q hq
  rw [he, dist_self, mul_zero] at hh
  have hv : p 2 = q 2 := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))
  calc
    p = graphAppendN (graphProjectionN 2 p) (p 2) := (graphAppendN_projection p).symm
    _ = graphAppendN (graphProjectionN 2 q) (q 2) := by rw [he, hv]
    _ = q := graphAppendN_projection q

def graphFiberHeight (S : Set AmbientSpace) (x : EuclideanSpace ℝ (Fin 2)) : ℝ := by
  classical
  exact if h : ∃ p ∈ S, graphProjectionN 2 p = x then (Classical.choose h) 2 else 0

lemma graphFiberHeight_projection {S : Set AmbientSpace}
    (hi : InjOn (graphProjectionN 2) S) {p : AmbientSpace} (hp : p ∈ S) :
    graphFiberHeight S (graphProjectionN 2 p) = p 2 := by
  have hx : ∃ q ∈ S, graphProjectionN 2 q = graphProjectionN 2 p := ⟨p, hp, rfl⟩
  rw [graphFiberHeight, dite_eq_left hx]
  have he := hi (Classical.choose_spec hx).1 hp (Classical.choose_spec hx).2
  rw [he]

lemma lipschitzOnWith_graphFiberHeight {S : Set AmbientSpace} {γ : ℝ≥0}
    (hS : ∀ p ∈ S, ∀ q ∈ S,
      |p 2 - q 2| ≤ γ * dist (graphProjectionN 2 p) (graphProjectionN 2 q)) :
    LipschitzOnWith γ (graphFiberHeight S) (graphProjectionN 2 '' S) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  rintro x ⟨p, hp, rfl⟩ y ⟨q, hq, rfl⟩
  rw [graphFiberHeight_projection (graph_projection_injOn_of_height_bound hS) hp,
    graphFiberHeight_projection (graph_projection_injOn_of_height_bound hS) hq, Real.dist_eq]
  exact hS p hp q hq

theorem exists_lipschitz_graph_extension {S : Set AmbientSpace} {γ : ℝ≥0}
    (hS : ∀ p ∈ S, ∀ q ∈ S,
      |p 2 - q 2| ≤ γ * dist (graphProjectionN 2 p) (graphProjectionN 2 q)) :
    ∃ f : EuclideanSpace ℝ (Fin 2) → ℝ, LipschitzWith γ f ∧
      (∀ p ∈ S, f (graphProjectionN 2 p) = p 2) ∧
      S = (fun x => graphAppendN x (f x)) '' (graphProjectionN 2 '' S) := by
  obtain ⟨f, hf, he⟩ := (lipschitzOnWith_graphFiberHeight hS).extend_real
  have hval (p : AmbientSpace) (hp : p ∈ S) : f (graphProjectionN 2 p) = p 2 :=
    (he (mem_image_of_mem _ hp)).symm.trans
      (graphFiberHeight_projection (graph_projection_injOn_of_height_bound hS) hp)
  refine ⟨f, hf, hval, ?_⟩
  ext p
  constructor
  · intro hp
    exact ⟨graphProjectionN 2 p, mem_image_of_mem _ hp, by
      dsimp only
      rw [hval p hp]; exact graphAppendN_projection p⟩
  · rintro ⟨x, ⟨q, hq, rfl⟩, rfl⟩
    dsimp only
    rw [hval q hq]
    have hrec : graphAppendN (graphProjectionN 2 q) (q 2) = q := graphAppendN_projection q
    rw [hrec]
    exact hq

lemma measurableSet_projected_graph {S : Set AmbientSpace} {γ : ℝ}
    (hmS : MeasurableSet S)
    (hS : ∀ p ∈ S, ∀ q ∈ S,
      |p 2 - q 2| ≤ γ * dist (graphProjectionN 2 p) (graphProjectionN 2 q)) :
    MeasurableSet (graphProjectionN 2 '' S) :=
  hmS.image_of_continuousOn_injOn (graphProjectionN 2).continuous.continuousOn
    (graph_projection_injOn_of_height_bound hS)

end LiquidDrop
