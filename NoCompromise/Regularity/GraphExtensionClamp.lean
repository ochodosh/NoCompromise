module

public import NoCompromise.Regularity.GraphExtension

@[expose] public section

/-! # Height-preserving Lipschitz graph extension -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology
namespace LiquidDrop

theorem exists_clamped_lipschitz_graph_extension {S : Set AmbientSpace} {γ : ℝ≥0}
    (hS : ∀ p ∈ S, ∀ q ∈ S,
      |p 2 - q 2| ≤ γ * dist (graphProjectionN 2 p) (graphProjectionN 2 q))
    {τ : ℝ} (hτ : 0 ≤ τ) (hheight : ∀ p ∈ S, |p 2| ≤ τ) :
    ∃ f : EuclideanSpace ℝ (Fin 2) → ℝ, LipschitzWith γ f ∧
      (∀ x, |f x| ≤ τ) ∧ (∀ p ∈ S, f (graphProjectionN 2 p) = p 2) ∧
      S = (fun x => graphAppendN x (f x)) '' (graphProjectionN 2 '' S) := by
  obtain ⟨g, hg, hval, _⟩ := exists_lipschitz_graph_extension hS
  let f := fun x => min (max (g x) (-τ)) τ
  have hf : LipschitzWith γ f := (hg.max_const (-τ)).min_const τ
  have hbound (x) : |f x| ≤ τ := by
    apply abs_le.mpr
    exact ⟨le_min ((le_max_right _ _)) (by linarith), min_le_right _ _⟩
  have hfix (p : AmbientSpace) (hp : p ∈ S) : f (graphProjectionN 2 p) = p 2 := by
    dsimp [f]
    rw [hval p hp, max_eq_left (abs_le.mp (hheight p hp)).1,
      min_eq_left (abs_le.mp (hheight p hp)).2]
  refine ⟨f, hf, hbound, hfix, ?_⟩
  ext p
  constructor
  · intro hp
    exact ⟨graphProjectionN 2 p, mem_image_of_mem _ hp, by
      dsimp only
      rw [hfix p hp]; exact graphAppendN_projection p⟩
  · rintro ⟨x, ⟨q, hq, rfl⟩, rfl⟩
    dsimp only
    rw [hfix q hq]
    have hrec : graphAppendN (graphProjectionN 2 q) (q 2) = q := graphAppendN_projection q
    rw [hrec]
    exact hq

end LiquidDrop
