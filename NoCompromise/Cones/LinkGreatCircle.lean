import NoCompromise.Cones.GreatCircle
import NoCompromise.Cones.Classification

/-!
# The link of a three-dimensional minimising cone is one great circle, from its Euler equation

Assembly of the last paragraph of blueprint `lem:cone-link-great-circle` and of `thm:cone-3d`
(chapter 25), with the analytic input stated as explicit hypotheses:

* the link `Γ = ∂C ∩ S²` is the union of a nonempty family of pairwise disjoint components;
* each component is the image of a unit-speed curve on `S²` solving the Euler equation
  `γ'' = -γ` (the blueprint's "its acceleration in `ℝ³` is normal to the sphere, so `γ'' = -γ`").

That the link of a nontrivial minimising cone admits such a description is the smoothness
statement `lem:cone-smooth` together with the first-variation computation of
`lem:cone-link-great-circle`; neither is asserted here.

* `inner_eq_zero_of_norm_eq_one` : a curve on the unit sphere is orthogonal to its velocity;
* `iUnion_range_eq_greatCircle` : such a family of pairwise disjoint components is one great circle
  ("two distinct great circles intersect, whereas distinct components of the embedded link are
  disjoint");
* `cone3d_halfspace_of_link_components` : `thm:cone-3d` from this description of the link.
-/

noncomputable section
open Set Metric

namespace LiquidDrop

/-- A differentiable curve on the unit sphere is orthogonal to its velocity. -/
theorem inner_eq_zero_of_norm_eq_one {γ γ' : ℝ → AmbientSpace}
    (hγ : ∀ t, HasDerivAt γ (γ' t) t) (hn : ∀ t, ‖γ t‖ = 1) (t : ℝ) :
    inner ℝ (γ t) (γ' t) = 0 := by
  have hd := (hγ t).inner ℝ (hγ t)
  have hc : (fun s => inner ℝ (γ s) (γ s)) = fun _ => (1 : ℝ) := by
    funext s
    rw [real_inner_self_eq_norm_sq, hn s, one_pow]
  rw [hc] at hd
  have h0 := hd.unique (hasDerivAt_const t (1 : ℝ))
  rw [real_inner_comm (γ t) (γ' t)] at h0
  linarith

/-- **Last paragraph of `lem:cone-link-great-circle`.**  A nonempty family of pairwise disjoint
images of unit-speed curves on `S²` solving `γ'' = -γ` has exactly one member, and its union is a
great circle. -/
theorem iUnion_range_eq_greatCircle {ι : Type*} [Nonempty ι] (γ γ' : ι → ℝ → AmbientSpace)
    (hγ : ∀ i t, HasDerivAt (γ i) (γ' i t) t) (hγ' : ∀ i t, HasDerivAt (γ' i) (-γ i t) t)
    (hn : ∀ i t, ‖γ i t‖ = 1) (hs : ∀ i t, ‖γ' i t‖ = 1)
    (hdisj : Pairwise fun i j => Disjoint (range (γ i)) (range (γ j))) :
    ∃ ν : AmbientSpace, ν ≠ 0 ∧ (⋃ i, range (γ i)) = {x | inner ℝ ν x = 0} ∩ sphere 0 1 := by
  have hcirc : ∀ i, ∃ ν : AmbientSpace, ν ≠ 0 ∧
      range (γ i) = {x | inner ℝ ν x = 0} ∩ sphere 0 1 := fun i =>
    range_eq_greatCircle_of_hasDerivAt_neg (hγ i) (hγ' i) (hn i 0) (hs i 0)
      (inner_eq_zero_of_norm_eq_one (hγ i) (hn i) 0)
  choose ν hν hrange using hcirc
  have hsub : Subsingleton ι := by
    refine subsingleton_of_pairwise_disjoint_greatCircles ν ?_
    intro i j hij
    rw [← hrange i, ← hrange j]
    exact hdisj hij
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨ν i₀, hν i₀, ?_⟩
  have hU : (⋃ i, range (γ i)) = range (γ i₀) := by
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      rwa [Subsingleton.elim i i₀] at hi
    · exact fun hx => ⟨i₀, hx⟩
  rw [hU, hrange i₀]

/-- **`thm:cone-3d` from the Euler equation of the link.**  If the link of a nontrivial locally
perimeter-minimising cone in `ℝ³` is the union of a nonempty family of pairwise disjoint images of
unit-speed curves on `S²` solving `γ'' = -γ`, then the density-one representative is an open
halfspace. -/
theorem cone3d_halfspace_of_link_components {C : Set AmbientSpace}
    (hC : IsNontrivialMinimizingCone C) {ι : Type*} [Nonempty ι]
    (γ γ' : ι → ℝ → AmbientSpace)
    (hγ : ∀ i t, HasDerivAt (γ i) (γ' i t) t) (hγ' : ∀ i t, HasDerivAt (γ' i) (-γ i t) t)
    (hn : ∀ i t, ‖γ i t‖ = 1) (hs : ∀ i t, ‖γ' i t‖ = 1)
    (hdisj : Pairwise fun i j => Disjoint (range (γ i)) (range (γ j)))
    (hlink : frontier (densityOne C) ∩ sphere 0 1 = ⋃ i, range (γ i)) :
    ∃ μ : AmbientSpace, ‖μ‖ = 1 ∧ densityOne C = {x | 0 < inner ℝ μ x} := by
  obtain ⟨ν, hν, hU⟩ := iUnion_range_eq_greatCircle γ γ' hγ hγ' hn hs hdisj
  exact cone3d_halfspace_of_link_eq hC hν (hlink.trans hU)

end LiquidDrop
