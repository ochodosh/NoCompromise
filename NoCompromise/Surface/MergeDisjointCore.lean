module

public import NoCompromise.Surface.LevelFlow
public import NoCompromise.Surface.SaddleChart
public import NoCompromise.Topology.OrbitEnds

@[expose] public section

/-!
# `lem:merge-disjoint`, core argument

The orbit of the rotated gradient through a point of the ray `r₁` of a saddle `p` has two ends,
both at `p`, along two distinct rays; `lem:level-adjacency` makes the adjacent lower and upper
components constant along it, and the flanking relations of `lem:local-sectors` (iii) give the
three cases. Here the two analytic inputs (height is constant along the orbit; the level set is
locally one orbit) are hypotheses `h_const` and `h_arc`.
-/

noncomputable section

open Set Filter Topology

namespace LiquidDrop

local notation "E2" => EuclideanSpace ℝ (Fin 2)

variable {S : Set E₃}

/-- Points in two of the four model rays determine the same ray. -/
theorem morse_ray_eq_of_mem {ρ : ℝ} {R R' : Set E2}
    (hR : R = morseRay1 ρ ∨ R = morseRay2 ρ ∨ R = morseRay3 ρ ∨ R = morseRay4 ρ)
    (hR' : R' = morseRay1 ρ ∨ R' = morseRay2 ρ ∨ R' = morseRay3 ρ ∨ R' = morseRay4 ρ)
    {z : E2} (hz : z ∈ R) (hz' : z ∈ R') : R = R' := by
  obtain ⟨h12, h13, h14, h23, h24, h34⟩ := morse_rays_disjoint ρ
  rcases hR with rfl | rfl | rfl | rfl <;> rcases hR' with rfl | rfl | rfl | rfl <;>
    first
    | rfl
    | exact absurd hz' (Set.disjoint_left.mp h12 hz)
    | exact absurd hz (Set.disjoint_left.mp h12 hz')
    | exact absurd hz' (Set.disjoint_left.mp h13 hz)
    | exact absurd hz (Set.disjoint_left.mp h13 hz')
    | exact absurd hz' (Set.disjoint_left.mp h14 hz)
    | exact absurd hz (Set.disjoint_left.mp h14 hz')
    | exact absurd hz' (Set.disjoint_left.mp h23 hz)
    | exact absurd hz (Set.disjoint_left.mp h23 hz')
    | exact absurd hz' (Set.disjoint_left.mp h24 hz)
    | exact absurd hz (Set.disjoint_left.mp h24 hz')
    | exact absurd hz' (Set.disjoint_left.mp h34 hz)
    | exact absurd hz (Set.disjoint_left.mp h34 hz')

/-- A preconnected piece of a curve inside the four rays lies in one ray. -/
theorem exists_ray_of_isPreconnected {ρ : ℝ} {β : ℝ → E2} {I : Set ℝ} (hI : IsPreconnected I)
    (hc : ContinuousOn β I)
    (hsub : ∀ t ∈ I, β t ∈ morseRay1 ρ ∪ morseRay2 ρ ∪ morseRay3 ρ ∪ morseRay4 ρ) :
    ∃ R : Set E2, (R = morseRay1 ρ ∨ R = morseRay2 ρ ∨ R = morseRay3 ρ ∨ R = morseRay4 ρ) ∧
      ∀ t ∈ I, β t ∈ R := by
  have hC : IsPreconnected (β '' I) := hI.image β hc
  have hs : β '' I ⊆ morseRay1 ρ ∪ morseRay2 ρ ∪ morseRay3 ρ ∪ morseRay4 ρ := by
    rintro _ ⟨t, ht, rfl⟩; exact hsub t ht
  rcases subset_ray_of_isPreconnected hC hs with h | h | h | h
  · exact ⟨_, Or.inl rfl, fun t ht => h ⟨t, ht, rfl⟩⟩
  · exact ⟨_, Or.inr (Or.inl rfl), fun t ht => h ⟨t, ht, rfl⟩⟩
  · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), fun t ht => h ⟨t, ht, rfl⟩⟩
  · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), fun t ht => h ⟨t, ht, rfl⟩⟩

end LiquidDrop
