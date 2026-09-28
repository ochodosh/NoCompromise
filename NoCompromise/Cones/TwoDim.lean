import NoCompromise.Regularity.OmegaMinimal
import NoCompromise.BV.OneDimensional

/-!
# Minimising cones in the plane

Blueprint `lem:cone-2d-link` (chapter 25), the structural part.

## Statement design (recorded as required by the task)

* Following `conv:representative` (chapter 21) the blueprint's set `C` is always taken to be its
  density-one representative, so the blueprint's `∂C` is rendered as `frontier (densityOne C)`
  and the link is `Γ = frontier (densityOne C) ∩ Metric.sphere 0 1`.
* The exact cone property is the project idiom of `Regularity/TangentCone.lean`, namely
  `∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne C = densityOne C`.  It is abstracted here as
  `LiquidDrop.IsDilationInvariant`.
* **Nontriviality is not assumed.**  The task suggested the hypothesis
  `(frontier (densityOne C)).Nonempty`.  None of the statements proved in this file needs it:
  the ray identity and the dilation invariance of the frontier are unconditional, and the
  degenerate case `Γ = ∅` has `Even (0 : ℕ)` anyway.  Dropping the hypothesis is a
  strengthening, not a weakening.  (Note also that `(frontier (densityOne C)).Nonempty` is a
  *strictly weaker* reading of "nontrivial" than `0 < volume C ∧ 0 < volume Cᶜ`, since it is
  satisfied by `frontier (densityOne C) = {0}`; nothing below depends on the difference.)

## What is proved here

The purely set-theoretic / topological consequences of exact dilation invariance, in every
dimension, and their specialisations to the plane:

* `IsDilationInvariant.frontier` : the frontier of a dilation-invariant set is dilation invariant;
* `IsDilationInvariant.diff_singleton_zero_eq` : a dilation-invariant set minus the origin is
  exactly the union of the open rays through its link;
* `cone2d_frontier_eq_rays` : the punctured boundary of a planar minimising cone is exactly the
  union of the rays through `Γ`;
* `cone2d_densityOne_eq_rays`, `cone2d_zero_mem_frontier`, `cone2d_link_frontier_eq`.

The remaining clauses of `lem:cone-2d-link` (finiteness of `Γ` and `Even Γ.ncard`), which require
the BV argument through `lem:bilip-chain`/`lem:bv-slices`, are **not** proved here.
-/

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace LiquidDrop

/-- Exact invariance under every positive dilation: the "cone" property in the form supplied by
`IsLocallyPerimeterMinimizing.tangent_is_cone` for the density-one representative. -/
def IsDilationInvariant {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ r : ℝ, 0 < r → (fun y => r • y) '' S = S

/-- The link of a set: its intersection with the unit sphere centred at the origin. -/
def link {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  S ∩ Metric.sphere 0 1

/-- The union of the open rays through a subset `Γ` of the unit sphere. -/
def rayUnion {n : ℕ} (Γ : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | x ≠ 0 ∧ ‖x‖⁻¹ • x ∈ Γ}

variable {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}

lemma mem_link_iff {x : EuclideanSpace ℝ (Fin n)} : x ∈ link S ↔ x ∈ S ∧ ‖x‖ = 1 := by
  simp [link]

lemma mem_rayUnion_iff {Γ : Set (EuclideanSpace ℝ (Fin n))} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ rayUnion Γ ↔ x ≠ 0 ∧ ‖x‖⁻¹ • x ∈ Γ := Iff.rfl

/-- Dilation invariance is closed under the action it describes. -/
lemma IsDilationInvariant.smul_mem (hS : IsDilationInvariant S) {r : ℝ} (hr : 0 < r)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S) : r • x ∈ S := by
  rw [← hS r hr]
  exact ⟨x, hx, rfl⟩

lemma IsDilationInvariant.mem_of_smul_mem (hS : IsDilationInvariant S) {r : ℝ} (hr : 0 < r)
    {x : EuclideanSpace ℝ (Fin n)} (hx : r • x ∈ S) : x ∈ S := by
  have := hS.smul_mem (inv_pos.mpr hr) hx
  rwa [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] at this

lemma IsDilationInvariant.smul_mem_iff (hS : IsDilationInvariant S) {r : ℝ} (hr : 0 < r)
    {x : EuclideanSpace ℝ (Fin n)} : r • x ∈ S ↔ x ∈ S :=
  ⟨hS.mem_of_smul_mem hr, hS.smul_mem hr⟩

/-- The frontier of a dilation-invariant set is dilation invariant: dilation is a
homeomorphism, so it carries frontiers to frontiers. -/
protected lemma IsDilationInvariant.frontier (hS : IsDilationInvariant S) :
    IsDilationInvariant (frontier S) := by
  intro r hr
  have h := (Homeomorph.smulOfNeZero r hr.ne').image_frontier S
  simp only [Homeomorph.smulOfNeZero_apply] at h
  rw [show (fun y : EuclideanSpace ℝ (Fin n) => r • y) = (r • ·) from rfl, h, hS r hr]

/-- The interior of a dilation-invariant set is dilation invariant. -/
protected lemma IsDilationInvariant.interior (hS : IsDilationInvariant S) :
    IsDilationInvariant (interior S) := by
  intro r hr
  have h := (Homeomorph.smulOfNeZero r hr.ne').image_interior S
  simp only [Homeomorph.smulOfNeZero_apply] at h
  rw [show (fun y : EuclideanSpace ℝ (Fin n) => r • y) = (r • ·) from rfl, h, hS r hr]

/-- The closure of a dilation-invariant set is dilation invariant. -/
protected lemma IsDilationInvariant.closure (hS : IsDilationInvariant S) :
    IsDilationInvariant (closure S) := by
  intro r hr
  have h := (Homeomorph.smulOfNeZero r hr.ne').image_closure S
  simp only [Homeomorph.smulOfNeZero_apply] at h
  rw [show (fun y : EuclideanSpace ℝ (Fin n) => r • y) = (r • ·) from rfl, h, hS r hr]

/-- **The cone-over-the-link identity.**  A dilation-invariant set, with the origin removed, is
exactly the union of the open rays through the points of its link. -/
theorem IsDilationInvariant.diff_singleton_zero_eq (hS : IsDilationInvariant S) :
    S \ {0} = rayUnion (link S) := by
  ext x
  constructor
  · rintro ⟨hxS, hx0⟩
    have hx0' : x ≠ 0 := by simpa using hx0
    have hn : (0 : ℝ) < ‖x‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hx0')
    refine ⟨hx0', ?_⟩
    refine mem_link_iff.mpr ⟨hS.smul_mem hn hxS, ?_⟩
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0')]
  · rintro ⟨hx0, hmem⟩
    refine ⟨?_, by simpa using hx0⟩
    have hn : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
    have := hS.smul_mem hn (mem_link_iff.mp hmem).1
    rwa [smul_smul, mul_inv_cancel₀ hn.ne', one_smul] at this

/-- The link only sees a set away from the origin. -/
lemma link_diff_singleton_zero : link (S \ {0}) = link S := by
  ext x
  simp only [mem_link_iff, Set.mem_sdiff, mem_singleton_iff, and_assoc]
  constructor
  · rintro ⟨hx, -, hn⟩; exact ⟨hx, hn⟩
  · rintro ⟨hx, hn⟩
    exact ⟨hx, by rintro rfl; simp at hn, hn⟩

/-- A nonempty dilation-invariant *closed* set contains the origin: dilating a point of the set
towards the origin stays inside it. -/
lemma IsDilationInvariant.zero_mem_of_isClosed (hS : IsDilationInvariant S) (hc : IsClosed S)
    (hne : S.Nonempty) : (0 : EuclideanSpace ℝ (Fin n)) ∈ S := by
  obtain ⟨x, hx⟩ := hne
  have hmem : ∀ m : ℕ, ((m : ℝ) + 1)⁻¹ • x ∈ S := fun m =>
    hS.smul_mem (by positivity) hx
  have htend : Filter.Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹ • x) atTop (𝓝 ((0 : ℝ) • x)) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat.congr
      (fun m => one_div _)).smul_const x
  rw [zero_smul] at htend
  exact hc.mem_of_tendsto htend (Filter.Eventually.of_forall hmem)

/-! ## The planar case -/

variable {C : Set (EuclideanSpace ℝ (Fin 2))}

/-- The frontier of the density-one representative of a planar cone is dilation invariant. -/
theorem cone2d_isDilationInvariant_frontier
    (hcone : ∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne C = densityOne C) :
    IsDilationInvariant (frontier (densityOne C)) :=
  IsDilationInvariant.frontier hcone

/-- The density-one representative of a planar cone, punctured at the origin, is exactly the
union of the open rays through its link. -/
theorem cone2d_densityOne_eq_rays
    (hcone : ∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne C = densityOne C) :
    densityOne C \ {0} =
      {x | x ≠ 0 ∧ ‖x‖⁻¹ • x ∈ densityOne C ∩ Metric.sphere 0 1} :=
  IsDilationInvariant.diff_singleton_zero_eq hcone

/-- **Blueprint `lem:cone-2d-link`, ray clause.**  For a locally perimeter-minimising cone `C` in
the plane, the punctured boundary `∂C ∖ {0}` is exactly the union of the open rays through the
link `Γ = ∂C ∩ S¹`. -/
theorem cone2d_frontier_eq_rays
    (hcone : ∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne C = densityOne C) :
    frontier (densityOne C) \ {0} =
      {x | x ≠ 0 ∧ ‖x‖⁻¹ • x ∈ frontier (densityOne C) ∩ Metric.sphere 0 1} :=
  IsDilationInvariant.diff_singleton_zero_eq (IsDilationInvariant.frontier hcone)

/-- A nontrivial planar cone has the origin on its boundary. -/
theorem cone2d_zero_mem_frontier
    (hcone : ∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne C = densityOne C)
    (hnt : (frontier (densityOne C)).Nonempty) :
    (0 : EuclideanSpace ℝ (Fin 2)) ∈ frontier (densityOne C) :=
  IsDilationInvariant.zero_mem_of_isClosed (IsDilationInvariant.frontier hcone)
    isClosed_frontier hnt

/-- The link is unchanged by puncturing the boundary at the origin. -/
theorem cone2d_link_frontier_eq :
    (frontier (densityOne C) \ {0}) ∩ Metric.sphere 0 1 =
      frontier (densityOne C) ∩ Metric.sphere 0 1 :=
  link_diff_singleton_zero

end LiquidDrop
