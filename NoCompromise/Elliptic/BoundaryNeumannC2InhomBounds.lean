import NoCompromise.Elliptic.NondivSchauderNorm
import NoCompromise.Elliptic.BoundaryNeumannInhomC1Conormal

/-!
# Compact Hölder bounds for smooth inhomogeneous Neumann data

These lemmas use ambient derivatives on an open neighborhood of a compact
convex set. In particular, they apply to closed balls and closed half balls.
-/

noncomputable section
open Set Metric InnerProductSpace
open scoped Topology Gradient
namespace LiquidDrop

/-- C¹ data on a neighborhood of a compact convex set have a common uniform
bound and an α-Hölder bound for every `0 ≤ α ≤ 1`. -/
theorem boundary_neumann_c2_inhom_compact_bounds
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {g : E → F} {K O : Set E} (hK : IsCompact K) (hcK : Convex ℝ K)
    (hO : IsOpen O) (hKO : K ⊆ O) (hg : ContDiffOn ℝ 1 g O) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ x ∈ K, ‖g x‖ ≤ B) ∧
      ∀ x ∈ K, ∀ y ∈ K, ‖g x - g y‖ ≤ B * dist x y ^ α := by
  have hD := (hg.fderiv_of_isOpen hO (by norm_num :
    (0 : WithTop ℕ∞) + 1 ≤ 1)).continuousOn
  obtain ⟨B, hB, hb⟩ :=
    (hK.image_of_continuousOn (hg.continuousOn.mono hKO)).isBounded.exists_pos_norm_le
  obtain ⟨L, hL, hl⟩ :=
    (hK.image_of_continuousOn (hD.mono hKO)).isBounded.exists_pos_norm_le
  obtain ⟨R, hR, hr⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨B + L * (2 * R + 1), by positivity,
    fun x hx => (hb _ (mem_image_of_mem _ hx)).trans
      (le_add_of_nonneg_right (by positivity)), ?_⟩
  intro x hx y hy
  have hd : dist x y ≤ 2 * R := by
    rw [dist_eq_norm]
    exact (norm_sub_le x y).trans (by linarith [hr x hx, hr y hy])
  have hp : dist x y ≤ (2 * R + 1) * dist x y ^ α := by
    by_cases hd1 : dist x y ≤ 1
    · have he := Real.self_le_rpow_of_le_one (dist_nonneg (x := x) (y := y)) hd1 hα1
      nlinarith [Real.rpow_nonneg (dist_nonneg (x := x) (y := y)) α]
    · have he := Real.one_le_rpow (le_of_not_ge hd1) hα
      nlinarith
  calc
    _ ≤ L * dist x y := by
      simpa only [dist_eq_norm] using hcK.norm_image_sub_le_of_norm_fderiv_le
        (fun z hz => (hg.contDiffAt (hO.mem_nhds (hKO hz))).differentiableAt (by norm_num))
        (fun z hz => hl _ (mem_image_of_mem _ hz)) hy hx
    _ ≤ L * ((2 * R + 1) * dist x y ^ α) := mul_le_mul_of_nonneg_left hp hL.le
    _ ≤ _ := by nlinarith [Real.rpow_nonneg (dist_nonneg (x := x) (y := y)) α]

/-- The compact C¹ bounds give finiteness of the project's actual Hölder norm. -/
theorem boundary_neumann_c2_inhom_finiteHolder_of_contDiffOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {g : E → F} {K O : Set E} (hK : IsCompact K) (hcK : Convex ℝ K)
    (hO : IsOpen O) (hKO : K ⊆ O) (hg : ContDiffOn ℝ 1 g O) :
    HasFiniteHolderNormOn α g K := by
  obtain ⟨B, hB, hb, hh⟩ := boundary_neumann_c2_inhom_compact_bounds
    hα hα1 hK hcK hO hKO hg
  refine HasFiniteHolderNormOn.of_bounds hB hB hb ?_
  intro x hx y hy
  by_cases he : x = y
  · subst y
    simpa only [sub_self, norm_zero, zero_div] using hB
  · apply (div_le_iff₀ (Real.rpow_pos_of_pos
      (norm_pos_iff.mpr (sub_ne_zero.mpr he)) α)).mpr
    simpa only [dist_eq_norm] using hh x hx y hy

/-- Smooth data have genuine C¹,α regularity on each compact convex subset of
their open domain, with no quantitative bounds added as assumptions. -/
theorem hasC1HolderOn_of_contDiffOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {g : E → F} {K O : Set E} (hK : IsCompact K) (hcK : Convex ℝ K)
    (hO : IsOpen O) (hKO : K ⊆ O) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g O) :
    HasC1HolderOn α g K := by
  have hg1 : ContDiffOn ℝ 1 g O := hg.of_le (by simp)
  have hD : ContDiffOn ℝ 1 (fderiv ℝ g) O :=
    hg.fderiv_of_isOpen hO (by simp)
  exact ⟨hg1.mono hKO,
    boundary_neumann_c2_inhom_finiteHolder_of_contDiffOn hα hα1 hK hcK hO hKO hg1,
    boundary_neumann_c2_inhom_finiteHolder_of_contDiffOn hα hα1 hK hcK hO hKO hD⟩

end LiquidDrop
