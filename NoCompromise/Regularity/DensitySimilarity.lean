module

public import NoCompromise.Regularity.TangentRepresentative

@[expose] public section

/-!
# Exact density representatives under positive similarities

All identities hold for arbitrary sets: the volume-ratio calculation requires
no measurability assumption. The boundary identities concern the actual
density-one representative, not a choice up to null sets.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

/-- Density ratios are unchanged by simultaneous translation and positive dilation. -/
theorem densityRatio_image_similarity (E : Set AmbientSpace) (x y : AmbientSpace)
    {r : ℝ} (hr : 0 < r) (s : ℝ) :
    densityRatio ((fun z => x + r • z) '' E) (x + r • y) (r * s) = densityRatio E y s := by
  let e := blowupHomeomorph x hr
  change densityRatio (e '' E) (x + r • y) (r * s) = _
  rw [densityRatio, ← image_ball_blowupHomeomorph x y hr s,
    ← image_inter e.injective, volume_image_blowupHomeomorph, volume_image_blowupHomeomorph]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le 3)]
  dsimp [densityRatio]
  field_simp [hr.ne']

/-- Exact density-ratio covariance for a blowup with arbitrary center. -/
theorem densityRatio_blowupSet (E : Set AmbientSpace) (x y : AmbientSpace)
    {r : ℝ} (hr : 0 < r) (s : ℝ) :
    densityRatio (blowupSet E x r) y s = densityRatio E (x + r • y) (r * s) := by
  have ht := densityRatio_image_similarity (blowupSet E x r) x y hr s
  rw [image_blowupSet E x hr] at ht
  exact ht.symm

/-- Membership in the canonical density-one representative commutes with blowup. -/
theorem mem_densityOne_blowupSet (E : Set AmbientSpace) (x y : AmbientSpace)
    {r : ℝ} (hr : 0 < r) :
    y ∈ densityOne (blowupSet E x r) ↔ x + r • y ∈ densityOne E := by
  change Tendsto (densityRatio (blowupSet E x r) y) (𝓝[>] (0 : ℝ)) (𝓝 1) ↔
    Tendsto (densityRatio E (x + r • y)) (𝓝[>] (0 : ℝ)) (𝓝 1)
  constructor
  · intro h
    have ht := h.comp (tangent_pos_mul_tendsto_zero (inv_pos.mpr hr))
    simpa only [Function.comp_def, densityRatio_blowupSet E x y hr,
      ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] using ht
  · intro h
    have ht := h.comp (tangent_pos_mul_tendsto_zero hr)
    simpa only [Function.comp_def, ← densityRatio_blowupSet E x y hr] using ht

/-- Exact preimage covariance of the density-one set. -/
theorem densityOne_blowupSet (E : Set AmbientSpace) (x : AmbientSpace)
    {r : ℝ} (hr : 0 < r) :
    densityOne (blowupSet E x r) = (fun y => x + r • y) ⁻¹' densityOne E := by
  ext y
  exact mem_densityOne_blowupSet E x y hr

/-- The equivalent exact image formula in blowup coordinates. -/
theorem densityOne_blowupSet_image (E : Set AmbientSpace) (x : AmbientSpace)
    {r : ℝ} (hr : 0 < r) :
    densityOne (blowupSet E x r) = (fun y => r⁻¹ • (y - x)) '' densityOne E := by
  rw [densityOne_blowupSet E x hr]
  rw [← show ⇑(blowupHomeomorph x hr).symm = (fun y => r⁻¹ • (y - x)) from
    funext (blowupHomeomorph_symm_apply x · hr)]
  exact ((blowupHomeomorph x hr).toEquiv.image_symm_eq_preimage (densityOne E)).symm

/-- The actual topological frontier has exact positive-blowup covariance. -/
theorem frontier_densityOne_blowupSet (E : Set AmbientSpace) (x : AmbientSpace)
    {r : ℝ} (hr : 0 < r) :
    frontier (densityOne (blowupSet E x r)) =
      (fun y => r⁻¹ • (y - x)) '' frontier (densityOne E) := by
  rw [densityOne_blowupSet_image E x hr]
  rw [← show ⇑(blowupHomeomorph x hr).symm = (fun y => r⁻¹ • (y - x)) from
    funext (blowupHomeomorph_symm_apply x · hr)]
  exact (blowupHomeomorph x hr).symm.image_frontier (densityOne E) |>.symm

/-- Boundary membership in the forward-coordinate convention. -/
theorem mem_frontier_densityOne_blowupSet (E : Set AmbientSpace) (x y : AmbientSpace)
    {r : ℝ} (hr : 0 < r) :
    y ∈ frontier (densityOne (blowupSet E x r)) ↔
      x + r • y ∈ frontier (densityOne E) := by
  rw [frontier_densityOne_blowupSet E x hr]
  rw [← show ⇑(blowupHomeomorph x hr).symm = (fun y => r⁻¹ • (y - x)) from
    funext (blowupHomeomorph_symm_apply x · hr)]
  change y ∈ (blowupHomeomorph x hr).symm '' frontier (densityOne E) ↔
    blowupHomeomorph x hr y ∈ frontier (densityOne E)
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa only [Homeomorph.apply_symm_apply] using hz
  · intro hy
    exact ⟨blowupHomeomorph x hr y, hy, (blowupHomeomorph x hr).symm_apply_apply y⟩

/-- Boundary membership in the inverse-coordinate convention. -/
theorem inverse_mem_frontier_densityOne_blowupSet (E : Set AmbientSpace)
    (x y : AmbientSpace) {r : ℝ} (hr : 0 < r) :
    r⁻¹ • (y - x) ∈ frontier (densityOne (blowupSet E x r)) ↔
      y ∈ frontier (densityOne E) := by
  simpa [smul_smul, hr.ne'] using
    mem_frontier_densityOne_blowupSet E x (r⁻¹ • (y - x)) hr

end LiquidDrop
