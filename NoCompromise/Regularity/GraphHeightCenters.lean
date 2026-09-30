module

public import NoCompromise.Regularity.DensitySimilarity
public import NoCompromise.Regularity.HeightBound

@[expose] public section

/-!
# Quantitative height control at every boundary center

The threshold is uniform in the center, the set, its quasiminimality parameter,
and the radius. The proof uses exact covariance of the density-one frontier and
of the genuine cylindrical excess, together with actual scaled quasiminimality.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal Topology
namespace LiquidDrop

/-- The height bound at an arbitrary boundary center, with the original uniform threshold. -/
theorem height_bound_at_center {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω),
      ∀ p ∈ frontier (densityOne E), ∀ r : ℝ, 0 < r → r ≤ 1 →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable p r
        (EuclideanSpace.single 2 1) + ω * r ≤ ε →
      ∀ q ∈ frontier (densityOne E) ∩ cylinder p (3 * r / 4) (EuclideanSpace.single 2 1),
        |q 2 - p 2| < η * r := by
  obtain ⟨ε, hε, hb⟩ := height_bound hη
  refine ⟨ε, hε, fun E ω hE p hp r hr hr1 he q hq => ?_⟩
  have hB : IsOmegaMinimal (blowupSet E p r) (ω * r) := by
    apply IsOmegaMinimalAtScales.blowupSet hE p hr (by norm_num)
    simpa only [mul_one, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hr1
  have h0 : (0 : AmbientSpace) ∈ frontier (densityOne (blowupSet E p r)) := by
    apply (mem_frontier_densityOne_blowupSet E p 0 hr).mpr
    simpa only [smul_zero, add_zero] using hp
  have heB : cylindricalExcess (blowupSet E p r) hB.locallyFinite hB.nullMeasurable 0 1
      (EuclideanSpace.single 2 1) + (ω * r) * 1 ≤ ε := by
    simpa only [cylindricalExcess_blowupSet_unit E hE.locallyFinite hE.nullMeasurable p hr,
      mul_one] using he
  have hqB : r⁻¹ • (q - p) ∈ frontier (densityOne (blowupSet E p r)) ∩
      standardCylinder (3 / 4) := by
    refine ⟨(inverse_mem_frontier_densityOne_blowupSet E p q hr).mpr hq.1, ?_⟩
    rw [standardCylinder_eq_cylinder]
    apply (mem_cylinder_translate_pos_smul p 0 (r⁻¹ • (q - p))
      (EuclideanSpace.single 2 1) hr (3 / 4)).mp
    have heq : p + r • (r⁻¹ • (q - p)) = q := by simp [smul_smul, hr.ne']
    rw [heq, smul_zero, add_zero, show r * (3 / 4) = 3 * r / 4 by ring]
    exact hq.2
  have ht := hb (blowupSet E p r) (ω * r) hB h0 1 (by norm_num) le_rfl heB
    (r⁻¹ • (q - p)) (by simpa only [mul_one] using hqB)
  simp only [mul_one, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
    abs_mul, abs_of_pos (inv_pos.mpr hr)] at ht
  have ht' := mul_lt_mul_of_pos_left ht hr
  simpa only [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul, mul_comm r η] using ht'

/-- The same uniform threshold controls the height difference of every admissible pair. -/
theorem graph_height_difference {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω)
      (p q : AmbientSpace) (r : ℝ), p ∈ frontier (densityOne E) →
      q ∈ frontier (densityOne E) → 0 < r → r ≤ 1 →
      q ∈ cylinder p (3 * r / 4) (EuclideanSpace.single 2 1) →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable p r
        (EuclideanSpace.single 2 1) + ω * r ≤ ε → |q 2 - p 2| < η * r := by
  obtain ⟨ε, hε, hb⟩ := height_bound_at_center hη
  exact ⟨ε, hε, fun E ω hE p q r hp hq hr hr1 hqp he =>
    hb E ω hE p hp r hr hr1 he q ⟨hq, hqp⟩⟩

end LiquidDrop
