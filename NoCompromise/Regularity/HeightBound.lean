import NoCompromise.Regularity.HeightBoundUnit
import NoCompromise.Regularity.HeightBoundBoundaryScaling
import NoCompromise.Regularity.ExcessScaling

/-! # The scale-invariant height bound

The threshold is fixed before the set, quasiminimality parameter, and radius.
Both the canonical boundary and the actual reduced-normal excess are rescaled
by proved exact identities.
-/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace LiquidDrop

/-- Full blueprint `lem:height-bound`. The proof in fact works for every
positive η, so the stated upper bound η < 1/8 is unnecessary. -/
theorem height_bound {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (E : Set AmbientSpace) (ω : ℝ)
      (hE : IsOmegaMinimal E ω),
      (0 : AmbientSpace) ∈ frontier (densityOne E) →
      ∀ r : ℝ, 0 < r → r ≤ 1 →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 r
        (EuclideanSpace.single 2 1) + ω * r ≤ ε →
      ∀ x ∈ frontier (densityOne E) ∩ standardCylinder (3 * r / 4), |x 2| < η * r := by
  obtain ⟨ε, hε, hunit⟩ := height_bound_unit hη
  refine ⟨min ε 1, lt_min hε (by norm_num), ?_⟩
  intro E ω hE h0 r hr hr1 he x hx
  have hB : IsOmegaMinimal (blowupSet E 0 r) (ω * r) := by
    apply IsOmegaMinimalAtScales.blowupSet hE 0 hr (by norm_num)
    simpa only [mul_one, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hr1
  have hnonneg : 0 ≤ cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 r
      (EuclideanSpace.single 2 1) :=
    div_nonneg (normalExcessIntegral_nonneg _ _ _ _ _) (sq_nonneg r)
  have hω : ω * r ≤ 1 := by have := min_le_right ε (1 : ℝ); linarith
  have heB : cylindricalExcess (blowupSet E 0 r) hB.locallyFinite hB.nullMeasurable 0 1
      (EuclideanSpace.single 2 1) ≤ ε := by
    rw [cylindricalExcess_blowupSet_unit E hE.locallyFinite hE.nullMeasurable 0 hr]
    have := min_le_left ε (1 : ℝ)
    have := mul_nonneg hE.nonneg hr.le
    linarith
  have h0B : (0 : AmbientSpace) ∈ frontier (densityOne (blowupSet E 0 r)) := by
    simpa only [smul_zero] using (height_mem_frontier_blowup_zero E hr 0).mpr h0
  have hxB : r⁻¹ • x ∈ frontier (densityOne (blowupSet E 0 r)) ∩ standardCylinder (3 / 4) := by
    refine ⟨(height_mem_frontier_blowup_zero E hr x).mpr hx.1, ?_⟩
    have hh := (height_mem_standardCylinder_pos_smul x (inv_pos.mpr hr) (3 * r / 4)).mpr hx.2
    have hscale : r⁻¹ * (3 * r / 4) = (3 / 4 : ℝ) := by field_simp
    simpa only [hscale] using hh
  have hh := hunit (blowupSet E 0 r) (ω * r) hB hω h0B heB _ hxB
  simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hr)] at hh
  have hh' := mul_lt_mul_of_pos_left hh hr
  simpa only [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul, mul_comm r η] using hh'

end LiquidDrop
