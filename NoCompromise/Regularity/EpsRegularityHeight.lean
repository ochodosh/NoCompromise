import NoCompromise.Regularity.HeightBound
import NoCompromise.Regularity.ExcessDecayCoordinates
import NoCompromise.Regularity.GraphTwoPointCaps

/-! # Height bounds in general position and vertical boundary crossings -/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- Uniform height control at every boundary center, unit axis, and admissible scale. -/
theorem height_bound_general {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω)
      (p ν : AmbientSpace) (s : ℝ),
      p ∈ frontier (densityOne E) → ‖ν‖ = 1 → 0 < s → s ≤ 1 →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable p s ν + ω * s ≤ ε →
      ∀ y ∈ frontier (densityOne E) ∩ cylinder p (3 * s / 4) ν,
        |inner ℝ ν (y - p)| < η * s := by
  obtain ⟨ε, hε, hb⟩ := height_bound hη
  refine ⟨ε, hε, fun E ω hE p ν s hp hν hs hs1 he y hy => ?_⟩
  let Q := verticalAxisIsometry ν
  let F := excessDecayCoordinates E p s ν
  have hF : IsOmegaMinimal F (ω * s) := hE.excessDecayCoordinates p hs hs1 ν
  have h0 : (0 : AmbientSpace) ∈ frontier (densityOne F) :=
    (excessDecayCoordinates_origin_frontier E p ν hs).mpr hp
  have heF : cylindricalExcess F hF.locallyFinite hF.nullMeasurable 0 1
      (EuclideanSpace.single 2 1) + (ω * s) * 1 ≤ ε := by
    simpa only [F, cylindricalExcess_excessDecayCoordinates_unit hE p ν hs hs1 hν,
      mul_one] using he
  have hyF : Q.symm (s⁻¹ • (y - p)) ∈ frontier (densityOne F) := by
    change Q.symm (s⁻¹ • (y - p)) ∈
      frontier (densityOne (excessDecayCoordinates E p s ν))
    rw [excessDecayCoordinates, frontier_densityOne_preimage_affineIsometry]
    change Q (Q.symm (s⁻¹ • (y - p))) ∈ frontier (densityOne (blowupSet E p s))
    rw [Q.apply_symm_apply]
    exact (inverse_mem_frontier_densityOne_blowupSet E p y hs).mpr hy.1
  have hyC : Q.symm (s⁻¹ • (y - p)) ∈ standardCylinder (3 / 4) := by
    rw [standardCylinder_eq_cylinder]
    apply (mem_cylinder_linearIsometry Q 0 _ (EuclideanSpace.single 2 1) (3 / 4)).mp
    rw [Q.apply_symm_apply, map_zero]
    rw [show Q (EuclideanSpace.single 2 1) = ν from verticalAxisIsometry_apply_vertical hν]
    apply (mem_cylinder_translate_pos_smul p 0 _ ν hs (3 / 4)).mp
    simpa only [smul_smul, mul_inv_cancel₀ hs.ne', one_smul, add_sub_cancel,
      smul_zero, add_zero, show s * (3 / 4) = 3 * s / 4 by ring] using hy.2
  have ht := hb F (ω * s) hF h0 1 (by norm_num) le_rfl heF
    (Q.symm (s⁻¹ • (y - p))) (by simpa only [mul_one, mem_inter_iff] using And.intro hyF hyC)
  rw [linearIsometry_inverse_vertical,
    show Q (EuclideanSpace.single 2 1) = ν from verticalAxisIsometry_apply_vertical hν,
    inner_smul_right, abs_mul, abs_of_pos (inv_pos.mpr hs), mul_one] at ht
  have ht' := mul_lt_mul_of_pos_left ht hs
  simpa only [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul, mul_comm s η] using ht'

/-- Every vertical line over the half disk meets the canonical boundary near height zero. -/
theorem frontier_vertical_crossing :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω) (r : ℝ),
      (0 : AmbientSpace) ∈ frontier (densityOne E) → 0 < r → r ≤ 1 →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 r
        (EuclideanSpace.single 2 1) + ω * r ≤ ε →
      ∀ x' : EuclideanSpace ℝ (Fin 2), ‖x'‖ < r / 2 →
        ∃ t : ℝ, |t| < r / 8 ∧ graphAppendN x' t ∈ frontier (densityOne E) := by
  obtain ⟨c, hc, ε₁, hε₁, hcaps⟩ :=
    graph_two_point_lipschitz (γ := (1 / 16 : ℝ)) (by norm_num) (by norm_num)
  obtain ⟨ε₂, hε₂, hheight⟩ := height_bound (η := (1 / 8 : ℝ)) (by norm_num)
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro E ω hE r h0 hr hr1 he x' hx'
  let F := blowupSet E 0 r
  have hF : IsOmegaMinimal F (ω * r) := by
    apply IsOmegaMinimalAtScales.blowupSet hE 0 hr (by norm_num)
    simpa only [mul_one, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hr1
  have h0F : (0 : AmbientSpace) ∈ frontier (densityOne F) := by
    apply (mem_frontier_densityOne_blowupSet E 0 0 hr).mpr
    simpa only [smul_zero, add_zero] using h0
  have heF : cylindricalExcess F hF.locallyFinite hF.nullMeasurable 0 1
      (EuclideanSpace.single 2 1) + ω * r ≤ min ε₁ ε₂ := by
    simpa only [F, cylindricalExcess_blowupSet_unit E hE.locallyFinite
      hE.nullMeasurable 0 hr] using he
  obtain ⟨_, _, hbottom, htop, _⟩ :=
    hcaps F (ω * r) hF h0F (heF.trans (min_le_left _ _))
  let y' := r⁻¹ • x'
  have hy' : ‖y'‖ < (1 / 2 : ℝ) := by
    dsimp [y']
    rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hr).le]
    calc
      r⁻¹ * ‖x'‖ < r⁻¹ * (r / 2) := mul_lt_mul_of_pos_left hx' (inv_pos.mpr hr)
      _ = 1 / 2 := by field_simp
  have hyball : y' ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) := by
    simpa only [mem_ball, dist_zero_right] using hy'
  have hbottomF : graphAppendN y' (-(1 / 2 : ℝ)) ∈ densityOne F :=
    hbottom ⟨y', hyball, rfl⟩
  have htopF : graphAppendN y' (1 / 2 : ℝ) ∉ densityOne F := by
    exact disjoint_left.mp (disjoint_densityZero_densityOne F) (htop ⟨y', hyball, rfl⟩)
  let S : Set AmbientSpace :=
    (fun t : ℝ => graphAppendN y' t) '' Icc (-(1 / 2 : ℝ)) (1 / 2)
  have hcont : Continuous (fun t : ℝ => graphAppendN y' t) := by
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hconn : IsPreconnected S := isPreconnected_Icc.image _ hcont.continuousOn
  have hbottomS : graphAppendN y' (-(1 / 2 : ℝ)) ∈ S :=
    ⟨-(1 / 2 : ℝ), by constructor <;> norm_num, rfl⟩
  have htopS : graphAppendN y' (1 / 2 : ℝ) ∈ S :=
    ⟨(1 / 2 : ℝ), by constructor <;> norm_num, rfl⟩
  have hcross : (S ∩ frontier (densityOne F)).Nonempty := by
    by_contra hn
    have havoid : ∀ q ∈ S, q ∉ frontier (densityOne F) :=
      fun q hq hqf => hn ⟨q, hq, hqf⟩
    have hcover : S ⊆ interior (densityOne F) ∪ interior (densityOne F)ᶜ := by
      rw [← compl_frontier_eq_union_interior]
      exact havoid
    have hb : graphAppendN y' (-(1 / 2 : ℝ)) ∈ interior (densityOne F) :=
      (mem_interior_iff_notMem_frontier hbottomF).mpr (havoid _ hbottomS)
    have ht : graphAppendN y' (1 / 2 : ℝ) ∈ interior (densityOne F)ᶜ := by
      apply (mem_interior_iff_notMem_frontier htopF).mpr
      rw [frontier_compl]
      exact havoid _ htopS
    obtain ⟨q, _, hq₁, hq₂⟩ :=
      hconn _ _ isOpen_interior isOpen_interior hcover
        ⟨_, hbottomS, hb⟩ ⟨_, htopS, ht⟩
    exact (interior_subset hq₂) (interior_subset hq₁)
  obtain ⟨q, ⟨t₀, ht₀, rfl⟩, hq⟩ := hcross
  have ht₀abs : |t₀| ≤ (1 / 2 : ℝ) := abs_le.mpr ht₀
  have hqC : graphAppendN y' t₀ ∈ standardCylinder (3 / 4) := by
    change ‖graphProjectionN 2 (graphAppendN y' t₀)‖ < 3 / 4 ∧
      |graphAppendN y' t₀ 2| < 3 / 4
    rw [graphProjectionN_append, graphAppendN_height_three]
    constructor <;> linarith
  have hsmall : |t₀| < (1 / 8 : ℝ) := by
    have hh := hheight F (ω * r) hF h0F 1 (by norm_num) le_rfl
      (by simpa only [mul_one] using heF.trans (min_le_right _ _))
      (graphAppendN y' t₀)
      (by simpa only [mul_one, mem_inter_iff] using And.intro hq hqC)
    simpa only [graphAppendN_height_three, mul_one] using hh
  refine ⟨r * t₀, ?_, ?_⟩
  · rw [abs_mul, abs_of_pos hr]
    nlinarith [mul_lt_mul_of_pos_left hsmall hr]
  · have hscale : r • graphAppendN y' t₀ = graphAppendN x' (r * t₀) := by
      simp only [graphAppendN, smul_add, ← map_smul, smul_smul, y',
        mul_inv_cancel₀ hr.ne', one_smul]
    have hh := (mem_frontier_densityOne_blowupSet E 0 (graphAppendN y' t₀) hr).mp hq
    simpa only [zero_add, hscale] using hh

end LiquidDrop
