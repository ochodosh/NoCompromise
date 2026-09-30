module

public import NoCompromise.Elliptic.BoundaryHolderRecurrence
public import NoCompromise.Elliptic.BoundaryHolderData
public import NoCompromise.Elliptic.CampanatoHolderIteration

@[expose] public section

/-! Uniform subcritical boundary energy growth and the ensuing normal-excess
power improvement, applied to the genuine half-ball equation data. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Every positive subcritical energy exponent is obtained without a priori
boundedness or continuity of the weak gradient. -/
theorem boundary_holder_energy_growth {a β lam cap HA HG M R : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hβ3 : β < 3) (hR : 0 < R) (hR1 : R ≤ 1)
    (hlam : 0 < lam) (hcap : 0 ≤ cap) (hHA : 0 ≤ HA) (hHG : 0 ≤ HG) (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (u : EuclideanSpace ℝ (Fin 3) → ℝ)
        (F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
        (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
          EuclideanSpace ℝ (Fin 3)),
        BoundaryHolderRadialData a lam cap HA HG R u F G A →
        (∫ x in boundaryHalfBall R, ‖F x‖ ^ 2) ≤ M →
        ∀ r ∈ Ioc 0 R, (∫ x in boundaryHalfBall r, ‖F x‖ ^ 2) ≤ K * r ^ β := by
  obtain ⟨C, hC, D, hD, hstep⟩ := boundary_holder_recurrence_constants hlam hcap hHA hHG
  obtain ⟨K, hK, hscalar⟩ := campanato_subcritical_growth_uniform
    (show 0 < 2 * a by positivity) hβ hβ3 hR hR1 hC.le hD hM
  refine ⟨K, hK, ?_⟩
  intro u F G A h henergy
  let Φ (r : ℝ) := ∫ x in boundaryHalfBall r, ‖F x‖ ^ 2
  apply hscalar Φ
  · exact fun _ _ => integral_nonneg (fun _ => sq_nonneg _)
  · intro s _ r hr hsr
    exact h.energy_mono hsr hr.2
  · intro r hr
    exact (h.energy_mono hr.2 le_rfl).trans henergy
  · intro r hr θ hθ hθ1
    let d := h.mono hr.2
    obtain ⟨hBA, hQG⟩ := d.oscillation_bounds ha.le hHA hHG
    exact (hstep a r hr.1 u F G A d.h1 d.zero_trace d.equation d.coefficient_measurable
      d.coefficient_bound d.datum_memLp d.elliptic_at_zero d.coefficient_bound_at_zero
      hBA hQG θ hθ hθ1).1

/-- A genuine energy bound of order β improves the normal excess to order β+2α.
Constants are uniform over the actual weak solutions. -/
theorem boundary_holder_normal_growth_from_energy {a β lam cap HA HG M E R : ℝ}
    (ha : 0 ≤ a) (hσ : 0 ≤ β + 2 * a) (hβ3 : β ≤ 3) (hgap : β + 2 * a < 5)
    (hR : 0 < R) (hR1 : R ≤ 1)
    (hlam : 0 < lam) (hcap : 0 ≤ cap) (hHA : 0 ≤ HA) (hHG : 0 ≤ HG) (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (u : EuclideanSpace ℝ (Fin 3) → ℝ)
        (F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
        (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
          EuclideanSpace ℝ (Fin 3)),
        BoundaryHolderRadialData a lam cap HA HG R u F G A →
        (∫ x in boundaryHalfBall R, ‖F x‖ ^ 2) ≤ M →
        (∀ r ∈ Ioc 0 R, (∫ x in boundaryHalfBall r, ‖F x‖ ^ 2) ≤ E * r ^ β) →
        ∀ r ∈ Ioc 0 R,
          boundaryNormalExcess (EuclideanSpace.single (Fin.last 2) 1) F
            (volume.restrict (boundaryHalfBall r)) ≤ K * r ^ (β + 2 * a) := by
  obtain ⟨C, hC, D, hD, hstep⟩ := boundary_holder_recurrence_constants hlam hcap hHA hHG
  obtain ⟨K, hK, hscalar⟩ := campanato_oscillation_growth_from_energy hσ hβ3
    (show β + 2 * a < (3 : ℝ) + 2 by linarith) hR hR1 hC.le hD hM (E := E)
  refine ⟨K, hK, ?_⟩
  intro u F G A h henergy hgrowth
  let n : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single (Fin.last 2) 1
  have hn : ‖n‖ = 1 := by simp [n]
  let Φ (r : ℝ) := boundaryNormalExcess n F (volume.restrict (boundaryHalfBall r))
  let Ψ (r : ℝ) := ∫ x in boundaryHalfBall r, ‖F x‖ ^ 2
  apply hscalar Φ Ψ
  · exact fun _ _ => integral_nonneg (fun _ => sq_nonneg _)
  · intro s _ r hr hsr
    exact boundary_normal_excess_mono (boundaryHalfBall_mono hsr)
      (boundaryHalfBall_volume_lt_top r) (h.mono hr.2).h1.memLp_gradient n hn
  · intro r hr
    let : IsFiniteMeasure (volume.restrict (boundaryHalfBall r)) :=
      ⟨by simpa using boundaryHalfBall_volume_lt_top r⟩
    exact (boundary_normal_excess_le_energy (h.mono hr.2).h1.memLp_gradient n hn).trans
      ((h.energy_mono hr.2 le_rfl).trans henergy)
  · exact hgrowth
  · intro r hr θ hθ hθ1
    let d := h.mono hr.2
    obtain ⟨hBA, hQG⟩ := d.oscillation_bounds ha hHA hHG
    have hb := (hstep a r hr.1 u F G A d.h1 d.zero_trace d.equation d.coefficient_measurable
      d.coefficient_bound d.datum_memLp d.elliptic_at_zero d.coefficient_bound_at_zero
      hBA hQG θ hθ hθ1).2
    simpa only [show (3 : ℝ) + 2 = 5 by norm_num] using hb

end LiquidDrop
