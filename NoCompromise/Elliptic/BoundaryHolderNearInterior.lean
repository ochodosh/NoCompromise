module

public import NoCompromise.Elliptic.BoundaryHolderGeometry
public import NoCompromise.Elliptic.BoundaryHolderInteriorBound
public import NoCompromise.Elliptic.BoundaryHolderUniformIteration

@[expose] public section

/-! Sharp oscillation on interior balls close to the flat boundary. The source
energy and initial excess come from the proved boundary estimates, and the
constants stay uniform as the height tends to zero. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Boundary growth supplies the exact initial powers needed for a uniform
interior Campanato iteration. All premises concern the original weak gradient. -/
theorem boundary_near_interior_growth {a lam cap HA HG M K P : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hHA : 0 ≤ HA) (hHG : 0 ≤ HG) (hK : 0 ≤ K) (hP : 0 ≤ P) :
    ∃ L Q : ℝ, 0 ≤ L ∧ 0 ≤ Q ∧
      ∀ (u : EuclideanSpace ℝ (Fin 3) → ℝ)
        (F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
        (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
          EuclideanSpace ℝ (Fin 3)),
        BoundaryHolderUnitData a lam cap HA HG M u F G A →
        (∀ z : EuclideanSpace ℝ (Fin 2), ‖graphAppendN z 0‖ < 3 / 4 →
          ∀ r ∈ Ioc 0 (1 / 8 : ℝ),
            boundaryNormalExcess (EuclideanSpace.single (Fin.last 2) 1) F
              (volume.restrict (ball (graphAppendN z 0) r ∩
                {y | 0 < y (Fin.last 2)})) ≤ K * r ^ (3 + 2 * a) ∧
            (∫ x in ball (graphAppendN z 0) r ∩ {y | 0 < y (Fin.last 2)}, ‖F x‖ ^ 2) ≤
              P * r ^ (3 : ℝ)) →
        ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ < 5 / 8 →
          0 < x (Fin.last 2) → x (Fin.last 2) < 1 / 64 →
          ∀ r ∈ Ioc 0 (x (Fin.last 2) / 4),
            (∫ y in ball x r, ‖F y - ⨍ z in ball x r, F z‖ ^ 2) ≤
              L * r ^ (3 + 2 * a) ∧
            (∫ y in ball x r, ‖F y‖ ^ 2) ≤ Q * r ^ (3 : ℝ) := by
  obtain ⟨Q, hQ, hbQ⟩ := boundary_interior_energy_cubic ha ha1 hlam hcap hHA hHG
    (show 0 ≤ 64 * P by positivity)
  obtain ⟨L, hL, hbL⟩ := boundary_interior_oscillation_uniform_radius ha ha1 hlam hcap hHA hHG
    (show 0 ≤ K * (8 : ℝ) ^ (3 + 2 * a) by positivity) (E := Q)
  refine ⟨L, Q, hL, hQ, ?_⟩
  intro u F G A h hboundary x hx hd hdsmall
  let d := x (Fin.last 2)
  have hd0 : 0 < d := hd
  have hds : d < 1 / 64 := hdsmall
  let q := graphAppendN (graphProjectionN 2 x) 0
  let V := ball q (2 * d) ∩ {y : EuclideanSpace ℝ (Fin 3) | 0 < y (Fin.last 2)}
  have hq : ‖q‖ < 3 / 4 := (boundary_flat_projection_norm_le x).trans_lt
    (hx.trans (by norm_num))
  have h2d : 2 * d ∈ Ioc 0 (1 / 8 : ℝ) := ⟨by positivity, by linarith only [hd0, hds]⟩
  have hVsub : V ⊆ boundaryHalfBall 1 := boundary_tangential_ball_subset_unit hq h2d.2
  have hlarge : ball x (d / 2) ⊆ boundaryHalfBall 1 :=
    boundary_interior_ball_subset_unit hx
      (by linarith only [hd0, hds]) (by linarith only [hd0, hds])
  have hsmall : ball x (d / 4) ⊆ boundaryHalfBall 1 :=
    (ball_subset_ball (by linarith only [hd0, hds] : d / 4 ≤ d / 2)).trans hlarge
  have hlargeV : ball x (d / 2) ⊆ V :=
    boundary_interior_ball_subset_tangential hd (by linarith only [hd0, hds])
  have hsmallV : ball x (d / 4) ⊆ V :=
    boundary_interior_ball_subset_tangential hd (by linarith only [hd0, hds])
  have hVfin : volume V < ∞ := (measure_mono inter_subset_left).trans_lt
    (isBounded_ball (x := q) (r := 2 * d)).measure_lt_top
  have hFV := h.h1.memLp_gradient.mono_measure (Measure.restrict_mono hVsub le_rfl)
  have hbound := hboundary (graphProjectionN 2 x) hq (2 * d) h2d
  have henergy : (∫ y in ball x (d / 2), ‖F y‖ ^ 2) ≤
      (64 * P) * (d / 2) ^ (3 : ℝ) := by
    calc
      _ ≤ ∫ y in V, ‖F y‖ ^ 2 := setIntegral_mono_set
        ((memLp_two_iff_integrable_sq_norm hFV.aestronglyMeasurable).mp hFV)
        (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall hlargeV)
      _ ≤ P * (2 * d) ^ (3 : ℝ) := hbound.2
      _ = _ := by rw [Real.rpow_ofNat, Real.rpow_ofNat]; ring
  have he := hbQ x (d / 2) (by positivity) (by linarith only [hd0, hds]) u F G A
    (h.coefficient_continuous.mono (hlarge.trans subset_closure))
    (h.datum_continuous.mono (hlarge.trans subset_closure))
    (fun y hy => h.coefficient_bound y (subset_closure (hlarge hy)))
    (fun y hy => h.elliptic y (subset_closure (hlarge hy)))
    (fun y hy z hz => h.coefficient_holder y (subset_closure (hlarge hy)) z
      (subset_closure (hlarge hz)))
    (fun y hy z hz => h.datum_holder y (subset_closure (hlarge hy)) z
      (subset_closure (hlarge hz)))
    (h.h1.mono hlarge) (h.equation.mono hlarge) henergy
  have he' : ∀ r ∈ Ioc 0 (d / 4), (∫ y in ball x r, ‖F y‖ ^ 2) ≤ Q * r ^ (3 : ℝ) := by
    simpa only [div_div, show (2 : ℝ) * 2 = 4 by norm_num] using he
  have hinit : (∫ y in ball x (d / 4), ‖F y - ⨍ z in ball x (d / 4), F z‖ ^ 2) ≤
      (K * (8 : ℝ) ^ (3 + 2 * a)) * (d / 4) ^ (3 + 2 * a) := by
    calc
      _ ≤ boundaryNormalExcess (EuclideanSpace.single (Fin.last 2) 1) F
          (volume.restrict V) := boundary_variance_le_excess_of_subset hsmallV hVfin hFV _
            (by simp only [PiLp.norm_single, norm_one])
      _ ≤ K * (2 * d) ^ (3 + 2 * a) := hbound.1
      _ = _ := by
        rw [show 2 * d = 8 * (d / 4) by ring,
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) (by positivity)]
        ring
  have hGmem := (boundary_radialData_of_holder ha.le hHG zero_lt_one
    h.coefficient_continuous h.datum_continuous h.coefficient_bound h.elliptic
    h.coefficient_holder h.datum_holder h.h1 h.trace_zero h.equation).datum_memLp
  have hos := hbL x (d / 4) (by positivity) u F G A
    (h.coefficient_continuous.mono (hsmall.trans subset_closure))
    (h.datum_continuous.mono (hsmall.trans subset_closure))
    (fun y hy => h.coefficient_bound y (subset_closure (hsmall hy)))
    (fun y hy => h.elliptic y (subset_closure (hsmall hy)))
    (fun y hy z hz => h.coefficient_holder y (subset_closure (hsmall hy)) z
      (subset_closure (hsmall hz)))
    (fun y hy z hz => h.datum_holder y (subset_closure (hsmall hy)) z
      (subset_closure (hsmall hz)))
    (h.h1.mono hsmall) (h.equation.mono hsmall)
    (hGmem.mono_measure (Measure.restrict_mono hsmall le_rfl)) he' hinit
  exact fun r hr => ⟨hos r hr, he' r hr⟩

end LiquidDrop
