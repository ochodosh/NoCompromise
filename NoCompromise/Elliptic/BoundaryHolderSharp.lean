module

public import NoCompromise.Elliptic.BoundaryHolderHolderData
public import NoCompromise.Elliptic.BoundaryHolderGrowth
public import NoCompromise.Elliptic.BoundaryHolderEnergyBootstrap

@[expose] public section

/-! Two genuine boundary iterations yield the full coefficient exponent for
the normal excess, and consequently for the actual gradient mean oscillation. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Sharp normal-excess decay and cubic energy growth, with all constants chosen
before the coefficient fields and the actual zero-trace weak solution. -/
theorem boundary_holder_sharp_normal_decay {a lam cap HA HG M R : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hR : 0 < R) (hR1 : R ≤ 1)
    (hlam : 0 < lam) (hcap : 0 ≤ cap) (hHA : 0 ≤ HA) (hHG : 0 ≤ HG) (hM : 0 ≤ M) :
    ∃ K P : ℝ, 0 ≤ K ∧ 0 ≤ P ∧
      ∀ (u : EuclideanSpace ℝ (Fin 3) → ℝ)
        (F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
        (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
          EuclideanSpace ℝ (Fin 3)),
        BoundaryHolderRadialData a lam cap HA HG R u F G A →
        (∫ x in boundaryHalfBall R, ‖F x‖ ^ 2) ≤ M →
        ∀ r ∈ Ioc 0 R,
          boundaryNormalExcess (EuclideanSpace.single (Fin.last 2) 1) F
              (volume.restrict (boundaryHalfBall r)) ≤ K * r ^ (3 + 2 * a) ∧
            (∫ x in boundaryHalfBall r, ‖F x‖ ^ 2) ≤ P * r ^ (3 : ℝ) := by
  obtain ⟨E, _, henergy⟩ := boundary_holder_energy_growth ha
    (show 0 < 3 - a by linarith) (show 3 - a < 3 by linarith)
    hR hR1 hlam hcap hHA hHG hM
  obtain ⟨K₀, hK₀, hnormal⟩ := boundary_holder_normal_growth_from_energy ha.le
    (show 0 ≤ 3 - a + 2 * a by linarith) (show 3 - a ≤ 3 by linarith)
    (show 3 - a + 2 * a < 5 by linarith) hR hR1 hlam hcap hHA hHG hM (E := E)
  obtain ⟨P, hP, hcubic⟩ := boundary_energy_cubic_of_normal_decay hK₀
    (show 0 < a / 2 by positivity) hR hM
  obtain ⟨K, hK, hsharp⟩ := boundary_holder_normal_growth_from_energy ha.le
    (show 0 ≤ (3 : ℝ) + 2 * a by positivity) (le_rfl (a := (3 : ℝ)))
    (show 3 + 2 * a < 5 by linarith) hR hR1 hlam hcap hHA hHG hM (E := P)
  refine ⟨K, P, hK, hP, ?_⟩
  intro u F G A h hM'
  have hfirst := hnormal u F G A h hM' (henergy u F G A h hM')
  have hpower : ∀ r ∈ Ioc 0 R,
      boundaryNormalExcess (EuclideanSpace.single (Fin.last 2) 1) F
        (volume.restrict (boundaryHalfBall r)) ≤ K₀ * r ^ (3 + 2 * (a / 2)) := by
    intro r hr
    convert hfirst r hr using 2
    congr 1
    ring
  have he := hcubic F h.h1.memLp_gradient hM' hpower
  exact fun r hr => ⟨hsharp u F G A h hM' he r hr, he r hr⟩

/-- The displayed boundary mean-oscillation estimate follows for the actual weak
gradient, with no continuity or classical gradient premise. -/
theorem boundary_holder_mean_oscillation {a lam cap HA HG M R : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hR : 0 < R) (hR1 : R ≤ 1)
    (hlam : 0 < lam) (hcap : 0 ≤ cap) (hHA : 0 ≤ HA) (hHG : 0 ≤ HG) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : EuclideanSpace ℝ (Fin 3) → ℝ)
        (F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
        (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
          EuclideanSpace ℝ (Fin 3)),
        BoundaryHolderRadialData a lam cap HA HG R u F G A →
        (∫ x in boundaryHalfBall R, ‖F x‖ ^ 2) ≤ M →
        ∀ r ∈ Ioc 0 R,
          (⨍ x in boundaryHalfBall r, ‖F x - ⨍ y in boundaryHalfBall r, F y‖ ^ 2) ≤
            C * r ^ (2 * a) := by
  obtain ⟨K, _, hK, _, hsharp⟩ :=
    boundary_holder_sharp_normal_decay ha ha1 hR hR1 hlam hcap hHA hHG hM
  let V := volume.real (boundaryHalfBall 1)
  have hV : 0 < V := ENNReal.toReal_pos (boundaryHalfBall_volume_pos zero_lt_one).ne'
    (boundaryHalfBall_volume_lt_top 1).ne
  let C := K / V + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro u F G A h hM' r hr
  let : IsFiniteMeasure (volume.restrict (boundaryHalfBall r)) :=
    ⟨by simpa using boundaryHalfBall_volume_lt_top r⟩
  have hv := (boundary_variance_le_normal_excess (h.mono hr.2).h1.memLp_gradient
    (EuclideanSpace.single (Fin.last 2) 1)).trans ((hsharp u F G A h hM' r hr).1)
  rw [average_eq]
  simp only [smul_eq_mul, Measure.real, Measure.restrict_apply_univ]
  calc
    _ ≤ (volume.real (boundaryHalfBall r))⁻¹ * (K * r ^ (3 + 2 * a)) :=
      mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr ENNReal.toReal_nonneg)
    _ = (K / V) * r ^ (2 * a) := by
      rw [boundaryHalfBall_real_volume hr.1, Real.rpow_add hr.1, Real.rpow_ofNat]
      dsimp [V]
      field_simp [hr.1.ne']
    _ ≤ C * r ^ (2 * a) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
        (Real.rpow_nonneg hr.1.le _)

/-- The blueprint's displayed estimate, under its genuine closed-half-ball
Hölder assumptions and actual zero weak trace. Construction of the full
boundary C¹,α representative is a separate step. -/
theorem boundary_holder_mean_oscillation_of_holder {a lam cap HA HG M : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hHA : 0 ≤ HA) (hHG : 0 ≤ HG) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : EuclideanSpace ℝ (Fin 3) → ℝ)
        (F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
        (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
          EuclideanSpace ℝ (Fin 3)),
        ContinuousOn A (closure (boundaryHalfBall 1)) →
        ContinuousOn G (closure (boundaryHalfBall 1)) →
        (∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap) →
        (∀ x ∈ closure (boundaryHalfBall 1), ∀ ξ,
          lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ) →
        (∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
          ‖A x - A y‖ ≤ HA * dist x y ^ a) →
        (∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
          ‖G x - G y‖ ≤ HG * dist x y ^ a) →
        HasH1GradientOn u F (boundaryHalfBall 1) → HasZeroFlatTraceOn u F (ball 0 1) →
        IsWeakDivergenceEquationOn A F G (boundaryHalfBall 1) →
        (∫ x in boundaryHalfBall 1, ‖F x‖ ^ 2) ≤ M →
        ∀ r ∈ Ioc 0 (1 : ℝ),
          (⨍ x in boundaryHalfBall r, ‖F x - ⨍ y in boundaryHalfBall r, F y‖ ^ 2) ≤
            C * r ^ (2 * a) := by
  obtain ⟨C, hC, hb⟩ := boundary_holder_mean_oscillation ha ha1 zero_lt_one le_rfl
    hlam hcap hHA hHG hM
  refine ⟨C, hC, ?_⟩
  intro u F G A hA hG hbA hell hHA' hHG' hu hT hw hE
  exact hb u F G A (boundary_radialData_of_holder ha.le hHG zero_lt_one hA hG hbA hell
    hHA' hHG' hu hT hw) hE

end LiquidDrop
