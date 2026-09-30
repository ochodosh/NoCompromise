module

public import NoCompromise.Elliptic.BoundaryHolderTranslatedData
public import NoCompromise.Elliptic.BoundaryHolderSharp

@[expose] public section

/-! Uniform boundary excess estimates at all tangential centers in a fixed
interior flat disk. The record below contains only the original analytic data. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The original closed-half-ball coefficient assumptions, genuine H¹ solution,
weak equation, and localized zero flat trace. No regularity conclusion is a field. -/
structure BoundaryHolderUnitData (a lam cap HA HG M : ℝ)
    (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)) : Prop where
  coefficient_continuous : ContinuousOn A (closure (boundaryHalfBall 1))
  datum_continuous : ContinuousOn G (closure (boundaryHalfBall 1))
  coefficient_bound : ∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap
  elliptic : ∀ x ∈ closure (boundaryHalfBall 1), ∀ ξ,
    lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ
  coefficient_holder : ∀ x ∈ closure (boundaryHalfBall 1),
    ∀ y ∈ closure (boundaryHalfBall 1), ‖A x - A y‖ ≤ HA * dist x y ^ a
  datum_holder : ∀ x ∈ closure (boundaryHalfBall 1),
    ∀ y ∈ closure (boundaryHalfBall 1), ‖G x - G y‖ ≤ HG * dist x y ^ a
  h1 : HasH1GradientOn u F (boundaryHalfBall 1)
  trace_zero : HasZeroFlatTraceOn u F (ball 0 1)
  equation : IsWeakDivergenceEquationOn A F G (boundaryHalfBall 1)
  energy_bound : (∫ x in boundaryHalfBall 1, ‖F x‖ ^ 2) ≤ M

lemma boundary_average_halfBall_translate {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : EuclideanSpace ℝ (Fin 3) → E) (z : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    (⨍ x in boundaryHalfBall r, f (x + graphAppendN z 0)) =
      ⨍ x in ball (graphAppendN z 0) r ∩ {y | 0 < y (Fin.last 2)}, f x := by
  have hvol := boundary_integral_halfBall_translate (fun _ => (1 : ℝ)) z r
  simp only [integral_const, smul_eq_mul, mul_one,
    Measure.real, Measure.restrict_apply_univ] at hvol
  simp only [average_eq, Measure.real, Measure.restrict_apply_univ,
    boundary_integral_halfBall_translate, hvol]

lemma boundary_normal_excess_translate (F : EuclideanSpace ℝ (Fin 3) →
    EuclideanSpace ℝ (Fin 3)) (n : EuclideanSpace ℝ (Fin 3))
    (z : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    boundaryNormalExcess n (fun x => F (x + graphAppendN z 0))
      (volume.restrict (boundaryHalfBall r)) =
    boundaryNormalExcess n F
      (volume.restrict (ball (graphAppendN z 0) r ∩ {y | 0 < y (Fin.last 2)})) := by
  unfold boundaryNormalExcess boundaryNormalMean
  rw [boundary_average_halfBall_translate]
  exact boundary_integral_halfBall_translate
    (fun x => ‖F x - inner ℝ n (⨍ y in ball (graphAppendN z 0) r ∩
      {y | 0 < y (Fin.last 2)}, F y) • n‖ ^ 2) z r

lemma BoundaryHolderUnitData.translated_energy {a lam cap HA HG M : ℝ}
    {u : EuclideanSpace ℝ (Fin 3) → ℝ}
    {F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)} (h : BoundaryHolderUnitData a lam cap HA HG M u F G A)
    (z : EuclideanSpace ℝ (Fin 2)) (hz : ‖graphAppendN z 0‖ < 3 / 4)
    {r : ℝ} (hr : r ≤ 1 / 8) :
    (∫ x in boundaryHalfBall r, ‖F (x + graphAppendN z 0)‖ ^ 2) ≤ M := by
  rw [boundary_integral_halfBall_translate (fun x => ‖F x‖ ^ 2) z r]
  have hsub : ball (graphAppendN z 0) r ∩ {y | 0 < y (Fin.last 2)} ⊆
      boundaryHalfBall 1 := by
    intro x hx
    have he : x - graphAppendN z 0 + graphAppendN z 0 = x := sub_add_cancel _ _
    have hx' : x - graphAppendN z 0 ∈ boundaryHalfBall r :=
      (boundary_halfBall_translate_mem z _ r).mp (by simpa only [he] using hx)
    simpa only [he] using boundary_small_translate_halfBall_subset hz hr hx'
  have hi := (memLp_two_iff_integrable_sq_norm h.h1.memLp_gradient.aestronglyMeasurable).mp h.h1.memLp_gradient
  exact (setIntegral_mono_set hi (Eventually.of_forall fun _ => sq_nonneg _)
    (Eventually.of_forall hsub)).trans h.energy_bound

/-- Both constants are uniform over all points of the smaller flat disk and
all data satisfying the original assumptions. -/
theorem boundary_holder_tangential_growth {a lam cap HA HG M : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hHA : 0 ≤ HA) (hHG : 0 ≤ HG) (hM : 0 ≤ M) :
    ∃ K P : ℝ, 0 ≤ K ∧ 0 ≤ P ∧
      ∀ (u : EuclideanSpace ℝ (Fin 3) → ℝ)
        (F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
        (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
          EuclideanSpace ℝ (Fin 3)),
        BoundaryHolderUnitData a lam cap HA HG M u F G A →
        ∀ z : EuclideanSpace ℝ (Fin 2), ‖graphAppendN z 0‖ < 3 / 4 →
        ∀ r ∈ Ioc 0 (1 / 8 : ℝ),
          boundaryNormalExcess (EuclideanSpace.single (Fin.last 2) 1) F
            (volume.restrict (ball (graphAppendN z 0) r ∩
              {y | 0 < y (Fin.last 2)})) ≤ K * r ^ (3 + 2 * a) ∧
          (∫ x in ball (graphAppendN z 0) r ∩ {y | 0 < y (Fin.last 2)}, ‖F x‖ ^ 2) ≤
            P * r ^ (3 : ℝ) := by
  obtain ⟨K, P, hK, hP, hb⟩ := boundary_holder_sharp_normal_decay ha ha1
    (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : (1 / 8 : ℝ) ≤ 1)
    hlam hcap hHA hHG hM
  refine ⟨K, P, hK, hP, ?_⟩
  intro u F G A h z hz r hr
  have hd := boundary_translated_radialData_of_holder ha.le hHG
    (by norm_num : (0 : ℝ) < 1 / 8) le_rfl z hz
    h.coefficient_continuous h.datum_continuous h.coefficient_bound h.elliptic
    h.coefficient_holder h.datum_holder h.h1 h.trace_zero h.equation
  have hh := hb _ _ _ _ hd (h.translated_energy z hz le_rfl) r hr
  rw [boundary_normal_excess_translate F _ z r,
    boundary_integral_halfBall_translate (fun x => ‖F x‖ ^ 2) z r] at hh
  exact hh

end LiquidDrop
