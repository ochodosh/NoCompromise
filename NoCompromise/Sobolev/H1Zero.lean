module

public import NoCompromise.Sobolev.H1TraceOperator
public import NoCompromise.Sobolev.SpatialGN

@[expose] public section

/-!
# The genuine zero-boundary Sobolev space

`H1ZeroSpace` is the H¹ closure of smooth compactly supported functions in the
open domain. Spatial Sobolev and finite-volume Hölder give its Poincaré estimate.
Every constructed boundary trace vanishes on this space; no identification of
this closure with an assumed trace kernel is used.
-/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Smooth compactly supported functions whose support lies inside the domain. -/
def h1ZeroTestFunctions {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n))) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n) → ℝ) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ D}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.1.add hg.2.1,
    (tsupport_add _ _).trans (union_subset hf.2.2 hg.2.2)⟩
  smul_mem' c f hf := ⟨contDiff_const.smul hf.1, hf.2.1.smul_left,
    (tsupport_smul_subset_right (fun _ => c) f).trans hf.2.2⟩

lemma h1ZeroTestFunctions.hasH1GradientOn {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (f : h1ZeroTestFunctions D)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) :
    HasH1GradientOn f.val (gradient f.val) U := by
  have hc : ContDiff ℝ 1 f.val := f.property.1.of_le (by simp)
  exact ⟨hasWeakGradientOn_of_contDiffOn hU hc.contDiffOn,
    hc.continuous.memLp_of_hasCompactSupport f.property.2.1,
    (continuous_gradient_of_contDiff hc).memLp_of_hasCompactSupport
      (f.property.2.1.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset _))⟩

/-- The actual H¹ class of a smooth interior test function. -/
def h1ZeroTestFunctions.toH1Space {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) :
    h1ZeroTestFunctions D →ₗ[ℝ] H1Space D where
  toFun f := H1Space.ofFunction f.val (gradient f.val) (h1ZeroTestFunctions.hasH1GradientOn f hD)
  map_add' f g := by
    apply H1Space.ext_ae hD
    filter_upwards [H1Space.coeFn_ofFunction _ _ (h1ZeroTestFunctions.hasH1GradientOn (f + g) hD),
      H1Space.coeFn_add (H1Space.ofFunction _ _ (h1ZeroTestFunctions.hasH1GradientOn f hD))
        (H1Space.ofFunction _ _ (h1ZeroTestFunctions.hasH1GradientOn g hD)),
      H1Space.coeFn_ofFunction _ _ (h1ZeroTestFunctions.hasH1GradientOn f hD),
      H1Space.coeFn_ofFunction _ _ (h1ZeroTestFunctions.hasH1GradientOn g hD)] with x h1 h2 h3 h4
    rw [h3, h4] at h2
    exact h1.trans h2.symm
  map_smul' c f := by
    apply H1Space.ext_ae hD
    filter_upwards [H1Space.coeFn_ofFunction _ _ (h1ZeroTestFunctions.hasH1GradientOn (c • f) hD),
      H1Space.coeFn_smul c (H1Space.ofFunction _ _ (h1ZeroTestFunctions.hasH1GradientOn f hD)),
      H1Space.coeFn_ofFunction _ _ (h1ZeroTestFunctions.hasH1GradientOn f hD)] with x h1 h2 h3
    rw [h3] at h2
    exact h1.trans h2.symm

/-- The H¹ closure of actual smooth compactly supported interior functions. -/
def h1ZeroSubmodule {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) :
    Submodule ℝ (H1Space D) := (h1ZeroTestFunctions.toH1Space hD).range.topologicalClosure

/-- The standard space H¹₀, with the inherited genuine H¹ Hilbert norm. -/
abbrev H1ZeroSpace {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) :=
  ↥(h1ZeroSubmodule hD)

instance h1ZeroSpaceComplete {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) :
    CompleteSpace (H1ZeroSpace hD) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- Support containment identifies the global and restricted Lᵖ norms. -/
lemma lpNorm_restrict_eq_of_tsupport_subset {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : MeasurableSet D)
    {f : EuclideanSpace ℝ (Fin n) → F} {p : ℝ≥0∞}
    (hf : MemLp f p volume) (hs : tsupport f ⊆ D) :
    lpNorm f p (volume.restrict D) = lpNorm f p volume := by
  rw [← toReal_eLpNorm,
    ← toReal_eLpNorm, ← eLpNorm_indicator_eq_eLpNorm_restrict hD,
    indicator_eq_self.mpr ((subset_tsupport f).trans hs)]

/-- Finite-volume Hölder from L⁶ to L². -/
lemma lpNorm_two_le_lpNorm_six_mul_measure {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ} (hf : MemLp f 6 μ) :
    lpNorm f 2 μ ≤ lpNorm f 6 μ * (μ univ).toReal ^ (1 / 3 : ℝ) := by
  have hm := hf.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 6)
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num : (2 : ℝ≥0∞) ≤ 6) hf.aestronglyMeasurable
  norm_num only [ENNReal.toReal_ofNat, show (1 / (2 : ℝ) - 1 / 6) = 1 / 3 by norm_num] at h
  have hr := ENNReal.toReal_mono (by finiteness) h
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    toReal_eLpNorm, toReal_eLpNorm] using hr

/-- The zero-boundary Poincaré estimate first holds on genuine interior tests. -/
lemma h1ZeroTestFunctions.poincare {D : Set AmbientSpace} (hD : IsOpen D)
    (hvol : volume D < ∞) (f : h1ZeroTestFunctions D) :
    ‖(h1ZeroTestFunctions.toH1Space hD f).toLp‖ ≤
      (4 * (volume D).toReal ^ (1 / 3 : ℝ)) *
        ‖(h1ZeroTestFunctions.toH1Space hD f).gradientLp‖ := by
  let : IsFiniteMeasure (volume.restrict D) := ⟨by simpa using hvol⟩
  have hf := h1ZeroTestFunctions.hasH1GradientOn f isOpen_univ
  have h6 := hf.memLp_six
  have h6D := h6.mono_measure (Measure.restrict_le_self (s := D))
  have hhold := lpNorm_two_le_lpNorm_six_mul_measure h6D
  rw [Measure.restrict_apply_univ,
    lpNorm_restrict_eq_of_tsupport_subset hD.measurableSet h6 f.property.2.2] at hhold
  have hgrad : MemLp (gradient f.val) 2 volume := by
    simpa only [Measure.restrict_univ] using hf.memLp_gradient
  have heq := lpNorm_restrict_eq_of_tsupport_subset hD.measurableSet hgrad
    ((tsupport_gradient_subset f.val).trans f.property.2.2)
  change ‖(h1ZeroTestFunctions.hasH1GradientOn f hD).memLp_function.toLp f.val‖ ≤
    _ * ‖(h1ZeroTestFunctions.hasH1GradientOn f hD).memLp_gradient.toLp (gradient f.val)‖
  rw [Lp.norm_toLp, Lp.norm_toLp,
    toReal_eLpNorm,
    toReal_eLpNorm, heq]
  exact hhold.trans (by
    have h := mul_le_mul_of_nonneg_right hf.lpNorm_six_le
      (by positivity : 0 ≤ (volume D).toReal ^ (1 / 3 : ℝ))
    nlinarith only [h])

/-- Poincaré extends to the defining H¹ closure of the test functions. -/
theorem H1ZeroSpace.poincare {D : Set AmbientSpace} (hD : IsOpen D)
    (hvol : volume D < ∞) (u : H1ZeroSpace hD) :
    ‖u.val.toLp‖ ≤ (4 * (volume D).toReal ^ (1 / 3 : ℝ)) * ‖u.val.gradientLp‖ := by
  have hclosed : IsClosed {v : H1Space D | ‖v.toLp‖ ≤
      (4 * (volume D).toReal ^ (1 / 3 : ℝ)) * ‖v.gradientLp‖} :=
    isClosed_le H1Space.toLpCLM.continuous.norm
      (continuous_const.mul H1Space.gradientCLM.continuous.norm)
  apply closure_minimal (s := ((h1ZeroTestFunctions.toH1Space hD).range : Set (H1Space D)))
    (t := {v | ‖v.toLp‖ ≤ (4 * (volume D).toReal ^ (1 / 3 : ℝ)) * ‖v.gradientLp‖})
    (by rintro v ⟨f, rfl⟩; exact h1ZeroTestFunctions.poincare hD hvol f) hclosed u.property

/-- The Dirichlet gradient is coercive in the actual inherited H¹ norm. -/
theorem H1ZeroSpace.norm_le_gradient {D : Set AmbientSpace} (hD : IsOpen D)
    (hvol : volume D < ∞) (u : H1ZeroSpace hD) :
    ‖u‖ ≤ (4 * (volume D).toReal ^ (1 / 3 : ℝ) + 1) * ‖u.val.gradientLp‖ := by
  have h := u.val.norm_le_sum
  have hp := H1ZeroSpace.poincare hD hvol u
  change ‖u.val‖ ≤ _
  nlinarith only [h, hp]

/-- Every boundary trace that agrees with continuous representatives vanishes
on H¹₀, by its defining closure and continuity. -/
theorem h1ZeroSubmodule_le_trace_ker {k : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hD : IsOpen D)
    (T : H1Space D →L[ℝ]
      Lp ℝ 2 ((Measure.euclideanHausdorffMeasure k).restrict (frontier D)))
    (hT : ∀ f G (hf : HasH1GradientOn f G D), Continuous f →
      ∀ᵐ x ∂(Measure.euclideanHausdorffMeasure k).restrict (frontier D),
        T (H1Space.ofFunction f G hf) x = f x) :
    h1ZeroSubmodule hD ≤ T.ker := by
  apply Submodule.topologicalClosure_minimal _ ?_ T.isClosed_ker
  rintro u ⟨f, rfl⟩
  change T (h1ZeroTestFunctions.toH1Space hD f) = 0
  apply Lp.ext
  filter_upwards [hT f.val (gradient f.val)
      (h1ZeroTestFunctions.hasH1GradientOn f hD) f.property.1.continuous,
    ae_restrict_mem (isClosed_frontier (s := D)).measurableSet,
    Lp.coeFn_zero ℝ 2 ((Measure.euclideanHausdorffMeasure k).restrict (frontier D))]
    with x htx hxf hx0
  have hz : f.val x = 0 := by
    by_contra hne
    have hxD := f.property.2.2 ((subset_tsupport f.val) hne)
    exact hxf.2 (hD.interior_eq.symm ▸ hxD)
  exact htx.trans (hz.trans hx0.symm)

end LiquidDrop
