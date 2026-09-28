import NoCompromise.Elliptic.VariationalHilbert
import NoCompromise.Sobolev.H1Zero

/-!
# The weak Dirichlet problem

The affine boundary constraint is the prescribed H¹ extension plus the genuine
H¹ closure of smooth interior test functions. Coercivity is proved from Sobolev,
and closed-range Hilbert representation constructs the minimizer.
-/

noncomputable section
open MeasureTheory Set InnerProductSpace
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The Dirichlet energy, with the sign convention Δz=f. -/
def dirichletEnergy {D : Set AmbientSpace} (f : Lp ℝ 2 (volume.restrict D))
    (z : H1Space D) : ℝ := (1 / 2 : ℝ) * ‖z.gradientLp‖ ^ 2 + inner ℝ f z.toLp

lemma dirichletEnergy_eq_integrals {D : Set AmbientSpace}
    (f : Lp ℝ 2 (volume.restrict D)) (z : H1Space D) :
    dirichletEnergy f z = (1 / 2 : ℝ) * (∫ x in D, ‖z.gradientLp x‖ ^ 2) +
      ∫ x in D, f x * z x := by
  rw [dirichletEnergy, ← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq, Real.inner_apply]

/-- A weak solution with the prescribed affine H¹₀ boundary condition. -/
def IsWeakDirichletSolution {D : Set AmbientSpace} (hD : IsOpen D)
    (f : Lp ℝ 2 (volume.restrict D)) (g z : H1Space D) : Prop :=
  z - g ∈ h1ZeroSubmodule hD ∧ ∀ φ : H1ZeroSpace hD,
    inner ℝ z.gradientLp φ.val.gradientLp = -inner ℝ f φ.val.toLp

lemma IsWeakDirichletSolution.test_eq {D : Set AmbientSpace} {hD : IsOpen D}
    {f : Lp ℝ 2 (volume.restrict D)} {g z : H1Space D}
    (hz : IsWeakDirichletSolution hD f g z) (φ : H1ZeroSpace hD) :
    (∫ x in D, inner ℝ (z.gradientLp x) (φ.val.gradientLp x)) =
      -(∫ x in D, f x * φ.val x) := by
  simpa only [L2.inner_def, Real.inner_apply] using hz.2 φ

/-- The bounded functional for the zero-boundary correction to the given extension. -/
def dirichletCorrectionFunctional {D : Set AmbientSpace} (hD : IsOpen D)
    (f : Lp ℝ 2 (volume.restrict D)) (g : H1Space D) : H1ZeroSpace hD →L[ℝ] ℝ :=
  -((innerSL ℝ f).comp (H1Space.toLpCLM.comp (h1ZeroSubmodule hD).subtypeL)) -
    (innerSL ℝ g.gradientLp).comp (H1Space.gradientCLM.comp (h1ZeroSubmodule hD).subtypeL)

lemma dirichletCorrectionFunctional_apply {D : Set AmbientSpace} (hD : IsOpen D)
    (f : Lp ℝ 2 (volume.restrict D)) (g : H1Space D) (u : H1ZeroSpace hD) :
    dirichletCorrectionFunctional hD f g u =
      -inner ℝ f u.val.toLp - inner ℝ g.gradientLp u.val.gradientLp := rfl

lemma norm_dirichletCorrectionFunctional_le {D : Set AmbientSpace} (hD : IsOpen D)
    (f : Lp ℝ 2 (volume.restrict D)) (g : H1Space D) :
    ‖dirichletCorrectionFunctional hD f g‖ ≤ ‖f‖ + ‖g.gradientLp‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro u
  rw [dirichletCorrectionFunctional_apply]
  calc
    _ ≤ ‖inner ℝ f u.val.toLp‖ + ‖inner ℝ g.gradientLp u.val.gradientLp‖ := by
      simpa only [norm_neg] using norm_sub_le (-inner ℝ f u.val.toLp)
        (inner ℝ g.gradientLp u.val.gradientLp)
    _ ≤ ‖f‖ * ‖u.val.toLp‖ + ‖g.gradientLp‖ * ‖u.val.gradientLp‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ (‖f‖ + ‖g.gradientLp‖) * ‖u‖ := by
      have h1 := mul_le_mul_of_nonneg_left u.val.norm_toLp_le (norm_nonneg f)
      have h2 := mul_le_mul_of_nonneg_left u.val.norm_gradientLp_le (norm_nonneg g.gradientLp)
      change _ ≤ (‖f‖ + ‖g.gradientLp‖) * ‖u.val‖
      nlinarith only [h1, h2]

/-- Expanding around the prescribed extension gives the coercive correction energy. -/
lemma dirichletEnergy_add_correction {D : Set AmbientSpace} (hD : IsOpen D)
    (f : Lp ℝ 2 (volume.restrict D)) (g : H1Space D) (u : H1ZeroSpace hD) :
    dirichletEnergy f (g + u.val) = dirichletEnergy f g +
      ((1 / 2 : ℝ) * ‖u.val.gradientLp‖ ^ 2 - dirichletCorrectionFunctional hD f g u) := by
  rw [dirichletEnergy, dirichletEnergy, H1Space.gradientLp_add, H1Space.toLp_add,
    norm_add_sq_real, inner_add_right, dirichletCorrectionFunctional_apply]
  ring

/-- Blueprint `prop:weak-dirichlet`: unique minimization and weak solvability on
`g + H¹₀(D)`. Finite volume and openness suffice for the spatial Dirichlet problem. -/
theorem exists_weak_dirichlet {D : Set AmbientSpace} (hD : IsOpen D)
    (hvol : volume D < ∞) (f : Lp ℝ 2 (volume.restrict D)) (g : H1Space D) :
    ∃ z : H1Space D, IsWeakDirichletSolution hD f g z ∧
      (∀ v : H1Space D, v - g ∈ h1ZeroSubmodule hD →
        dirichletEnergy f z ≤ dirichletEnergy f v) ∧
      (∀ v : H1Space D, v - g ∈ h1ZeroSubmodule hD →
        (dirichletEnergy f v ≤ dirichletEnergy f z ↔ v = z)) ∧
      (∀ v : H1Space D, IsWeakDirichletSolution hD f g v → v = z) ∧
      ‖z - g‖ ≤ (4 * (volume D).toReal ^ (1 / 3 : ℝ) + 1) ^ 2 *
        (‖f‖ + ‖g.gradientLp‖) := by
  let A := H1Space.gradientCLM.comp (h1ZeroSubmodule hD).subtypeL
  let C := 4 * (volume D).toReal ^ (1 / 3 : ℝ) + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hA (u : H1ZeroSpace hD) : ‖u‖ ≤ C * ‖A u‖ := H1ZeroSpace.norm_le_gradient hD hvol u
  let ℓ := dirichletCorrectionFunctional hD f g
  obtain ⟨u, hu, hmin, huniq, hgrad, hnorm⟩ :=
    exists_unique_coercive_quadratic_minimizer A hC hA ℓ
  let z := g + u.val
  have hz : IsWeakDirichletSolution hD f g z := by
    refine ⟨by simpa only [z, add_sub_cancel_left] using u.property, fun φ => ?_⟩
    have h := hu φ
    change inner ℝ u.val.gradientLp φ.val.gradientLp =
      -inner ℝ f φ.val.toLp - inner ℝ g.gradientLp φ.val.gradientLp at h
    change inner ℝ (g + u.val).gradientLp φ.val.gradientLp = _
    rw [H1Space.gradientLp_add, inner_add_left]
    linarith
  have hev (v : H1Space D) (hv : v - g ∈ h1ZeroSubmodule hD) :
      v = g + (⟨v - g, hv⟩ : H1ZeroSpace hD).val := by simp
  have hez := dirichletEnergy_add_correction hD f g u
  refine ⟨z, hz, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have he := dirichletEnergy_add_correction hD f g (⟨v - g, hv⟩ : H1ZeroSpace hD)
    rw [← hev v hv] at he
    change dirichletEnergy f (g + u.val) ≤ _
    rw [hez, he]
    exact add_le_add le_rfl (hmin ⟨v - g, hv⟩)
  · intro v hv
    have he := dirichletEnergy_add_correction hD f g (⟨v - g, hv⟩ : H1ZeroSpace hD)
    rw [← hev v hv] at he
    change (dirichletEnergy f v ≤ dirichletEnergy f (g + u.val)) ↔ _
    rw [hez, he, add_le_add_iff_left]
    change ((1 / 2 : ℝ) * ‖A ⟨v - g, hv⟩‖ ^ 2 - ℓ ⟨v - g, hv⟩ ≤
      (1 / 2 : ℝ) * ‖A u‖ ^ 2 - ℓ u) ↔ _
    rw [huniq]
    constructor
    · intro h
      have hval := congrArg Subtype.val h
      dsimp only at hval
      change v = g + u.val
      rw [← hval]
      abel
    · intro h
      apply Subtype.ext
      change v - g = u.val
      rw [h]
      simp [z]
  · intro v hv
    let w : H1ZeroSpace hD := ⟨v - g, hv.1⟩
    have hw (φ : H1ZeroSpace hD) : inner ℝ (A w) (A φ) = ℓ φ := by
      have h := hv.2 φ
      change inner ℝ (H1Space.gradientCLM (v - g)) φ.val.gradientLp = _
      rw [map_sub, inner_sub_left]
      change inner ℝ v.gradientLp φ.val.gradientLp -
        inner ℝ g.gradientLp φ.val.gradientLp = _
      rw [h]
      rfl
    obtain ⟨q, hq, hunique⟩ := exists_unique_gradient_riesz A hC hA ℓ
    have hwu : w = u := (hunique w hw).trans (hunique u hu).symm
    have hval := congrArg Subtype.val hwu
    change v - g = u.val at hval
    change v = g + u.val
    rw [← hval]
    abel
  · change ‖g + u.val - g‖ ≤ _
    rw [add_sub_cancel_left]
    exact hnorm.trans (mul_le_mul_of_nonneg_left
      (norm_dirichletCorrectionFunctional_le hD f g) (sq_nonneg C))

end LiquidDrop
