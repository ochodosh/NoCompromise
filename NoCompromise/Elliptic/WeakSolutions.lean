import NoCompromise.Elliptic.WeakDirichlet
import NoCompromise.Sobolev.H1MeanZero

/-!
# The weak Neumann problem

The boundary functional uses the constructed L² trace on the actual normalized
Hausdorff boundary measure. The compatibility condition annihilates constants;
Hilbert representation on the closed mean-zero space yields a solution, and the
weak equation then extends to every H¹ test. Dirichlet solvability is imported
from the independently proved affine H¹₀ minimization theorem.
-/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The constructed trace, fixed once for a bounded open Lipschitz domain. -/
def h1BoundaryTrace {D : Set AmbientSpace} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    H1Space D →L[ℝ] Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D)) :=
  (exists_h1_trace_operator hD hbD hL).choose

lemma h1BoundaryTrace_eq_restrict {D : Set AmbientSpace} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D)
    (f : AmbientSpace → ℝ) (G : AmbientSpace → AmbientSpace)
    (hf : HasH1GradientOn f G D) (hc : Continuous f) :
    ⇑(h1BoundaryTrace hD hbD hL (H1Space.ofFunction f G hf)) =ᵐ[
      (hausdorffMeasure2 3).restrict (frontier D)] f :=
  (exists_h1_trace_operator hD hbD hL).choose_spec.choose_spec.2.2 f G hf hc

lemma h1BoundaryTrace_const {D : Set AmbientSpace} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) (c : ℝ) :
    ⇑(h1BoundaryTrace hD hbD hL (H1Space.const hD hbD.measure_lt_top c)) =ᵐ[
      (hausdorffMeasure2 3).restrict (frontier D)] fun _ => c :=
  h1BoundaryTrace_eq_restrict hD hbD hL _ _ _ continuous_const

/-- Scalar L² pairing with a constant is the actual volume or surface integral. -/
lemma inner_lp_eq_const_mul_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g : Lp ℝ 2 μ) {c : ℝ} (hg : ⇑g =ᵐ[μ] fun _ => c) :
    inner ℝ f g = c * ∫ x, f x ∂μ := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, f x * c ∂μ := integral_congr_ae (by
      filter_upwards [hg] with x hx
      simp only [Real.inner_apply, hx])
    _ = _ := by rw [integral_mul_const]; ring

/-- L² boundary data are integrable: the trace of the constant one supplies the
other L² factor. This also checks that the compatibility integrals are genuine. -/
lemma integrable_h1_boundary_data {D : Set AmbientSpace} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D)
    (h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))) :
    Integrable h ((hausdorffMeasure2 3).restrict (frontier D)) := by
  have hi := L2.integrable_inner (𝕜 := ℝ) h
    (h1BoundaryTrace hD hbD hL (H1Space.const hD hbD.measure_lt_top 1))
  apply hi.congr
  filter_upwards [h1BoundaryTrace_const hD hbD hL 1] with x hx
  simp only [Real.inner_apply, hx, mul_one]

/-- The forcing functional, with Δz=f and outward normal derivative h. -/
def neumannFunctional {D : Set AmbientSpace} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D)
    (f : Lp ℝ 2 (volume.restrict D))
    (h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))) : H1Space D →L[ℝ] ℝ :=
  -((innerSL ℝ f).comp H1Space.toLpCLM) +
    (innerSL ℝ h).comp (h1BoundaryTrace hD hbD hL)

lemma neumannFunctional_apply {D : Set AmbientSpace} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D)
    (f : Lp ℝ 2 (volume.restrict D))
    (h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))) (u : H1Space D) :
    neumannFunctional hD hbD hL f h u =
      -inner ℝ f u.toLp + inner ℝ h (h1BoundaryTrace hD hbD hL u) := rfl

lemma norm_neumannFunctional_le {D : Set AmbientSpace} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D)
    (f : Lp ℝ 2 (volume.restrict D))
    (h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))) :
    ‖neumannFunctional hD hbD hL f h‖ ≤
      ‖f‖ + ‖h‖ * ‖h1BoundaryTrace hD hbD hL‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  rw [neumannFunctional_apply]
  calc
    _ ≤ ‖inner ℝ f u.toLp‖ + ‖inner ℝ h (h1BoundaryTrace hD hbD hL u)‖ := by
      simpa only [norm_neg] using norm_add_le (-inner ℝ f u.toLp)
        (inner ℝ h (h1BoundaryTrace hD hbD hL u))
    _ ≤ ‖f‖ * ‖u.toLp‖ + ‖h‖ * ‖h1BoundaryTrace hD hbD hL u‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ _ := by
      have h1 := mul_le_mul_of_nonneg_left u.norm_toLp_le (norm_nonneg f)
      have h2 := mul_le_mul_of_nonneg_left ((h1BoundaryTrace hD hbD hL).le_opNorm u)
        (norm_nonneg h)
      nlinarith only [h1, h2]

/-- The global Neumann compatibility condition is exactly the constant obstruction. -/
lemma neumannFunctional_const_eq_zero {D : Set AmbientSpace} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D)
    (f : Lp ℝ 2 (volume.restrict D))
    (h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D)))
    (hcompat : (∫ x in D, f x) = ∫ x, h x ∂(hausdorffMeasure2 3).restrict (frontier D))
    (c : ℝ) : neumannFunctional hD hbD hL f h (H1Space.const hD hbD.measure_lt_top c) = 0 := by
  rw [neumannFunctional_apply,
    inner_lp_eq_const_mul_integral f _ (H1Space.coeFn_const hD hbD.measure_lt_top c),
    inner_lp_eq_const_mul_integral h _ (h1BoundaryTrace_const hD hbD hL c), hcompat]
  ring

/-- The Neumann energy on genuine H¹ classes. -/
def neumannEnergy {D : Set AmbientSpace} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D)
    (f : Lp ℝ 2 (volume.restrict D))
    (h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))) (z : H1Space D) : ℝ :=
  (1 / 2 : ℝ) * ‖z.gradientLp‖ ^ 2 - neumannFunctional hD hbD hL f h z

lemma neumannEnergy_eq_integrals {D : Set AmbientSpace} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D)
    (f : Lp ℝ 2 (volume.restrict D))
    (h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))) (z : H1Space D) :
    neumannEnergy hD hbD hL f h z = (1 / 2 : ℝ) * (∫ x in D, ‖z.gradientLp x‖ ^ 2) +
      (∫ x in D, f x * z x) -
      ∫ x, h x * h1BoundaryTrace hD hbD hL z x
        ∂(hausdorffMeasure2 3).restrict (frontier D) := by
  rw [neumannEnergy, neumannFunctional_apply, ← real_inner_self_eq_norm_sq,
    L2.inner_def, L2.inner_def, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq, Real.inner_apply]
  ring

/-- The weak equation is imposed on every H¹ test, including constants. -/
def IsWeakNeumannSolution {D : Set AmbientSpace} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D)
    (f : Lp ℝ 2 (volume.restrict D))
    (h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))) (z : H1Space D) : Prop :=
  ∀ φ : H1Space D, inner ℝ z.gradientLp φ.gradientLp = neumannFunctional hD hbD hL f h φ

lemma IsWeakNeumannSolution.test_eq {D : Set AmbientSpace} {hD : IsOpen D}
    {hbD : Bornology.IsBounded D} {hL : HasLipschitzBoundary D}
    {f : Lp ℝ 2 (volume.restrict D)}
    {h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))} {z : H1Space D}
    (hz : IsWeakNeumannSolution hD hbD hL f h z) (φ : H1Space D) :
    (∫ x in D, inner ℝ (z.gradientLp x) (φ.gradientLp x)) =
      -(∫ x in D, f x * φ x) +
        ∫ x, h x * h1BoundaryTrace hD hbD hL φ x
          ∂(hausdorffMeasure2 3).restrict (frontier D) := by
  simpa only [neumannFunctional_apply, L2.inner_def, Real.inner_apply] using hz φ

lemma IsWeakNeumannSolution.energy_gap {D : Set AmbientSpace} {hD : IsOpen D}
    {hbD : Bornology.IsBounded D} {hL : HasLipschitzBoundary D}
    {f : Lp ℝ 2 (volume.restrict D)}
    {h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))} {z : H1Space D}
    (hz : IsWeakNeumannSolution hD hbD hL f h z) (v : H1Space D) :
    neumannEnergy hD hbD hL f h v = neumannEnergy hD hbD hL f h z +
      (1 / 2 : ℝ) * ‖(v - z).gradientLp‖ ^ 2 :=
  quadratic_energy_gap_of_gradient_riesz H1Space.gradientCLM
    (neumannFunctional hD hbD hL f h) hz v

/-- Blueprint `prop:weak-neumann`: actual weak solvability, global minimization,
uniqueness modulo constants, unique mean-zero normalization, and an energy bound.
The compatibility condition is stated using the actual volume and boundary integrals. -/
theorem exists_weak_neumann {D : Set AmbientSpace} (hD : IsOpen D)
    (hcD : IsPreconnected D) (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Lp ℝ 2 (volume.restrict D))
      (h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))),
      (∫ x in D, f x) = (∫ x, h x ∂(hausdorffMeasure2 3).restrict (frontier D)) →
      ∃ z : H1Space D, (∫ x in D, z x) = 0 ∧ IsWeakNeumannSolution hD hbD hL f h z ∧
        (∀ v : H1Space D, neumannEnergy hD hbD hL f h z ≤ neumannEnergy hD hbD hL f h v) ∧
        (∀ v : H1Space D, IsWeakNeumannSolution hD hbD hL f h v →
          ∃ c : ℝ, v = z + H1Space.const hD hbD.measure_lt_top c) ∧
        (∀ v : H1Space D, (∫ x in D, v x) = 0 →
          IsWeakNeumannSolution hD hbD hL f h v → v = z) ∧
        ‖z‖ ≤ C * (‖f‖ + ‖h‖) := by
  obtain ⟨K, hK, hcoerce⟩ := exists_h1_meanZero_coercivity hD hcD hbD hL
  let T := h1BoundaryTrace hD hbD hL
  refine ⟨K ^ 2 * (1 + ‖T‖), by positivity, fun f h hcompat => ?_⟩
  let M := h1MeanZeroSubmodule hbD.measure_lt_top
  let A := H1Space.gradientCLM.comp M.subtypeL
  let ℓ := (neumannFunctional hD hbD hL f h).comp M.subtypeL
  obtain ⟨u, hu, hmin, huniq, hgrad, hnorm⟩ :=
    exists_unique_coercive_quadratic_minimizer A hK.le hcoerce ℓ
  have hzero (c : ℝ) := neumannFunctional_const_eq_zero hD hbD hL f h hcompat c
  have hz : IsWeakNeumannSolution hD hbD hL f h u.val := by
    intro φ
    let φ₀ : H1MeanZeroSpace hbD.measure_lt_top :=
      ⟨φ.subMean hD hbD.measure_lt_top, φ.subMean_mem hD hbD.measure_lt_top⟩
    have ht := hu φ₀
    change inner ℝ u.val.gradientLp (φ.subMean hD hbD.measure_lt_top).gradientLp =
      neumannFunctional hD hbD hL f h (φ.subMean hD hbD.measure_lt_top) at ht
    rw [H1Space.gradientLp_subMean] at ht
    simpa only [H1Space.subMean, map_sub, hzero, sub_zero] using ht
  have huniqmod (v : H1Space D) (hv : IsWeakNeumannSolution hD hbD hL f h v) :
      ∃ c : ℝ, v = u.val + H1Space.const hD hbD.measure_lt_top c := by
    let w := v - u.val
    have hw : w.gradientLp = 0 := by
      have hvw := hv w
      have huw := hz w
      have heq : w.gradientLp = v.gradientLp - u.val.gradientLp :=
        H1Space.gradientCLM.map_sub v u.val
      apply norm_eq_zero.mp
      have hi : ‖w.gradientLp‖ ^ 2 = 0 := by
        rw [← real_inner_self_eq_norm_sq, heq, inner_sub_left]
        rw [← heq]
        linarith
      nlinarith [norm_nonneg w.gradientLp]
    let w₀ : H1MeanZeroSpace hbD.measure_lt_top :=
      ⟨w.subMean hD hbD.measure_lt_top, w.subMean_mem hD hbD.measure_lt_top⟩
    have hnorm0 := hcoerce w₀
    change ‖w.subMean hD hbD.measure_lt_top‖ ≤
      K * ‖(w.subMean hD hbD.measure_lt_top).gradientLp‖ at hnorm0
    rw [H1Space.gradientLp_subMean, hw, norm_zero, mul_zero] at hnorm0
    have heq : w.subMean hD hbD.measure_lt_top = 0 :=
      norm_eq_zero.mp (le_antisymm hnorm0 (norm_nonneg _))
    refine ⟨⨍ x in D, w x, ?_⟩
    have hc : w = H1Space.const hD hbD.measure_lt_top (⨍ x in D, w x) := sub_eq_zero.mp heq
    change v = u.val + _
    rw [← hc]
    dsimp [w]
    abel
  refine ⟨u.val, (mem_h1MeanZeroSubmodule_iff _ _).mp u.property, hz,
    fun v => ?_, huniqmod, ?_, ?_⟩
  · rw [hz.energy_gap v]
    nlinarith [sq_nonneg ‖(v - u.val).gradientLp‖]
  · intro v hvmean hv
    let v₀ : H1MeanZeroSpace hbD.measure_lt_top :=
      ⟨v, (mem_h1MeanZeroSubmodule_iff _ _).mpr hvmean⟩
    have hv₀ (φ : H1MeanZeroSpace hbD.measure_lt_top) : inner ℝ (A v₀) (A φ) = ℓ φ :=
      hv φ.val
    obtain ⟨q, hq, hquniq⟩ := exists_unique_gradient_riesz A hK.le hcoerce ℓ
    exact congrArg Subtype.val ((hquniq v₀ hv₀).trans (hquniq u hu).symm)
  · have hℓ : ‖ℓ‖ ≤ ‖f‖ + ‖h‖ * ‖T‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro v
      exact ((neumannFunctional hD hbD hL f h).le_opNorm v.val).trans
        (mul_le_mul_of_nonneg_right (norm_neumannFunctional_le hD hbD hL f h) (norm_nonneg _))
    have hb := mul_le_mul_of_nonneg_left hℓ (sq_nonneg K)
    change ‖u.val‖ ≤ _
    apply hnorm.trans (hb.trans ?_)
    have hh : ‖f‖ + ‖h‖ * ‖T‖ ≤ (1 + ‖T‖) * (‖f‖ + ‖h‖) := by
      nlinarith [mul_nonneg (norm_nonneg T) (norm_nonneg f), norm_nonneg h]
    nlinarith only [mul_le_mul_of_nonneg_left hh (sq_nonneg K)]

/-- The constructed Dirichlet solution has the actual prescribed boundary trace. -/
lemma IsWeakDirichletSolution.trace_eq {D : Set AmbientSpace} {hD : IsOpen D}
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D)
    {f : Lp ℝ 2 (volume.restrict D)} {g z : H1Space D}
    (hz : IsWeakDirichletSolution hD f g z) :
    h1BoundaryTrace hD hbD hL z = h1BoundaryTrace hD hbD hL g := by
  have hker := h1ZeroSubmodule_le_trace_ker hD (h1BoundaryTrace hD hbD hL)
    (fun f G hf hc => h1BoundaryTrace_eq_restrict hD hbD hL f G hf hc) hz.1
  change h1BoundaryTrace hD hbD hL (z - g) = 0 at hker
  rwa [map_sub, sub_eq_zero] at hker

/-- The Dirichlet Euler equation characterizes minimizers on the exact affine
closure space used in the blueprint. -/
theorem isWeakDirichletSolution_iff_minimizer {D : Set AmbientSpace} (hD : IsOpen D)
    (hvol : volume D < ∞) (f : Lp ℝ 2 (volume.restrict D)) (g z : H1Space D) :
    IsWeakDirichletSolution hD f g z ↔ z - g ∈ h1ZeroSubmodule hD ∧
      ∀ v : H1Space D, v - g ∈ h1ZeroSubmodule hD →
        dirichletEnergy f z ≤ dirichletEnergy f v := by
  obtain ⟨u, hu, hmin, hminuniq, huniq, _⟩ := exists_weak_dirichlet hD hvol f g
  constructor
  · intro hz
    have heq := huniq z hz
    exact ⟨hz.1, by simpa only [heq] using hmin⟩
  · rintro ⟨hzg, hzmin⟩
    have heq := (hminuniq z hzg).mp (hzmin u hu.1)
    simpa only [heq] using hu

/-- Testing the Neumann equation with the constant one proves necessity of the
global compatibility condition, with the same volume and surface measures. -/
lemma IsWeakNeumannSolution.compatibility {D : Set AmbientSpace} {hD : IsOpen D}
    {hbD : Bornology.IsBounded D} {hL : HasLipschitzBoundary D}
    {f : Lp ℝ 2 (volume.restrict D)}
    {h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))} {z : H1Space D}
    (hz : IsWeakNeumannSolution hD hbD hL f h z) :
    (∫ x in D, f x) = ∫ x, h x ∂(hausdorffMeasure2 3).restrict (frontier D) := by
  have ht := hz (H1Space.const hD hbD.measure_lt_top 1)
  rw [H1Space.gradientLp_const, inner_zero_right, neumannFunctional_apply,
    inner_lp_eq_const_mul_integral f _ (H1Space.coeFn_const hD hbD.measure_lt_top 1),
    inner_lp_eq_const_mul_integral h _ (h1BoundaryTrace_const hD hbD hL 1)] at ht
  linarith

/-- Adding any constant preserves the full Neumann weak equation. -/
lemma IsWeakNeumannSolution.add_const {D : Set AmbientSpace} {hD : IsOpen D}
    {hbD : Bornology.IsBounded D} {hL : HasLipschitzBoundary D}
    {f : Lp ℝ 2 (volume.restrict D)}
    {h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))} {z : H1Space D}
    (hz : IsWeakNeumannSolution hD hbD hL f h z) (c : ℝ) :
    IsWeakNeumannSolution hD hbD hL f h (z + H1Space.const hD hbD.measure_lt_top c) := by
  intro φ
  simpa only [H1Space.gradientLp_add, H1Space.gradientLp_const, add_zero] using hz φ

/-- Every weak Neumann solution minimizes the actual energy on all of H¹. -/
lemma IsWeakNeumannSolution.isMinimizer {D : Set AmbientSpace} {hD : IsOpen D}
    {hbD : Bornology.IsBounded D} {hL : HasLipschitzBoundary D}
    {f : Lp ℝ 2 (volume.restrict D)}
    {h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D))} {z : H1Space D}
    (hz : IsWeakNeumannSolution hD hbD hL f h z) (v : H1Space D) :
    neumannEnergy hD hbD hL f h z ≤ neumannEnergy hD hbD hL f h v := by
  rw [hz.energy_gap v]
  nlinarith [sq_nonneg ‖(v - z).gradientLp‖]

/-- With compatibility, minimizing the Neumann energy is equivalent to the full
weak equation. Combined with the constructed normalized solution, this gives
uniqueness of minimizers modulo constants as well as uniqueness of solutions. -/
theorem isWeakNeumannSolution_iff_minimizer {D : Set AmbientSpace} (hD : IsOpen D)
    (hcD : IsPreconnected D) (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D)
    (f : Lp ℝ 2 (volume.restrict D))
    (h : Lp ℝ 2 ((hausdorffMeasure2 3).restrict (frontier D)))
    (hcompat : (∫ x in D, f x) = ∫ x, h x ∂(hausdorffMeasure2 3).restrict (frontier D))
    (z : H1Space D) :
    IsWeakNeumannSolution hD hbD hL f h z ↔
      ∀ v : H1Space D, neumannEnergy hD hbD hL f h z ≤ neumannEnergy hD hbD hL f h v := by
  constructor
  · exact fun hz => hz.isMinimizer
  · intro hzmin
    obtain ⟨C, hC, hsolve⟩ := exists_weak_neumann hD hcD hbD hL
    obtain ⟨u, _, hu, _⟩ := hsolve f h hcompat
    have he := hu.energy_gap z
    have hm := hzmin u
    have hg : (z - u).gradientLp = 0 := by
      apply norm_eq_zero.mp
      nlinarith [sq_nonneg ‖(z - u).gradientLp‖, norm_nonneg (z - u).gradientLp]
    have hsub : z.gradientLp - u.gradientLp = 0 := by
      change H1Space.gradientCLM z - H1Space.gradientCLM u = _
      rwa [← map_sub]
    have heq := sub_eq_zero.mp hsub
    intro φ
    rw [heq]
    exact hu φ

end LiquidDrop
