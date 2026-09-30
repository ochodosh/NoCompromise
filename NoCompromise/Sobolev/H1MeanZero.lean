module

public import NoCompromise.Sobolev.PoincareTrace

@[expose] public section

/-!
# The normalized Sobolev space for Neumann problems

The mean-zero space is the closed kernel of the actual volume integral. Constants
and subtraction of the mean are represented by genuine weak-gradient pairs.
The proved Poincaré theorem supplies coercivity on this closed Hilbert space.
-/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma hasH1GradientOn_const_of_finite_volume {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (hvol : volume D < ∞) (c : ℝ) :
    HasH1GradientOn (fun _ => c) (fun _ => 0) D := by
  let : IsFiniteMeasure (volume.restrict D) := ⟨by simpa using hvol⟩
  refine ⟨?_, memLp_const c, memLp_const (0 : EuclideanSpace ℝ (Fin n))⟩
  simpa only [gradient_fun_const'] using
    hasWeakGradientOn_of_contDiffOn hD (contDiff_const (c := c)).contDiffOn

/-- The H¹ class of a constant, with its zero weak gradient. -/
def H1Space.const {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (hD : IsOpen D) (hvol : volume D < ∞) (c : ℝ) : H1Space D :=
  H1Space.ofFunction (fun _ => c) (fun _ => 0) (hasH1GradientOn_const_of_finite_volume hD hvol c)

lemma H1Space.coeFn_const {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (hD : IsOpen D) (hvol : volume D < ∞) (c : ℝ) :
    ⇑(H1Space.const hD hvol c) =ᵐ[volume.restrict D] fun _ => c :=
  H1Space.coeFn_ofFunction _ _ _

@[simp] lemma H1Space.gradientLp_const {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (hD : IsOpen D) (hvol : volume D < ∞) (c : ℝ) :
    (H1Space.const hD hvol c).gradientLp = 0 := by
  apply Lp.ext
  exact (H1Space.gradientLp_ofFunction _ _ _).trans (Lp.coeFn_zero _ _ _).symm

@[simp] lemma H1Space.const_zero {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (hD : IsOpen D) (hvol : volume D < ∞) : H1Space.const hD hvol 0 = 0 := by
  apply H1Space.ext_ae hD
  exact (H1Space.coeFn_const hD hvol 0).trans (Lp.coeFn_zero _ _ _).symm

/-- The actual integral as a bounded linear functional on H¹. -/
def h1IntegralCLM {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (hvol : volume D < ∞) : H1Space D →L[ℝ] ℝ := by
  let : IsFiniteMeasure (volume.restrict D) := ⟨by simpa using hvol⟩
  let one : Lp ℝ 2 (volume.restrict D) :=
    indicatorConstLp 2 MeasurableSet.univ (measure_ne_top _ univ) 1
  exact (innerSL ℝ one).comp H1Space.toLpCLM

lemma h1IntegralCLM_apply {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (hvol : volume D < ∞) (u : H1Space D) : h1IntegralCLM hvol u = ∫ x in D, u x := by
  let : IsFiniteMeasure (volume.restrict D) := ⟨by simpa using hvol⟩
  change inner ℝ (indicatorConstLp 2 MeasurableSet.univ
    (measure_ne_top (volume.restrict D) univ) 1) u.toLp = _
  exact (by simpa only [setIntegral_univ] using
    (L2.inner_indicatorConstLp_one MeasurableSet.univ
      (measure_ne_top (volume.restrict D) univ) u.toLp))

/-- The closed mean-zero subspace, defined using the volume integral. -/
def h1MeanZeroSubmodule {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (hvol : volume D < ∞) : Submodule ℝ (H1Space D) := (h1IntegralCLM hvol).ker

abbrev H1MeanZeroSpace {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (hvol : volume D < ∞) := ↥(h1MeanZeroSubmodule hvol)

instance h1MeanZeroSpaceComplete {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (hvol : volume D < ∞) :
    CompleteSpace (H1MeanZeroSpace hvol) := (h1IntegralCLM hvol).isClosed_ker.completeSpace_coe

lemma mem_h1MeanZeroSubmodule_iff {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (hvol : volume D < ∞) (u : H1Space D) :
    u ∈ h1MeanZeroSubmodule hvol ↔ (∫ x in D, u x) = 0 := by
  change h1IntegralCLM hvol u = 0 ↔ _
  rw [h1IntegralCLM_apply]

/-- Remove the actual average, without requiring the domain volume to be positive. -/
def H1Space.subMean {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (hD : IsOpen D) (hvol : volume D < ∞) (u : H1Space D) : H1Space D :=
  u - H1Space.const hD hvol (⨍ x in D, u x)

lemma H1Space.subMean_mem {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (hD : IsOpen D) (hvol : volume D < ∞) (u : H1Space D) :
    u.subMean hD hvol ∈ h1MeanZeroSubmodule hvol := by
  rw [mem_h1MeanZeroSubmodule_iff]
  have heq : ⇑(u.subMean hD hvol) =ᵐ[volume.restrict D]
      fun x => u x - ⨍ y in D, u y := by
    filter_upwards [H1Space.coeFn_sub u (H1Space.const hD hvol (⨍ y in D, u y)),
      H1Space.coeFn_const hD hvol (⨍ y in D, u y)] with x h1 h2
    exact h1.trans (by rw [h2])
  rw [integral_congr_ae heq]
  exact setAverage_sub_setAverage hvol.ne u

@[simp] lemma H1Space.gradientLp_subMean {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (hD : IsOpen D) (hvol : volume D < ∞) (u : H1Space D) :
    (u.subMean hD hvol).gradientLp = u.gradientLp := by
  change H1Space.gradientCLM (u - H1Space.const hD hvol (⨍ x in D, u x)) = _
  rw [map_sub]
  change u.gradientLp - (H1Space.const hD hvol (⨍ x in D, u x)).gradientLp = _
  simp

/-- The spatial mean-zero Poincaré estimate, in the genuine H¹ component norms. -/
theorem exists_h1_meanZero_poincare {D : Set AmbientSpace}
    (hD : IsOpen D) (hcD : IsPreconnected D) (hbD : Bornology.IsBounded D)
    (hL : HasLipschitzBoundary D) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : H1MeanZeroSpace hbD.measure_lt_top,
      ‖u.val.toLp‖ ≤ C * ‖u.val.gradientLp‖ := by
  obtain ⟨C, hC, hP⟩ := h1_poincare_spatial hD hcD hbD hL
  refine ⟨C, hC, fun u => ?_⟩
  have hi := (mem_h1MeanZeroSubmodule_iff hbD.measure_lt_top u.val).mp u.property
  have hm : (⨍ x in D, u.val x) = 0 := by rw [setAverage_eq, hi, smul_zero]
  have hp := hP u.val u.val.gradientLp u.val.hasH1GradientOn
  simpa only [hm, sub_zero, ← H1Space.norm_toLp_eq_lpNorm,
    ← H1Space.norm_gradientLp_eq_lpNorm] using hp

/-- The mean-zero gradient controls the complete H¹ norm. -/
theorem exists_h1_meanZero_coercivity {D : Set AmbientSpace}
    (hD : IsOpen D) (hcD : IsPreconnected D) (hbD : Bornology.IsBounded D)
    (hL : HasLipschitzBoundary D) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : H1MeanZeroSpace hbD.measure_lt_top,
      ‖u‖ ≤ C * ‖u.val.gradientLp‖ := by
  obtain ⟨C, hC, hP⟩ := exists_h1_meanZero_poincare hD hcD hbD hL
  refine ⟨C + 1, by positivity, fun u => ?_⟩
  have h := u.val.norm_le_sum
  have hp := hP u
  change ‖u.val‖ ≤ _
  nlinarith only [h, hp]

end LiquidDrop
