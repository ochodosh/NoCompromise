module

public import NoCompromise.BV.Compactness
public import NoCompromise.BV.Algebra
public import NoCompromise.BV.Space
public import NoCompromise.Sobolev.ExtensionPartition
public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
public import Mathlib.Geometry.Euclidean.Volume.Measure

@[expose] public section
/-!
# Weak gradients, the bi-Lipschitz BV chain rule, and BV extension

The weak gradient is defined by coordinate integration by parts on open Euclidean
domains. It is unique almost everywhere, is unchanged by null modifications, and
controls the variation supremum when integrable. C¹ and locally Lipschitz functions
on open domains have their ordinary gradients as weak gradients.

Blueprint `lem:bilip-chain` is proved by strict approximation, the smooth chain rule,
Lipschitz distortion of Hausdorff measure, and lower semicontinuity. Flat reflection
on cubes is proved by shifted smooth approximation, with factor-two L¹ and variation
bounds. A fixed compact cutoff yields a global BV function with quantitative bounds.
Lipschitz graph charts and a finite smooth partition assemble a linear extension
with fixed compact support and a uniform BV bound. Almost-everywhere invariance
allows descent to a continuous linear map between the normed BV spaces.
No BV extension or trace theorem is used as an input.
-/

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient Pointwise
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Distributional weak gradient on an open Euclidean domain. Both functions are locally
integrable; the sign is the standard integration-by-parts convention. -/
structure HasWeakGradientOn {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n))) : Prop where
  locallyIntegrable_function : LocallyIntegrableOn f U
  locallyIntegrable_gradient : LocallyIntegrableOn G U
  test_eq : ∀ (i : Fin n) (φ : EuclideanSpace ℝ (Fin n) → ℝ),
    ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U →
    -(∫ x in U, f x * fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in U, φ x * G x i

lemma locallyIntegrableOn_component {n : ℕ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hG : LocallyIntegrableOn G U) (i : Fin n) :
    LocallyIntegrableOn (fun x => G x i) U := by
  intro x hx
  obtain ⟨A, hA, hi⟩ := hG x hx
  exact ⟨A, hA, hi.eval_piLp i⟩

lemma integrable_mul_compact_factor_on {n : ℕ}
    {f φ : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hf : LocallyIntegrableOn f U) (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ U) : Integrable (fun x => φ x * f x) := by
  have hi := (hf.integrableOn_compact_subset hsφ hcφ).mul_continuousOn hφ.continuousOn hcφ
  have hi' : IntegrableOn (fun x => φ x * f x) (tsupport φ) := by
    simpa only [mul_comm] using hi
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hi'
  intro x hx
  by_contra h
  exact hx (by simp [image_eq_zero_of_notMem_tsupport h])

lemma integrable_inner_compact_factor_on {n : ℕ}
    {G X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    (hG : LocallyIntegrableOn G U) (hX : Continuous X) (hcX : HasCompactSupport X)
    (hsX : tsupport X ⊆ U) : Integrable (fun x => inner ℝ (X x) (G x)) := by
  obtain ⟨C, hC⟩ := hcX.exists_bound_of_continuous hX
  have hi := integrable_inner_of_bound (hG.integrableOn_compact_subset hsX hcX)
    hX.aestronglyMeasurable (Eventually.of_forall hC)
  have hi' : IntegrableOn (fun x => inner ℝ (X x) (G x)) (tsupport X) := by
    simpa only [IntegrableOn, real_inner_comm] using hi
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hi'
  intro x hx
  by_contra h
  exact hx (by simp [image_eq_zero_of_notMem_tsupport h])

/-- Componentwise weak differentiation gives the full divergence pairing. -/
theorem HasWeakGradientOn.integral_divergence_eq {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hf : HasWeakGradientOn f G U)
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) (hsX : tsupport X ⊆ U) :
    -(∫ x in U, f x * divergenceN X x) = ∫ x in U, inner ℝ (X x) (G x) := by
  have hi (i : Fin n) := (integrable_mul_fderiv_component hf.locallyIntegrable_function
    hX hcX hsX i i).integrableOn (s := U)
  have hj (i : Fin n) : IntegrableOn (fun x => X x i * G x i) U :=
    (integrable_mul_compact_factor_on
      (locallyIntegrableOn_component hf.locallyIntegrable_gradient i)
      ((EuclideanSpace.proj i).continuous.comp hX.continuous)
      (hcX.of_isClosed_subset (isClosed_tsupport _) (tsupport_vectorComponent_subset X i))
      ((tsupport_vectorComponent_subset X i).trans hsX)).integrableOn
  have htest (i : Fin n) :
      -(∫ x in U, f x * fderiv ℝ X x (EuclideanSpace.single i 1) i) =
        ∫ x in U, X x i * G x i := by
    have hφ : ContDiff ℝ 1 (fun x => X x i) :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hX
    have h := hf.test_eq i (fun x => X x i) hφ
      (hcX.of_isClosed_subset (isClosed_tsupport _) (tsupport_vectorComponent_subset X i))
      ((tsupport_vectorComponent_subset X i).trans hsX)
    simpa only [fderiv_vectorComponent hX] using h
  simp only [divergenceN, Finset.mul_sum,
    integral_finsetSum Finset.univ (fun i _ => hi i)]
  rw [← Finset.sum_neg_distrib]
  simp_rw [htest]
  rw [← integral_finsetSum Finset.univ (fun i _ => hj i)]
  congr 1
  funext x
  simp only [PiLp.inner_apply, Real.inner_apply]

/-- The variation of a function is bounded by the integral of any weak gradient. -/
theorem HasWeakGradientOn.variation_le {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hf : HasWeakGradientOn f G U)
    (hG : IntegrableOn G U) : variation f U ≤ ENNReal.ofReal (∫ x in U, ‖G x‖) := by
  apply iSup_le
  intro X
  apply iSup_le
  intro hX
  apply ENNReal.ofReal_le_ofReal
  have h := hf.integral_divergence_eq hX.1 hX.2.1 hX.2.2.1
  have hnorm : ‖∫ x in U, inner ℝ (X x) (G x)‖ ≤ ∫ x in U, ‖G x‖ := by
    apply norm_integral_le_of_norm_le hG.norm
    exact Eventually.of_forall fun x => by
      simpa only [one_mul] using (norm_inner_le_norm (X x) (G x)).trans
        (mul_le_mul_of_nonneg_right (hX.2.2.2 x) (norm_nonneg _))
  have ha := le_abs_self (∫ x in U, f x * divergenceN X x)
  rw [← Real.norm_eq_abs, ← norm_neg, h] at ha
  exact ha.trans hnorm

lemma HasWeakGradientOn.isBVOn {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hf : HasWeakGradientOn f G U)
    (hif : IntegrableOn f U) (hiG : IntegrableOn G U) : IsBVOn f U :=
  ⟨hif, (hf.variation_le hiG).trans_lt ENNReal.ofReal_lt_top⟩

/-- Weak gradients are unique almost everywhere on open domains. -/
theorem HasWeakGradientOn.unique {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hG : HasWeakGradientOn f G U) (hH : HasWeakGradientOn f H U) :
    G =ᵐ[volume.restrict U] H := by
  have hcoord (i : Fin n) : ∀ᵐ x ∂volume, x ∈ U → G x i - H x i = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((locallyIntegrableOn_component hG.locallyIntegrable_gradient i).sub
        (locallyIntegrableOn_component hH.locallyIntegrable_gradient i))
    intro φ hφ hcφ hsφ
    have h1 := hG.test_eq i φ (hφ.of_le (by simp)) hcφ hsφ
    have h2 := hH.test_eq i φ (hφ.of_le (by simp)) hcφ hsφ
    have hiG := (integrable_mul_compact_factor_on
      (locallyIntegrableOn_component hG.locallyIntegrable_gradient i) hφ.continuous hcφ hsφ)
    have hiH := (integrable_mul_compact_factor_on
      (locallyIntegrableOn_component hH.locallyIntegrable_gradient i) hφ.continuous hcφ hsφ)
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U)]
    · simp only [smul_eq_mul, Pi.sub_apply, mul_sub]
      rw [integral_sub hiG.integrableOn hiH.integrableOn]
      linarith
    · intro x hx
      simp [image_eq_zero_of_notMem_tsupport (fun h => hx (hsφ h))]
  apply (ae_restrict_iff' hU.measurableSet).mpr
  filter_upwards [ae_all_iff.mpr hcoord] with x hx hxU
  apply PiLp.ext
  intro i
  exact sub_eq_zero.mp (hx i hxU)


/-- Changing representatives on null sets preserves the weak-gradient identity. -/
lemma HasWeakGradientOn.congr_ae {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {G H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasWeakGradientOn f G U) (hfg : f =ᵐ[volume.restrict U] g)
    (hGH : G =ᵐ[volume.restrict U] H) : HasWeakGradientOn g H U := by
  refine ⟨LocallyIntegrableOn.congr hfg hf.locallyIntegrable_function,
    LocallyIntegrableOn.congr hGH hf.locallyIntegrable_gradient, ?_⟩
  intro i φ hφ hcφ hsφ
  calc
    _ = -(∫ x in U, f x * fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hfg] with x hx
      rw [hx]
    _ = ∫ x in U, φ x * G x i := hf.test_eq i φ hφ hcφ hsφ
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hGH] with x hx
      rw [hx]

/-- Integration by parts for a C¹ function on the open domain, with no global regularity. -/
theorem integral_divergence_eq_gradient_on {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiffOn ℝ 1 f U)
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hX : ContDiff ℝ 1 X) (hcX : HasCompactSupport X) (hsX : tsupport X ⊆ U) :
    -(∫ x in U, f x * divergenceN X x) = ∫ x in U, inner ℝ (X x) (gradient f x) := by
  have hlf : LocallyIntegrableOn f U := hf.continuousOn.locallyIntegrableOn hU.measurableSet
  have hlG : LocallyIntegrableOn (gradient f) U :=
    (continuousOn_gradient_of_contDiffOn hU hf).locallyIntegrableOn hU.measurableSet
  have hi := (integrable_inner_compact_factor_on hlG hX.continuous hcX hsX).integrableOn (s := U)
  have hfdiv := (integrable_mul_divergenceN hlf hX hcX hsX).integrableOn (s := U)
  have hY := contDiff_smul_of_tsupport_subset hU hf hX hsX
  have hsY : tsupport (fun y => f y • X y) ⊆ U :=
    (tsupport_smul_subset_right f X).trans hsX
  have hcY : HasCompactSupport (fun y => f y • X y) :=
    hcX.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_right f X)
  have hzero : (∫ x in U, divergenceN (fun y => f y • X y) x) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact integral_divergenceN_eq_zero (X := fun y => f y • X y) hY hcY
    · intro x hx
      exact divergenceN_eq_zero_of_notMem_tsupport (fun h => hx (hsY h))
  have heq : (∫ x in U, divergenceN (fun y => f y • X y) x) =
      ∫ x in U, f x * divergenceN X x + inner ℝ (X x) (gradient f x) := by
    apply setIntegral_congr_fun hU.measurableSet
    intro x hx
    simpa only [real_inner_comm] using divergenceN_smul_of_differentiableAt
      ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero)
      (hX.differentiable one_ne_zero x)
  rw [heq, integral_add hfdiv hi] at hzero
  linarith

/-- A C¹ function has its ordinary Hilbert-space gradient as weak gradient. -/
theorem hasWeakGradientOn_of_contDiffOn {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiffOn ℝ 1 f U) :
    HasWeakGradientOn f (gradient f) U := by
  refine ⟨hf.continuousOn.locallyIntegrableOn hU.measurableSet,
    (continuousOn_gradient_of_contDiffOn hU hf).locallyIntegrableOn hU.measurableSet, ?_⟩
  intro i φ hφ hcφ hsφ
  let X (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
    φ x • EuclideanSpace.single i 1
  have hX : ContDiff ℝ 1 X := hφ.smul contDiff_const
  have hcX : HasCompactSupport X := hcφ.smul_right
  have hsX : tsupport X ⊆ U := (tsupport_smul_subset_left φ _).trans hsφ
  have h := integral_divergence_eq_gradient_on hU hf hX hcX hsX
  have hdiv (x) : divergenceN X x = fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    rw [divergenceN_smul hφ contDiff_const]
    simp [divergenceN, inner_gradient_left]
  simpa only [hdiv, X, real_inner_smul_left, EuclideanSpace.inner_single_left,
    one_mul, conj_trivial] using h

/-- The ordinary gradient, taken to be zero at nondifferentiability points, is measurable. -/
lemma measurable_gradient {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    Measurable (gradient f) :=
  (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.measurable.comp (measurable_fderiv ℝ f)

lemma norm_gradient_le_of_lipschitz {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {C : ℝ≥0} (hf : LipschitzWith C f) (x : EuclideanSpace ℝ (Fin n)) :
    ‖gradient f x‖ ≤ C := by
  change ‖(toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f x)‖ ≤ C
  rw [LinearIsometryEquiv.norm_map]
  exact norm_fderiv_le_of_lipschitz ℝ hf

/-- Rademacher's gradient of a Lipschitz function is also its distributional weak gradient. -/
theorem hasWeakGradientOn_of_lipschitz {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f)
    (U : Set (EuclideanSpace ℝ (Fin n))) : HasWeakGradientOn f (gradient f) U := by
  have hG : LocallyIntegrable (gradient f) :=
    (memLp_top_of_bound (measurable_gradient f).aestronglyMeasurable (C : ℝ)
      (Eventually.of_forall (norm_gradient_le_of_lipschitz hf))).locallyIntegrable le_top
  refine ⟨hf.continuous.locallyIntegrable.locallyIntegrableOn U, hG.locallyIntegrableOn U, ?_⟩
  intro i φ hφ hcφ hsφ
  obtain ⟨D, hφlip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcφ hφ one_ne_zero
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1
  have hid := hf.integral_lineDeriv_mul_eq (μ := volume) hφlip hcφ e
  have hleft : (∫ x in U, f x * fderiv ℝ φ x e) = ∫ x, f x * fderiv ℝ φ x e := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hsφ h)), zero_apply, mul_zero]
  have hright : (∫ x in U, φ x * gradient f x i) = ∫ x, φ x * gradient f x i := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsφ h)), zero_mul]
  change -(∫ x in U, f x * fderiv ℝ φ x e) = _
  rw [hleft, hright]
  calc
    _ = ∫ x, lineDeriv ℝ φ x (-e) * f x := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with x
      rw [(hφ.differentiable one_ne_zero x).lineDeriv_eq_fderiv, map_neg]
      ring
    _ = ∫ x, lineDeriv ℝ f x e * φ x := hid.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hf.ae_differentiableAt (μ := volume)] with x hx
      rw [hx.lineDeriv_eq_fderiv, ← gradient_apply_eq_fderiv_single]
      exact mul_comm _ _


/-- The elementary infimum-of-cones extension of a scalar Lipschitz function.
This does not assume a Sobolev or BV extension theorem. -/
lemma exists_lipschitz_extension_real {α : Type*} [PseudoMetricSpace α]
    {f : α → ℝ} {s : Set α} {K : ℝ≥0} (hf : LipschitzOnWith K f s) :
    ∃ g : α → ℝ, LipschitzWith K g ∧ EqOn f g s := by
  rcases eq_empty_or_nonempty s with rfl | hs
  · exact ⟨fun _ => 0, (LipschitzWith.const _).weaken zero_le, eqOn_empty _ _⟩
  have : Nonempty s := by simp only [hs, nonempty_coe_sort]
  let g (y : α) := ⨅ x : s, f x + K * dist y x
  have hbelow (y : α) : BddBelow (range fun x : s => f x + K * dist y x) := by
    obtain ⟨z, hz⟩ := hs
    refine ⟨f z - K * dist y z, ?_⟩
    rintro w ⟨t, rfl⟩
    dsimp
    rw [sub_le_iff_le_add, add_assoc, ← mul_add, add_comm (dist y t)]
    calc
      f z ≤ f t + K * dist z t := hf.le_add_mul hz t.2
      _ ≤ f t + K * (dist y z + dist y t) := by gcongr; apply dist_triangle_left
  have heq : EqOn f g s := fun x hx => by
    refine le_antisymm (le_ciInf fun y => hf.le_add_mul hx y.2) ?_
    simpa only [add_zero, Subtype.coe_mk, mul_zero, dist_self] using ciInf_le (hbelow x) ⟨x, hx⟩
  refine ⟨g, LipschitzWith.of_le_add_mul K (fun x y => ?_), heq⟩
  rw [← sub_le_iff_le_add]
  refine le_ciInf fun z => ?_
  rw [sub_le_iff_le_add]
  calc
    g x ≤ f z + K * dist x z := ciInf_le (hbelow x) _
    _ ≤ f z + K * dist y z + K * dist x y := by
      rw [add_assoc, ← mul_add, add_comm (dist y z)]
      gcongr
      apply dist_triangle

/-- A locally Lipschitz scalar function agrees with a globally Lipschitz function
on an open neighbourhood of any compact subset of its open domain. -/
lemma exists_lipschitz_representative_near_compact {n : ℕ}
    {U K : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : LocallyLipschitzOn U f) :
    ∃ (W : Set (EuclideanSpace ℝ (Fin n))) (g : EuclideanSpace ℝ (Fin n) → ℝ) (C : ℝ≥0),
      IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧ LipschitzWith C g ∧ EqOn f g W ∧
      EqOn (gradient f) (gradient g) W := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨C, hC⟩ := (hf.mono hsub).exists_lipschitzOnWith_of_compact hK.cthickening
  obtain ⟨g, hg, heq⟩ := exists_lipschitz_extension_real hC
  have hW : thickening δ K ⊆ cthickening δ K := thickening_subset_cthickening δ K
  refine ⟨thickening δ K, g, C, isOpen_thickening, self_subset_thickening hδ K,
    hW.trans hsub, hg, heq.mono hW, ?_⟩
  intro x hx
  apply Filter.EventuallyEq.gradient_eq
  filter_upwards [isOpen_thickening.mem_nhds hx] with y hy
  exact heq (hW hy)

lemma locallyIntegrableOn_gradient_of_locallyLipschitzOn {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LocallyLipschitzOn U f) :
    LocallyIntegrableOn (gradient f) U := by
  intro x hx
  obtain ⟨W, g, C, hW, hxW, hWU, hg, heq, hgrad⟩ :=
    exists_lipschitz_representative_near_compact hU isCompact_singleton
      (singleton_subset_iff.mpr hx) hf
  obtain ⟨A, hA, hi⟩ := (hasWeakGradientOn_of_lipschitz hg U).locallyIntegrable_gradient x hx
  refine ⟨A ∩ W, inter_mem hA (mem_nhdsWithin_of_mem_nhds (hW.mem_nhds (hxW (mem_singleton x)))),
    ?_⟩
  apply (hi.mono_set inter_subset_left).congr_fun_ae
  exact ae_restrict_of_ae_restrict_of_subset inter_subset_right
    (ae_restrict_of_forall_mem hW.measurableSet fun y hy => (hgrad hy).symm)

/-- A locally Lipschitz function on an open domain has its ordinary gradient as
weak gradient, with no regularity assumption outside that domain. -/
theorem hasWeakGradientOn_of_locallyLipschitzOn {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LocallyLipschitzOn U f) :
    HasWeakGradientOn f (gradient f) U := by
  refine ⟨hf.continuousOn.locallyIntegrableOn hU.measurableSet,
    locallyIntegrableOn_gradient_of_locallyLipschitzOn hU hf, ?_⟩
  intro i φ hφ hcφ hsφ
  obtain ⟨W, g, C, hW, hsW, hWU, hg, heq, hgrad⟩ :=
    exists_lipschitz_representative_near_compact hU hcφ hsφ hf
  have hleft : (fun x => f x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      (fun x => g x * fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
    funext x
    by_cases hx : x ∈ tsupport φ
    · rw [heq (hsW hx)]
    · rw [fderiv_of_notMem_tsupport ℝ hx, zero_apply, mul_zero, mul_zero]
  have hright : (fun x => φ x * gradient f x i) = (fun x => φ x * gradient g x i) := by
    funext x
    by_cases hx : x ∈ tsupport φ
    · rw [hgrad (hsW hx)]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  simpa only [hleft, hright] using (hasWeakGradientOn_of_lipschitz hg U).test_eq i φ hφ hcφ hsφ

/-- Smooth scalar functions remain locally Lipschitz after Lipschitz changes of variables. -/
lemma locallyLipschitzOn_comp_of_contDiffOn {n m : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {V : Set (EuclideanSpace ℝ (Fin m))}
    (hV : IsOpen V) {g : EuclideanSpace ℝ (Fin m) → ℝ} (hg : ContDiffOn ℝ 1 g V)
    {Φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} {C : ℝ≥0}
    (hΦ : LipschitzOnWith C Φ U) (hmaps : MapsTo Φ U V) :
    LocallyLipschitzOn U (g ∘ Φ) := by
  intro x hx
  obtain ⟨K, t, ht, hgt⟩ :=
    (hg.contDiffAt (hV.mem_nhds (hmaps hx))).exists_lipschitzOnWith
  refine ⟨K * C, U ∩ Φ ⁻¹' t, inter_mem self_mem_nhdsWithin
    ((hΦ.continuousOn x hx) ht), ?_⟩
  exact hgt.comp (hΦ.mono inter_subset_left) fun _ hy => hy.2

/-- The ordinary gradient of a smooth function composed with a Lipschitz map is its
weak gradient on the open source domain. -/
theorem hasWeakGradientOn_comp_of_contDiffOn {n m : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {V : Set (EuclideanSpace ℝ (Fin m))}
    (hU : IsOpen U) (hV : IsOpen V)
    {g : EuclideanSpace ℝ (Fin m) → ℝ} (hg : ContDiffOn ℝ 1 g V)
    {Φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} {C : ℝ≥0}
    (hΦ : LipschitzOnWith C Φ U) (hmaps : MapsTo Φ U V) :
    HasWeakGradientOn (g ∘ Φ) (gradient (g ∘ Φ)) U :=
  hasWeakGradientOn_of_locallyLipschitzOn hU
    (locallyLipschitzOn_comp_of_contDiffOn hV hg hΦ hmaps)

/-- The classical chain rule applies almost everywhere to a smooth scalar function
after a Lipschitz change of variables on open domains. -/
theorem ae_fderiv_comp_of_contDiffOn {n m : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {V : Set (EuclideanSpace ℝ (Fin m))}
    (hU : IsOpen U) (hV : IsOpen V)
    {g : EuclideanSpace ℝ (Fin m) → ℝ} (hg : ContDiffOn ℝ 1 g V)
    {Φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} {C : ℝ≥0}
    (hΦ : LipschitzOnWith C Φ U) (hmaps : MapsTo Φ U V) :
    ∀ᵐ x ∂volume.restrict U,
      fderiv ℝ (g ∘ Φ) x = (fderiv ℝ g (Φ x)).comp (fderiv ℝ Φ x) := by
  filter_upwards [hΦ.ae_differentiableWithinAt (μ := volume) hU.measurableSet,
    ae_restrict_mem hU.measurableSet] with x hx hxU
  exact fderiv_comp x ((hg.contDiffAt (hV.mem_nhds (hmaps hxU))).differentiableAt
    one_ne_zero) (hx.differentiableAt (hU.mem_nhds hxU))

/-- Quantitative gradient bound for smooth scalar functions under Lipschitz composition. -/
theorem ae_norm_gradient_comp_le {n m : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {V : Set (EuclideanSpace ℝ (Fin m))}
    (hU : IsOpen U) (hV : IsOpen V)
    {g : EuclideanSpace ℝ (Fin m) → ℝ} (hg : ContDiffOn ℝ 1 g V)
    {Φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} {C : ℝ≥0}
    (hΦ : LipschitzOnWith C Φ U) (hmaps : MapsTo Φ U V) :
    ∀ᵐ x ∂volume.restrict U, ‖gradient (g ∘ Φ) x‖ ≤ C * ‖gradient g (Φ x)‖ := by
  filter_upwards [ae_fderiv_comp_of_contDiffOn hU hV hg hΦ hmaps,
    ae_restrict_mem hU.measurableSet] with x hx hxU
  change ‖(toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ (g ∘ Φ) x)‖ ≤
    C * ‖(toDual ℝ (EuclideanSpace ℝ (Fin m))).symm (fderiv ℝ g (Φ x))‖
  simp only [LinearIsometryEquiv.norm_map]
  rw [hx]
  calc
    _ ≤ ‖fderiv ℝ g (Φ x)‖ * ‖fderiv ℝ Φ x‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ g (Φ x)‖ * C := mul_le_mul_of_nonneg_left
      (norm_fderiv_le_of_lipschitzOn ℝ (hU.mem_nhds hxU) hΦ) (norm_nonneg _)
    _ = _ := mul_comm _ _
/-- Lipschitz distortion of Lebesgue volume, by the corresponding Hausdorff measure bound. -/
lemma volume_image_le_of_lipschitzOn {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {s : Set (EuclideanSpace ℝ (Fin n))} {C : ℝ≥0} (hf : LipschitzOnWith C f s) :
    volume (f '' s) ≤ (C : ℝ≥0∞) ^ n * volume s := by
  rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume n,
    Measure.euclideanHausdorffMeasure_def]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  calc
    _ ≤ _ := mul_le_mul' le_rfl (hf.hausdorffMeasure_image_le (d := n) (by positivity))
    _ = _ := by rw [ENNReal.rpow_natCast]; ring

/-- A Lipschitz left inverse controls the volume of preimages, including nonmeasurable sets. -/
lemma volume_preimage_inter_le_of_lipschitz_leftInverse {n : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin n))}
    {Φ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {K : ℝ≥0}
    (hΨ : LipschitzOnWith K Ψ V) (hmaps : MapsTo Φ U V) (hinv : LeftInvOn Ψ Φ U)
    (s : Set (EuclideanSpace ℝ (Fin n))) :
    volume (Φ ⁻¹' s ∩ U) ≤ (K : ℝ≥0∞) ^ n * volume (s ∩ V) := by
  have hsub : Φ ⁻¹' s ∩ U ⊆ Ψ '' (s ∩ V) := by
    intro x hx
    exact ⟨Φ x, ⟨hx.1, hmaps hx.2⟩, hinv hx.2⟩
  exact (measure_mono hsub).trans
    (volume_image_le_of_lipschitzOn (hΨ.mono inter_subset_right))

/-- The pushforward of source volume is dominated by inverse-Lipschitz distortion. -/
lemma map_volume_restrict_le_of_lipschitz_leftInverse {n : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    {Φ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {K : ℝ≥0}
    (hΦ : ContinuousOn Φ U) (hΨ : LipschitzOnWith K Ψ V)
    (hmaps : MapsTo Φ U V) (hinv : LeftInvOn Ψ Φ U) :
    Measure.map Φ (volume.restrict U) ≤ (K : ℝ≥0∞) ^ n • volume.restrict V := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.map_apply_of_aemeasurable (hΦ.aemeasurable hU) hs,
    Measure.restrict_apply' hU, Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]
  exact volume_preimage_inter_le_of_lipschitz_leftInverse hΨ hmaps hinv s

/-- Integrability is preserved by a continuous map with a Lipschitz left inverse. -/
lemma integrableOn_comp_of_lipschitz_leftInverse {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    {Φ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {K : ℝ≥0}
    (hΦ : ContinuousOn Φ U) (hΨ : LipschitzOnWith K Ψ V)
    (hmaps : MapsTo Φ U V) (hinv : LeftInvOn Ψ Φ U)
    {g : EuclideanSpace ℝ (Fin n) → E} (hg : IntegrableOn g V) :
    IntegrableOn (g ∘ Φ) U := by
  have hi := (hg.smul_measure (c := (K : ℝ≥0∞) ^ n) (by finiteness)).mono_measure
    (map_volume_restrict_le_of_lipschitz_leftInverse hU hΦ hΨ hmaps hinv)
  exact hi.comp_aemeasurable (hΦ.aemeasurable hU)

/-- Quantitative L¹ control under a change of variables with Lipschitz inverse. -/
lemma integral_norm_comp_le_of_lipschitz_leftInverse {n : ℕ} {E : Type*}
    [NormedAddCommGroup E]
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    {Φ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {K : ℝ≥0}
    (hΦ : ContinuousOn Φ U) (hΨ : LipschitzOnWith K Ψ V)
    (hmaps : MapsTo Φ U V) (hinv : LeftInvOn Ψ Φ U)
    {g : EuclideanSpace ℝ (Fin n) → E} (hg : IntegrableOn g V) :
    (∫ x in U, ‖g (Φ x)‖) ≤ (K : ℝ) ^ n * ∫ x in V, ‖g x‖ := by
  have hmap := map_volume_restrict_le_of_lipschitz_leftInverse hU hΦ hΨ hmaps hinv
  have hi := hg.norm.smul_measure (c := (K : ℝ≥0∞) ^ n) (by finiteness)
  calc
    _ = ∫ y, ‖g y‖ ∂Measure.map Φ (volume.restrict U) :=
      (integral_map (hΦ.aemeasurable hU) (hi.mono_measure hmap).aestronglyMeasurable).symm
    _ ≤ ∫ y, ‖g y‖ ∂((K : ℝ≥0∞) ^ n • volume.restrict V) :=
      integral_mono_measure hmap (Eventually.of_forall fun _ => norm_nonneg _) hi
    _ = _ := by simp [integral_smul_measure]

/-- The integrated smooth chain-rule bound, on arbitrary open domains. -/
theorem integral_norm_gradient_comp_le {n : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hV : IsOpen V)
    {Φ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {C K : ℝ≥0}
    (hΦ : LipschitzOnWith C Φ U) (hΨ : LipschitzOnWith K Ψ V)
    (hmaps : MapsTo Φ U V) (hinv : LeftInvOn Ψ Φ U)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiffOn ℝ 1 g V)
    (hi : IntegrableOn (gradient g) V) :
    IntegrableOn (gradient (g ∘ Φ)) U ∧
      (∫ x in U, ‖gradient (g ∘ Φ) x‖) ≤ C * (K : ℝ) ^ n * ∫ y in V, ‖gradient g y‖ := by
  have hbound := ae_norm_gradient_comp_le hU hV hg hΦ hmaps
  have hi' := integrableOn_comp_of_lipschitz_leftInverse hU.measurableSet
    hΦ.continuousOn hΨ hmaps hinv hi
  have hmaj : IntegrableOn (fun x => C * ‖gradient g (Φ x)‖) U := hi'.norm.const_mul C
  have higrad : IntegrableOn (gradient (g ∘ Φ)) U :=
    hmaj.mono' (measurable_gradient _).aestronglyMeasurable hbound
  refine ⟨higrad, ?_⟩
  calc
    _ ≤ ∫ x in U, C * ‖gradient g (Φ x)‖ := integral_mono_ae higrad.norm hmaj hbound
    _ = C * ∫ x in U, ‖gradient g (Φ x)‖ := integral_const_mul _ _
    _ ≤ C * ((K : ℝ) ^ n * ∫ y in V, ‖gradient g y‖) :=
      mul_le_mul_of_nonneg_left (integral_norm_comp_le_of_lipschitz_leftInverse
        hU.measurableSet hΦ.continuousOn hΨ hmaps hinv hi) C.coe_nonneg
    _ = _ := (mul_assoc _ _ _).symm

/-- BV variation is controlled by the forward and inverse Lipschitz constants.
Strict approximation and lower semicontinuity justify the nonsmooth passage. -/
theorem variation_comp_le_of_lipschitz_leftInverse {n : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hV : IsOpen V)
    {Φ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {C K : ℝ≥0}
    (hΦ : LipschitzOnWith C Φ U) (hΨ : LipschitzOnWith K Ψ V)
    (hmaps : MapsTo Φ U V) (hinv : LeftInvOn Ψ Φ U)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : IsBVOn g V) :
    variation (g ∘ Φ) U ≤ ENNReal.ofReal (C * (K : ℝ) ^ n * (variation g V).toReal) := by
  have hi := integrableOn_comp_of_lipschitz_leftInverse hU.measurableSet
    hΦ.continuousOn hΨ hmaps hinv hg.1
  obtain ⟨f, hf, hie, he, _, hstrict⟩ := strict_approximation_on hV
    (isLocallyBVOn_of_variation_lt_top hV hg.1.locallyIntegrableOn hg.2)
  obtain ⟨hifgrad, hgradconv⟩ := hstrict hg.2
  have hif (j) : IntegrableOn (f j) V := by
    have h := (hie j).add hg.1
    change IntegrableOn (fun x => (f j x - g x) + g x) V at h
    simpa only [sub_add_cancel] using h
  have hifcomp (j) := integrableOn_comp_of_lipschitz_leftInverse hU.measurableSet
    hΦ.continuousOn hΨ hmaps hinv (hif j)
  have hecomp (j) := integrableOn_comp_of_lipschitz_leftInverse hU.measurableSet
    hΦ.continuousOn hΨ hmaps hinv (hie j)
  have hglobal : Tendsto (fun j => ∫ x in U, |f j (Φ x) - g (Φ x)|) atTop (𝓝 0) := by
    apply squeeze_zero (fun j => integral_nonneg fun _ => abs_nonneg _) (fun j => ?_)
      (by simpa only [mul_zero] using he.const_mul ((K : ℝ) ^ n))
    simpa only [Function.comp_def, Real.norm_eq_abs] using
      integral_norm_comp_le_of_lipschitz_leftInverse hU.measurableSet hΦ.continuousOn
        hΨ hmaps hinv (hie j)
  have hlocal (A : Set (EuclideanSpace ℝ (Fin n))) (hAU : A ⊆ U) :
      Tendsto (fun j => ∫ x in A, |f j (Φ x) - g (Φ x)|) atTop (𝓝 0) := by
    apply squeeze_zero (fun j => integral_nonneg fun _ => abs_nonneg _) (fun j => ?_) hglobal
    exact setIntegral_mono_set (hecomp j).abs (Eventually.of_forall fun _ => abs_nonneg _)
      (Eventually.of_forall hAU)
  have hlsc := variation_le_liminf_of_locally_l1 hU
    (fun j => (hifcomp j).locallyIntegrableOn) hi.locallyIntegrableOn
    (fun A _ hAU => hlocal A hAU)
  have hvar (j) : variation (f j ∘ Φ) U ≤
      ENNReal.ofReal (C * (K : ℝ) ^ n * ∫ y in V, ‖gradient (f j) y‖) := by
    have hs : ContDiffOn ℝ 1 (f j) V := (hf j).of_le (by simp)
    have hb := integral_norm_gradient_comp_le hU hV hΦ hΨ hmaps hinv hs (hifgrad j)
    exact ((hasWeakGradientOn_comp_of_contDiffOn hU hV hs hΦ hmaps).variation_le hb.1).trans
      (ENNReal.ofReal_le_ofReal hb.2)
  have ht : Tendsto
      (fun j => ENNReal.ofReal (C * (K : ℝ) ^ n * ∫ y in V, ‖gradient (f j) y‖))
      atTop (𝓝 (ENNReal.ofReal (C * (K : ℝ) ^ n * (variation g V).toReal))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hgradconv.const_mul _)
  exact hlsc.trans ((liminf_le_liminf (Eventually.of_forall hvar)).trans_eq ht.liminf_eq)

/-- Quantitative BV composition. A Lipschitz left inverse suffices; surjectivity is unnecessary. -/
theorem bv_comp_of_lipschitz_leftInverse {n : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hV : IsOpen V)
    {Φ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {C K : ℝ≥0}
    (hΦ : LipschitzOnWith C Φ U) (hΨ : LipschitzOnWith K Ψ V)
    (hmaps : MapsTo Φ U V) (hinv : LeftInvOn Ψ Φ U)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : IsBVOn g V) :
    IsBVOn (g ∘ Φ) U ∧
      (∫ x in U, ‖g (Φ x)‖) + (variation (g ∘ Φ) U).toReal ≤
        max 1 (C : ℝ) * (K : ℝ) ^ n * ((∫ y in V, ‖g y‖) + (variation g V).toReal) := by
  have hi := integrableOn_comp_of_lipschitz_leftInverse hU.measurableSet
    hΦ.continuousOn hΨ hmaps hinv hg.1
  have hv := variation_comp_le_of_lipschitz_leftInverse hU hV hΦ hΨ hmaps hinv hg
  refine ⟨⟨hi, hv.trans_lt ENNReal.ofReal_lt_top⟩, ?_⟩
  have hvreal := ENNReal.toReal_le_of_le_ofReal (by positivity) hv
  have hl1 := integral_norm_comp_le_of_lipschitz_leftInverse hU.measurableSet
    hΦ.continuousOn hΨ hmaps hinv hg.1
  have hcoef1 : (K : ℝ) ^ n ≤ max 1 (C : ℝ) * (K : ℝ) ^ n := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left 1 (C : ℝ))
      (pow_nonneg K.coe_nonneg n)
  have hcoef2 : (C : ℝ) * (K : ℝ) ^ n ≤ max 1 (C : ℝ) * (K : ℝ) ^ n :=
    mul_le_mul_of_nonneg_right (le_max_right 1 (C : ℝ)) (pow_nonneg K.coe_nonneg n)
  calc
    _ ≤ (K : ℝ) ^ n * (∫ y in V, ‖g y‖) +
        C * (K : ℝ) ^ n * (variation g V).toReal := add_le_add hl1 hvreal
    _ ≤ (max 1 (C : ℝ) * (K : ℝ) ^ n) * (∫ y in V, ‖g y‖) +
        (max 1 (C : ℝ) * (K : ℝ) ^ n) * (variation g V).toReal :=
      add_le_add (mul_le_mul_of_nonneg_right hcoef1 (integral_nonneg fun _ => norm_nonneg _))
        (mul_le_mul_of_nonneg_right hcoef2 ENNReal.toReal_nonneg)
    _ = _ := (mul_add _ _ _).symm

/-- Blueprint `lem:bilip-chain`, with the explicit constant `max 1 C * K^n`.
The domain is the preimage inside `U`; a forward Lipschitz map and a Lipschitz
left inverse on `V` suffice for the asserted bi-Lipschitz-homeomorphism case. -/
theorem bv_bilipschitz_chain {n : ℕ}
    {U V D : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hD : IsOpen D) (hDV : D ⊆ V)
    {Φ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {C K : ℝ≥0}
    (hΦ : LipschitzOnWith C Φ U) (hΨ : LipschitzOnWith K Ψ V) (hinv : LeftInvOn Ψ Φ U)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : IsBVOn g D) :
    IsBVOn (g ∘ Φ) (U ∩ Φ ⁻¹' D) ∧
      (∫ x in U ∩ Φ ⁻¹' D, ‖g (Φ x)‖) + (variation (g ∘ Φ) (U ∩ Φ ⁻¹' D)).toReal ≤
        max 1 (C : ℝ) * (K : ℝ) ^ n * ((∫ y in D, ‖g y‖) + (variation g D).toReal) := by
  apply bv_comp_of_lipschitz_leftInverse (hΦ.continuousOn.isOpen_inter_preimage hU hD) hD
    (hΦ.mono inter_subset_left) (hΨ.mono hDV) (fun _ hx => hx.2)
    (fun _ hx => hinv hx.1) hg
/-! ## Flat reflection and compact cutoff bounds -/

/-- Orthogonal reflection across the coordinate hyperplane indexed by `i`. -/
noncomputable def coordinateReflection {n : ℕ} (i : Fin n) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun j => if j = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

lemma coordinateReflection_apply {n : ℕ} (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    coordinateReflection i x j = if j = i then -x j else x j := by
  simp only [coordinateReflection, LinearIsometryEquiv.piLpCongrRight_apply, PiLp.toLp_apply]
  split_ifs <;> rfl

lemma coordinateReflection_involutive {n : ℕ} (i : Fin n) :
    Function.Involutive (coordinateReflection i) := by
  intro x
  ext j
  simp only [coordinateReflection_apply]
  split_ifs <;> simp

/-- Fold the `i`-th coordinate into the closed upper half-space. -/
noncomputable def coordinateFold {n : ℕ} (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => if j = i then |x j| else x j)

lemma coordinateFold_apply {n : ℕ} (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    coordinateFold i x j = if j = i then |x j| else x j := rfl

lemma coordinateFold_eq_self {n : ℕ} {i : Fin n}
    {x : EuclideanSpace ℝ (Fin n)} (hx : 0 ≤ x i) : coordinateFold i x = x := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [coordinateFold_apply, abs_of_nonneg hx]
  · simp [coordinateFold_apply, hj]

lemma coordinateFold_eq_reflection {n : ℕ} {i : Fin n}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x i ≤ 0) :
    coordinateFold i x = coordinateReflection i x := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [coordinateFold_apply, coordinateReflection_apply, abs_of_nonpos hx]
  · simp [coordinateFold_apply, coordinateReflection_apply, hj]

lemma lipschitzWith_coordinateFold {n : ℕ} (i : Fin n) :
    LipschitzWith 1 (coordinateFold i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, PiLp.dist_eq_of_L2]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j = i
  · subst j
    simp only [coordinateFold_apply, ite_true]
    gcongr
    simpa only [Real.dist_eq] using abs_abs_sub_abs_le_abs_sub (x i) (y i)
  · simp only [coordinateFold_apply, ite_eq_right hj, le_refl]

lemma volume_preimage_coordinateFold_le {n : ℕ} (i : Fin n)
    (s : Set (EuclideanSpace ℝ (Fin n))) :
    volume (coordinateFold i ⁻¹' s) ≤ 2 * volume s := by
  have hsub : coordinateFold i ⁻¹' s ⊆ s ∪ coordinateReflection i '' s := by
    intro x hx
    change coordinateFold i x ∈ s at hx
    by_cases hx0 : 0 ≤ x i
    · exact Or.inl (by simpa only [coordinateFold_eq_self hx0] using hx)
    · right
      refine ⟨coordinateReflection i x, ?_, coordinateReflection_involutive i x⟩
      simpa only [coordinateFold_eq_reflection (le_of_lt (lt_of_not_ge hx0))] using hx
  calc
    _ ≤ volume (s ∪ coordinateReflection i '' s) := measure_mono hsub
    _ ≤ volume s + volume (coordinateReflection i '' s) := measure_union_le _ _
    _ ≤ volume s + volume s := add_le_add le_rfl
      (by simpa using (volume_image_le_of_lipschitzOn
        (coordinateReflection i).lipschitz.lipschitzOnWith))
    _ = _ := (two_mul _).symm

/-- Shift the folded coordinate a positive distance into the upper half-space. -/
noncomputable def shiftedCoordinateFold {n : ℕ} (i : Fin n) (δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  coordinateFold i x + δ • EuclideanSpace.single i 1

lemma lipschitzWith_shiftedCoordinateFold {n : ℕ} (i : Fin n) (δ : ℝ) :
    LipschitzWith 1 (shiftedCoordinateFold i δ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [shiftedCoordinateFold, dist_add_right, NNReal.coe_one, one_mul] using
    (lipschitzWith_coordinateFold i).dist_le_mul x y

lemma volume_preimage_shiftedCoordinateFold_le {n : ℕ} (i : Fin n) (δ : ℝ)
    (s : Set (EuclideanSpace ℝ (Fin n))) :
    volume (shiftedCoordinateFold i δ ⁻¹' s) ≤ 2 * volume s := by
  have h := volume_preimage_coordinateFold_le i
    ((fun x => x + δ • EuclideanSpace.single i 1) ⁻¹' s)
  have heq : volume ((fun x => x + δ • EuclideanSpace.single i 1) ⁻¹' s) = volume s :=
    measure_preimage_add_right volume _ s
  exact h.trans_eq (congrArg (fun t => 2 * t) heq)

/-- At most two sheets contribute to volume under shifted folding. -/
lemma map_volume_restrict_shiftedCoordinateFold_le {n : ℕ} (i : Fin n) (δ : ℝ)
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    (hmaps : MapsTo (shiftedCoordinateFold i δ) U V) :
    Measure.map (shiftedCoordinateFold i δ) (volume.restrict U) ≤
      (2 : ℝ≥0∞) • volume.restrict V := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.map_apply (lipschitzWith_shiftedCoordinateFold i δ).continuous.measurable hs,
    Measure.restrict_apply' hU, Measure.smul_apply, Measure.restrict_apply hs]
  change volume (shiftedCoordinateFold i δ ⁻¹' s ∩ U) ≤ 2 * volume (s ∩ V)
  calc
    _ ≤ volume (shiftedCoordinateFold i δ ⁻¹' (s ∩ V)) :=
      measure_mono fun _ hx => ⟨hx.1, hmaps hx.2⟩
    _ ≤ _ := volume_preimage_shiftedCoordinateFold_le i δ (s ∩ V)

lemma integrableOn_comp_shiftedCoordinateFold {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (i : Fin n) (δ : ℝ) {U V : Set (EuclideanSpace ℝ (Fin n))}
    (hU : MeasurableSet U) (hmaps : MapsTo (shiftedCoordinateFold i δ) U V)
    {g : EuclideanSpace ℝ (Fin n) → E} (hg : IntegrableOn g V) :
    IntegrableOn (g ∘ shiftedCoordinateFold i δ) U := by
  have hi := (hg.smul_measure (c := (2 : ℝ≥0∞)) (by norm_num)).mono_measure
    (map_volume_restrict_shiftedCoordinateFold_le i δ hU hmaps)
  exact hi.comp_aemeasurable (lipschitzWith_shiftedCoordinateFold i δ).continuous.aemeasurable

lemma integral_norm_comp_shiftedCoordinateFold_le {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (i : Fin n) (δ : ℝ) {U V : Set (EuclideanSpace ℝ (Fin n))}
    (hU : MeasurableSet U) (hmaps : MapsTo (shiftedCoordinateFold i δ) U V)
    {g : EuclideanSpace ℝ (Fin n) → E} (hg : IntegrableOn g V) :
    (∫ x in U, ‖g (shiftedCoordinateFold i δ x)‖) ≤ 2 * ∫ x in V, ‖g x‖ := by
  have hmap := map_volume_restrict_shiftedCoordinateFold_le i δ hU hmaps
  have hi := hg.norm.smul_measure (c := (2 : ℝ≥0∞)) (by norm_num)
  calc
    _ = ∫ y, ‖g y‖ ∂Measure.map (shiftedCoordinateFold i δ) (volume.restrict U) :=
      (integral_map (lipschitzWith_shiftedCoordinateFold i δ).continuous.aemeasurable
        (hi.mono_measure hmap).aestronglyMeasurable).symm
    _ ≤ ∫ y, ‖g y‖ ∂((2 : ℝ≥0∞) • volume.restrict V) :=
      integral_mono_measure hmap (Eventually.of_forall fun _ => norm_nonneg _) hi
    _ = _ := by simp [integral_smul_measure]

/-- The open coordinate cube of radius `r`. -/
def coordinateCube (n : ℕ) (r : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ j, |x j| < r}

/-- The upper half of the open coordinate cube, with normal coordinate `i`. -/
def coordinateHalfCube {n : ℕ} (i : Fin n) (r : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  coordinateCube n r ∩ {x | 0 < x i}

lemma isOpen_coordinateCube (n : ℕ) (r : ℝ) : IsOpen (coordinateCube n r) := by
  simp only [coordinateCube, ofPred_forall]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt (EuclideanSpace.proj j).continuous.abs continuous_const

lemma isOpen_coordinateHalfCube {n : ℕ} (i : Fin n) (r : ℝ) :
    IsOpen (coordinateHalfCube i r) :=
  (isOpen_coordinateCube n r).inter (isOpen_lt continuous_const (EuclideanSpace.proj i).continuous)

lemma shiftedCoordinateFold_apply {n : ℕ} (i : Fin n) (δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    shiftedCoordinateFold i δ x j = if j = i then |x j| + δ else x j := by
  by_cases hj : j = i
  · subst j
    simp [shiftedCoordinateFold, coordinateFold_apply]
  · simp [shiftedCoordinateFold, coordinateFold_apply, hj]

lemma mapsTo_shiftedCoordinateFold_halfCube {n : ℕ} (i : Fin n)
    {r R δ : ℝ} (hδ : 0 < δ) (hrδ : r + δ ≤ R) :
    MapsTo (shiftedCoordinateFold i δ) (coordinateCube n r) (coordinateHalfCube i R) := by
  intro x hx
  constructor
  · intro j
    rw [shiftedCoordinateFold_apply]
    split_ifs with hj
    · rw [abs_of_nonneg (by positivity)]
      exact (add_lt_add_of_lt_of_le (hx j) le_rfl).trans_le hrδ
    · exact (hx j).trans_le (by linarith)
  · simp only [shiftedCoordinateFold_apply, ite_true, mem_ofPred_eq]
    positivity

lemma shiftedCoordinateFold_zero {n : ℕ} (i : Fin n) :
    shiftedCoordinateFold i 0 = coordinateFold i := by
  funext x
  simp [shiftedCoordinateFold]

lemma integrable_comp_coordinateFold {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (i : Fin n) {g : EuclideanSpace ℝ (Fin n) → E} (hg : Integrable g) :
    Integrable (g ∘ coordinateFold i) := by
  simpa only [shiftedCoordinateFold_zero, integrableOn_univ] using
    integrableOn_comp_shiftedCoordinateFold i 0 MeasurableSet.univ
      (mapsTo_univ _ _) (integrableOn_univ.mpr hg)

/-- Translating into the upper half-space before folding tends to even reflection in L¹. -/
theorem tendsto_integral_norm_shiftedCoordinateFold_sub {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] (i : Fin n) {g : EuclideanSpace ℝ (Fin n) → E}
    (hg : Integrable g) {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0))
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U) :
    Tendsto (fun j => ∫ x in U,
      ‖g (shiftedCoordinateFold i (δ j) x) - g (coordinateFold i x)‖) atTop (𝓝 0) := by
  have ht : Tendsto (fun j => ∫ x,
      ‖g (x + δ j • EuclideanSpace.single i 1) - g x‖) atTop (𝓝 0) := by
    have h := (continuous_integral_norm_translate_sub hg).continuousAt.tendsto.comp
      (hδ.neg.smul_const (EuclideanSpace.single i (1 : ℝ)))
    simpa only [neg_zero, zero_smul, sub_zero, sub_self, norm_zero, integral_zero,
      neg_smul, sub_neg_eq_add, Function.comp_def] using h
  apply squeeze_zero (fun j => integral_nonneg fun _ => norm_nonneg _) (fun j => ?_)
    (by simpa only [mul_zero] using ht.const_mul 2)
  have hi : Integrable (fun x => g (x + δ j • EuclideanSpace.single i 1) - g x) :=
    ((measurePreserving_add_right volume _).integrable_comp_of_integrable hg).sub hg
  have hb := integral_norm_comp_shiftedCoordinateFold_le i 0 hU (mapsTo_univ _ _)
    (integrableOn_univ.mpr hi)
  simpa only [shiftedCoordinateFold, zero_smul, add_zero, setIntegral_univ] using hb

/-- The variation bound for shifted reflection of a smooth function. -/
theorem variation_smooth_shiftedCoordinateFold_le {n : ℕ} (i : Fin n) (δ : ℝ)
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hV : IsOpen V)
    (hmaps : MapsTo (shiftedCoordinateFold i δ) U V)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiffOn ℝ 1 g V)
    (hgrad : IntegrableOn (gradient g) V) :
    variation (g ∘ shiftedCoordinateFold i δ) U ≤
      ENNReal.ofReal (2 * ∫ y in V, ‖gradient g y‖) := by
  have hlip := (lipschitzWith_shiftedCoordinateFold i δ).lipschitzOnWith (s := U)
  have hbound := ae_norm_gradient_comp_le hU hV hg hlip hmaps
  simp only [NNReal.coe_one, one_mul] at hbound
  have hi := integrableOn_comp_shiftedCoordinateFold i δ hU.measurableSet hmaps hgrad
  have hif : IntegrableOn (gradient (g ∘ shiftedCoordinateFold i δ)) U :=
    hi.norm.mono' (measurable_gradient _).aestronglyMeasurable hbound
  apply ((hasWeakGradientOn_comp_of_contDiffOn hU hV hg hlip hmaps).variation_le hif).trans
  apply ENNReal.ofReal_le_ofReal
  exact (integral_mono_ae hif.norm hi.norm hbound).trans
    (integral_norm_comp_shiftedCoordinateFold_le i δ hU.measurableSet hmaps hgrad)

lemma volume_coordinate_hyperplane {n : ℕ} (i : Fin n) :
    volume {x : EuclideanSpace ℝ (Fin n) | x i = 0} = 0 := by
  change volume (↑(LinearMap.ker (EuclideanSpace.proj (𝕜 := ℝ) i).toLinearMap) :
    Set (EuclideanSpace ℝ (Fin n))) = 0
  apply Measure.addHaar_submodule
  rw [Ne, LinearMap.ker_eq_top]
  intro h
  have hv := congrArg (fun L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ =>
    L (EuclideanSpace.single i 1)) h
  simp at hv

lemma ae_coordinate_ne_zero {n : ℕ} (i : Fin n) :
    ∀ᵐ x : EuclideanSpace ℝ (Fin n) ∂volume, x i ≠ 0 := by
  rw [ae_iff]
  simpa only [not_not] using volume_coordinate_hyperplane i

lemma coordinateCube_mono {n : ℕ} {r R : ℝ} (h : r ≤ R) :
    coordinateCube n r ⊆ coordinateCube n R := fun _ hx j => (hx j).trans_le h

lemma coordinateFold_mem_halfCube {n : ℕ} {i : Fin n} {R : ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ coordinateCube n R) (hxi : x i ≠ 0) :
    coordinateFold i x ∈ coordinateHalfCube i R := by
  constructor
  · intro j
    simp only [coordinateFold_apply]
    split_ifs <;> simpa only [abs_abs] using hx j
  · simpa only [coordinateFold_apply, ite_true, mem_ofPred_eq] using abs_pos.mpr hxi

lemma indicator_halfCube_comp_coordinateFold_ae {n : ℕ} (i : Fin n) {r R : ℝ}
    (hrR : r ≤ R) (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    ((coordinateHalfCube i R).indicator g ∘ coordinateFold i) =ᵐ[
      volume.restrict (coordinateCube n r)] (g ∘ coordinateFold i) := by
  filter_upwards [ae_restrict_of_ae (ae_coordinate_ne_zero i),
    ae_restrict_mem (isOpen_coordinateCube n r).measurableSet] with x hx hxQ
  exact indicator_of_mem (coordinateFold_mem_halfCube (coordinateCube_mono hrR hxQ) hx) g

/-- L¹ control of even reflection from a larger half-cube to a smaller cube. -/
theorem integrableOn_coordinateFold_halfCube {n : ℕ} (i : Fin n) {r R : ℝ}
    (hrR : r ≤ R) {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : IntegrableOn g (coordinateHalfCube i R)) :
    IntegrableOn (g ∘ coordinateFold i) (coordinateCube n r) ∧
      (∫ x in coordinateCube n r, ‖g (coordinateFold i x)‖) ≤
        2 * ∫ x in coordinateHalfCube i R, ‖g x‖ := by
  let g0 := (coordinateHalfCube i R).indicator g
  have hg0 : Integrable g0 := hg.integrable_indicator (isOpen_coordinateHalfCube i R).measurableSet
  have hae := indicator_halfCube_comp_coordinateFold_ae i hrR g
  have hi := (integrable_comp_coordinateFold i hg0).integrableOn (s := coordinateCube n r)
  refine ⟨hi.congr hae, ?_⟩
  have hb := integral_norm_comp_shiftedCoordinateFold_le i 0
    (isOpen_coordinateCube n r).measurableSet (mapsTo_univ _ _) (integrableOn_univ.mpr hg0)
  calc
    _ = ∫ x in coordinateCube n r, ‖g0 (coordinateFold i x)‖ :=
      integral_congr_ae (hae.fun_comp (fun y => ‖y‖)).symm
    _ ≤ 2 * ∫ x, ‖g0 x‖ := by
      simpa only [shiftedCoordinateFold_zero, setIntegral_univ] using hb
    _ = _ := by
      simp only [g0, norm_indicator_eq_indicator_norm,
        integral_indicator (isOpen_coordinateHalfCube i R).measurableSet]

/-- Even reflection of BV functions across a flat face. Both L¹ norm and variation
increase by at most a factor of two on every smaller concentric cube. -/
theorem bv_reflection_halfCube {n : ℕ} (i : Fin n) {r R : ℝ} (hrR : r < R)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : IsBVOn g (coordinateHalfCube i R)) :
    IsBVOn (g ∘ coordinateFold i) (coordinateCube n r) ∧
      (∫ x in coordinateCube n r, ‖g (coordinateFold i x)‖) ≤
        2 * ∫ x in coordinateHalfCube i R, ‖g x‖ ∧
      variation (g ∘ coordinateFold i) (coordinateCube n r) ≤
        2 * variation g (coordinateHalfCube i R) := by
  let U := coordinateCube n r
  let V := coordinateHalfCube i R
  have hU : IsOpen U := isOpen_coordinateCube n r
  have hV : IsOpen V := isOpen_coordinateHalfCube i R
  have hbase := integrableOn_coordinateFold_halfCube i hrR.le hg.1
  let g0 := V.indicator g
  have hg0 : Integrable g0 := hg.1.integrable_indicator hV.measurableSet
  have hraw : (g0 ∘ coordinateFold i) =ᵐ[volume.restrict U] (g ∘ coordinateFold i) :=
    indicator_halfCube_comp_coordinateFold_ae i hrR.le g
  obtain ⟨f, hf, hie, he, _, hstrict⟩ := strict_approximation_on hV
    (isLocallyBVOn_of_variation_lt_top hV hg.1.locallyIntegrableOn hg.2)
  obtain ⟨hifgrad, hgradconv⟩ := hstrict hg.2
  let δ (j : ℕ) : ℝ := (R - r) / (j + 1)
  have hδpos (j) : 0 < δ j := div_pos (sub_pos.mpr hrR) (by positivity)
  have hδbound (j) : r + δ j ≤ R := by
    have hdenom : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
    have hle : δ j ≤ R - r := div_le_self (sub_nonneg.mpr hrR.le) hdenom
    linarith
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa only [δ, mul_one_div, mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (R - r)
  have hmaps (j) : MapsTo (shiftedCoordinateFold i (δ j)) U V :=
    mapsTo_shiftedCoordinateFold_halfCube i (hδpos j) (hδbound j)
  have hif (j) : IntegrableOn (f j) V := by
    have h := (hie j).add hg.1
    change IntegrableOn (fun x => (f j x - g x) + g x) V at h
    simpa only [sub_add_cancel] using h
  let F (j : ℕ) := f j ∘ shiftedCoordinateFold i (δ j)
  have hiF (j) : IntegrableOn (F j) U :=
    integrableOn_comp_shiftedCoordinateFold i (δ j) hU.measurableSet (hmaps j) (hif j)
  have hierr (j) := integrableOn_comp_shiftedCoordinateFold i (δ j)
    hU.measurableSet (hmaps j) (hie j)
  have hi0 : IntegrableOn (g0 ∘ coordinateFold i) U :=
    (integrable_comp_coordinateFold i hg0).integrableOn
  have hishift (j) : IntegrableOn (g0 ∘ shiftedCoordinateFold i (δ j)) U :=
    integrableOn_comp_shiftedCoordinateFold i (δ j) hU.measurableSet
      (mapsTo_univ _ _) (integrableOn_univ.mpr hg0)
  have htrans := tendsto_integral_norm_shiftedCoordinateFold_sub i hg0 hδ hU.measurableSet
  have hglobal : Tendsto (fun j => ∫ x in U, |F j x - g (coordinateFold i x)|)
      atTop (𝓝 0) := by
    have ht := (he.const_mul 2).add htrans
    simp only [mul_zero, zero_add] at ht
    apply squeeze_zero (fun j => integral_nonneg fun _ => abs_nonneg _) (fun j => ?_) ht
    calc
      _ ≤ ∫ x in U, ‖f j (shiftedCoordinateFold i (δ j) x) -
          g (shiftedCoordinateFold i (δ j) x)‖ +
          ‖g0 (shiftedCoordinateFold i (δ j) x) - g0 (coordinateFold i x)‖ := by
        apply integral_mono_ae ((hiF j).sub hbase.1).abs
          ((hierr j).norm.add ((hishift j).sub hi0).norm)
        filter_upwards [hraw, ae_restrict_mem hU.measurableSet] with x hx hxU
        change g0 (coordinateFold i x) = g (coordinateFold i x) at hx
        change |f j (shiftedCoordinateFold i (δ j) x) - g (coordinateFold i x)| ≤
          ‖f j (shiftedCoordinateFold i (δ j) x) - g (shiftedCoordinateFold i (δ j) x)‖ +
          ‖g0 (shiftedCoordinateFold i (δ j) x) - g0 (coordinateFold i x)‖
        rw [hx, show g0 (shiftedCoordinateFold i (δ j) x) =
          g (shiftedCoordinateFold i (δ j) x) from indicator_of_mem (hmaps j hxU) g]
        simpa only [Real.norm_eq_abs] using norm_sub_le_norm_sub_add_norm_sub
          (f j (shiftedCoordinateFold i (δ j) x))
          (g (shiftedCoordinateFold i (δ j) x)) (g (coordinateFold i x))
      _ = (∫ x in U, ‖f j (shiftedCoordinateFold i (δ j) x) -
          g (shiftedCoordinateFold i (δ j) x)‖) +
          ∫ x in U, ‖g0 (shiftedCoordinateFold i (δ j) x) - g0 (coordinateFold i x)‖ :=
        integral_add (hierr j).norm ((hishift j).sub hi0).norm
      _ ≤ _ := add_le_add (by
        simpa only [Real.norm_eq_abs] using integral_norm_comp_shiftedCoordinateFold_le
          i (δ j) hU.measurableSet (hmaps j) (hie j)) le_rfl
  have hlocal (A : Set (EuclideanSpace ℝ (Fin n))) (hAU : A ⊆ U) :
      Tendsto (fun j => ∫ x in A, |F j x - g (coordinateFold i x)|) atTop (𝓝 0) := by
    apply squeeze_zero (fun j => integral_nonneg fun _ => abs_nonneg _) (fun j => ?_) hglobal
    exact setIntegral_mono_set ((hiF j).sub hbase.1).abs
      (Eventually.of_forall fun _ => abs_nonneg _) (Eventually.of_forall hAU)
  have hlsc := variation_le_liminf_of_locally_l1 hU
    (fun j => (hiF j).locallyIntegrableOn) hbase.1.locallyIntegrableOn
    (fun A _ hAU => hlocal A hAU)
  have hvar (j) : variation (F j) U ≤
      ENNReal.ofReal (2 * ∫ y in V, ‖gradient (f j) y‖) :=
    variation_smooth_shiftedCoordinateFold_le i (δ j) hU hV (hmaps j)
      ((hf j).of_le (by simp)) (hifgrad j)
  have ht : Tendsto (fun j => ENNReal.ofReal (2 * ∫ y in V, ‖gradient (f j) y‖))
      atTop (𝓝 (2 * variation g V)) := by
    have hvfin : variation g V ≠ ∞ := hg.2.ne
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hgradconv.const_mul 2)
    simpa only [Function.comp_def, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_toReal hvfin] using h
  have hv : variation (g ∘ coordinateFold i) U ≤ 2 * variation g V :=
    hlsc.trans ((liminf_le_liminf (Eventually.of_forall hvar)).trans_eq ht.liminf_eq)
  exact ⟨⟨hbase.1, hv.trans_lt (ENNReal.mul_lt_top (by norm_num) hg.2)⟩, hbase.2, hv⟩

/-- A compact subset of a coordinate cube lies in a strictly smaller concentric cube. -/
lemma exists_smaller_coordinateCube_of_isCompact {n : ℕ} (i : Fin n) {R : ℝ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKR : K ⊆ coordinateCube n R) :
    ∃ r < R, K ⊆ coordinateCube n r := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨R - 1, by linarith, empty_subset _⟩
  choose p hp hmax using fun j : Fin n => hK.exists_isMaxOn hne
    ((EuclideanSpace.proj j).continuous.abs.continuousOn)
  let hn : (Finset.univ : Finset (Fin n)).Nonempty := ⟨i, Finset.mem_univ i⟩
  let M := Finset.univ.sup' hn (fun j => |p j j|)
  have hMR : M < R := (Finset.sup'_lt_iff hn).mpr fun j _ => hKR (hp j) j
  refine ⟨(M + R) / 2, by linarith, ?_⟩
  intro x hx j
  have hle : |x j| ≤ M := (hmax j hx).trans (Finset.le_sup' (fun j => |p j j|)
    (Finset.mem_univ j))
  linarith

/-- Flat BV reflection on the full open cube, with separate sharp factor-two bounds.
Compact support of the variation tests lets the smaller-cube estimates exhaust the cube. -/
theorem bv_reflection_cube {n : ℕ} (i : Fin n) (R : ℝ)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : IsBVOn g (coordinateHalfCube i R)) :
    IsBVOn (g ∘ coordinateFold i) (coordinateCube n R) ∧
      (∫ x in coordinateCube n R, ‖g (coordinateFold i x)‖) ≤
        2 * ∫ x in coordinateHalfCube i R, ‖g x‖ ∧
      variation (g ∘ coordinateFold i) (coordinateCube n R) ≤
        2 * variation g (coordinateHalfCube i R) := by
  have hi := integrableOn_coordinateFold_halfCube i (le_refl R) hg.1
  have hv : variation (g ∘ coordinateFold i) (coordinateCube n R) ≤
      2 * variation g (coordinateHalfCube i R) := by
    apply iSup_le
    intro X
    apply iSup_le
    intro hX
    obtain ⟨r, hrR, hsr⟩ := exists_smaller_coordinateCube_of_isCompact i hX.2.1 hX.2.2.1
    have htest : IsVariationTestField (coordinateCube n r) X :=
      ⟨hX.1, hX.2.1, hsr, hX.2.2.2⟩
    have heq : (∫ x in coordinateCube n R, (g ∘ coordinateFold i) x * divergenceN X x) =
        ∫ x in coordinateCube n r, (g ∘ coordinateFold i) x * divergenceN X x := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        (isOpen_coordinateCube n R).measurableSet (coordinateCube_mono hrR.le)
      intro x hx
      rw [divergenceN_eq_zero_of_notMem_tsupport (fun h => hx.2 (hsr h)), mul_zero]
    rw [heq]
    calc
      _ ≤ variation (g ∘ coordinateFold i) (coordinateCube n r) :=
        le_iSup_of_le X (le_iSup_of_le htest le_rfl)
      _ ≤ _ := (bv_reflection_halfCube i hrR hg).2.2
  exact ⟨⟨hi.1, hv.trans_lt (ENNReal.mul_lt_top (by norm_num) hg.2)⟩, hi.2, hv⟩

/-- The actual even-reflection operation is linear on scalar representatives. -/
noncomputable def evenReflectionLinearMap {n : ℕ} (i : Fin n) :
    (EuclideanSpace ℝ (Fin n) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n) → ℝ) where
  toFun g := g ∘ coordinateFold i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma evenReflection_eq_on_halfCube {n : ℕ} (i : Fin n) (R : ℝ)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    EqOn (evenReflectionLinearMap i g) g (coordinateHalfCube i R) := by
  intro x hx
  change g (coordinateFold i x) = g x
  rw [coordinateFold_eq_self hx.2.le]

/-- A uniform cutoff estimate for the BV norm, in the existing variation convention. -/
theorem variation_mul_compact_factor_le {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f ζ : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsBVOn f U)
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ U)
    {A B : ℝ}
    (hbζ : ∀ x, ‖ζ x‖ ≤ A) (hbgrad : ∀ x, ‖gradient ζ x‖ ≤ B) :
    variation (fun x => ζ x * f x) univ ≤
      ENNReal.ofReal (A * (variation f U).toReal + B * ∫ x in U, ‖f x‖) := by
  have hlocal := isLocallyBVOn_of_variation_lt_top hU hf.1.locallyIntegrableOn hf.2
  obtain ⟨ρ, σ, hρ, _, hpolar⟩ := exists_distributional_polar_representation hU hlocal
  let : ρ.Regular := hρ
  have hmass : variation f U = ρ univ := by
    simpa only [Subtype.coe_preimage_self] using
      hpolar.variation_eq_measure hU hU Subset.rfl hf.1.locallyIntegrableOn
  let : IsFiniteMeasure ρ := ⟨hmass ▸ hf.2⟩
  have hiζσ := hpolar.integrable_smul_compact_factor hζ.continuous hcζ hsζ
  have hfirst : (∫ x : U, ‖ζ x • σ x‖ ∂ρ) ≤ A * (variation f U).toReal := by
    calc
      _ ≤ ∫ _ : U, A ∂ρ := by
        apply integral_mono_ae hiζσ.norm (integrable_const A)
        filter_upwards [hpolar.norm_ae] with x hx
        simpa only [norm_smul, hx, mul_one] using hbζ x
      _ = _ := by simp only [integral_const, smul_eq_mul, Measure.real, hmass, mul_comm]
  have hiG := integrable_smul_gradient hf.1.locallyIntegrableOn hζ hcζ hsζ
  have hsecond : (∫ x, ‖f x • gradient ζ x‖) ≤ B * ∫ x in U, ‖f x‖ := by
    calc
      _ = ∫ x in U, ‖f x • gradient ζ x‖ := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        rw [gradient_eq_zero_of_notMem_tsupport (fun h => hx (hsζ h)), smul_zero, norm_zero]
      _ ≤ ∫ x in U, B * ‖f x‖ := by
        apply integral_mono_ae hiG.norm.integrableOn (hf.1.norm.const_mul B)
        exact Eventually.of_forall fun x => by
          change ‖f x • gradient ζ x‖ ≤ B * ‖f x‖
          rw [norm_smul, mul_comm B]
          exact mul_le_mul_of_nonneg_left (hbgrad x) (norm_nonneg _)
      _ = _ := integral_const_mul _ _
  exact (hpolar.variation_mul_le hf.1.locallyIntegrableOn hζ hcζ hsζ).trans
    (ENNReal.ofReal_le_ofReal (add_le_add hfirst hsecond))

/-- The L¹ bound for multiplication by a supported, uniformly bounded cutoff. -/
lemma integral_norm_mul_compact_factor_le {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f ζ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : IntegrableOn f U) (hζ : Continuous ζ) (hcζ : HasCompactSupport ζ)
    (hsζ : tsupport ζ ⊆ U) {A : ℝ} (hbζ : ∀ x, ‖ζ x‖ ≤ A) :
    (∫ x, ‖ζ x * f x‖) ≤ A * ∫ x in U, ‖f x‖ := by
  have hi := integrable_mul_compact_factor hf.locallyIntegrableOn hζ hcζ hsζ
  calc
    _ = ∫ x in U, ‖ζ x * f x‖ := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsζ h)), zero_mul, norm_zero]
    _ ≤ ∫ x in U, A * ‖f x‖ := by
      apply integral_mono_ae hi.norm.integrableOn (hf.norm.const_mul A)
      exact Eventually.of_forall fun x => by
        change ‖ζ x * f x‖ ≤ A * ‖f x‖
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hbζ x) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

/-- A fixed smooth cutoff turns flat reflection into a compactly supported global BV function,
with a bound independent of the reflected function. -/
theorem bv_compact_reflection {n : ℕ} (i : Fin n) (R : ℝ)
    {g ζ : EuclideanSpace ℝ (Fin n) → ℝ} (hg : IsBVOn g (coordinateHalfCube i R))
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ)
    (hsζ : tsupport ζ ⊆ coordinateCube n R)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbζ : ∀ x, ‖ζ x‖ ≤ A) (hbgrad : ∀ x, ‖gradient ζ x‖ ≤ B) :
    IsBVOn (fun x => ζ x * g (coordinateFold i x)) univ ∧
      tsupport (fun x => ζ x * g (coordinateFold i x)) ⊆ tsupport ζ ∧
      (∫ x, ‖ζ x * g (coordinateFold i x)‖) ≤
        2 * A * ∫ x in coordinateHalfCube i R, ‖g x‖ ∧
      variation (fun x => ζ x * g (coordinateFold i x)) univ ≤
        ENNReal.ofReal (2 * A * (variation g (coordinateHalfCube i R)).toReal +
          2 * B * ∫ x in coordinateHalfCube i R, ‖g x‖) := by
  have hR := bv_reflection_cube i R hg
  have hU := isOpen_coordinateCube n R
  have hlocal := isLocallyBVOn_of_variation_lt_top hU hR.1.1.locallyIntegrableOn hR.1.2
  refine ⟨hlocal.isBVOn_mul_compact_factor hU hζ hcζ hsζ,
    tsupport_mul_subset_left, ?_, ?_⟩
  · calc
      _ ≤ A * ∫ x in coordinateCube n R, ‖g (coordinateFold i x)‖ :=
        integral_norm_mul_compact_factor_le hR.1.1 hζ.continuous hcζ hsζ hbζ
      _ ≤ A * (2 * ∫ x in coordinateHalfCube i R, ‖g x‖) :=
        mul_le_mul_of_nonneg_left hR.2.1 hA
      _ = _ := by ring
  · have hvreal : (variation (g ∘ coordinateFold i) (coordinateCube n R)).toReal ≤
        2 * (variation g (coordinateHalfCube i R)).toReal := by
      have h := ENNReal.toReal_mono
        (ENNReal.mul_lt_top (by norm_num) hg.2).ne hR.2.2
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] using h
    apply (variation_mul_compact_factor_le hU hR.1 hζ hcζ hsζ hbζ hbgrad).trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ A * (2 * (variation g (coordinateHalfCube i R)).toReal) +
          B * (2 * ∫ x in coordinateHalfCube i R, ‖g x‖) :=
        add_le_add (mul_le_mul_of_nonneg_left hvreal hA) (mul_le_mul_of_nonneg_left hR.2.1 hB)
      _ = _ := by ring
/-- Erase the normal coordinate, retaining the tangential coordinates of a graph chart. -/
noncomputable def coordinateErase {n : ℕ} (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => if j = i then 0 else x j)

lemma coordinateErase_apply {n : ℕ} (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    coordinateErase i x j = if j = i then 0 else x j := rfl

lemma lipschitzWith_coordinateErase {n : ℕ} (i : Fin n) :
    LipschitzWith 1 (coordinateErase i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, PiLp.dist_eq_of_L2]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j = i
  · simp only [coordinateErase_apply, hj, ite_true, dist_self, zero_pow (by norm_num : 2 ≠ 0)]
    positivity
  · simp only [coordinateErase_apply, ite_eq_right hj, le_refl]

/-- The shear taking a flat boundary to the graph of a tangential height function. -/
noncomputable def graphShear {n : ℕ} (i : Fin n)
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) := x + h (coordinateErase i x) • EuclideanSpace.single i 1

lemma graphShear_apply {n : ℕ} (i : Fin n) (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    graphShear i h x j = if j = i then x j + h (coordinateErase i x) else x j := by
  by_cases hj : j = i
  · subst j
    simp [graphShear]
  · simp [graphShear, hj]

lemma coordinateErase_graphShear {n : ℕ} (i : Fin n)
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    coordinateErase i (graphShear i h x) = coordinateErase i x := by
  ext j
  by_cases hj : j = i <;> simp [coordinateErase_apply, graphShear_apply, hj]

lemma graphShear_neg_leftInverse {n : ℕ} (i : Fin n)
    (h : EuclideanSpace ℝ (Fin n) → ℝ) :
    Function.LeftInverse (graphShear i (-h)) (graphShear i h) := by
  intro x
  ext j
  by_cases hj : j = i <;>
    simp [graphShear_apply, coordinateErase_graphShear, hj]

lemma graphShear_neg_rightInverse {n : ℕ} (i : Fin n)
    (h : EuclideanSpace ℝ (Fin n) → ℝ) :
    Function.RightInverse (graphShear i (-h)) (graphShear i h) := by
  change Function.LeftInverse (graphShear i h) (graphShear i (-h))
  simpa only [neg_neg] using graphShear_neg_leftInverse i (-h)

lemma lipschitzWith_graphShear {n : ℕ} (i : Fin n)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0} (hh : LipschitzWith L h) :
    LipschitzWith (1 + L) (graphShear i h) := by
  have ht : LipschitzWith L (h ∘ coordinateErase i) := by
    simpa only [mul_one] using hh.comp (lipschitzWith_coordinateErase i)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    _ ≤ dist x y + dist (h (coordinateErase i x) • EuclideanSpace.single i 1)
        (h (coordinateErase i y) • EuclideanSpace.single i 1) := dist_add_add_le _ _ _ _
    _ = dist x y + dist (h (coordinateErase i x)) (h (coordinateErase i y)) := by
      congr 1
      rw [dist_eq_norm, ← sub_smul, norm_smul, PiLp.norm_single, norm_one, mul_one, dist_eq_norm]
    _ ≤ dist x y + L * dist x y := add_le_add le_rfl (ht.dist_le_mul x y)
    _ = _ := by simp only [NNReal.coe_add, NNReal.coe_one]; ring

/-- A Lipschitz graph is flattened by a global bi-Lipschitz homeomorphism. -/
noncomputable def graphShearHomeomorph {n : ℕ} (i : Fin n)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0} (hh : LipschitzWith L h) :
    EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) where
  toFun := graphShear i h
  invFun := graphShear i (-h)
  left_inv := graphShear_neg_leftInverse i h
  right_inv := graphShear_neg_rightInverse i h
  continuous_toFun := (lipschitzWith_graphShear i hh).continuous
  continuous_invFun := (lipschitzWith_graphShear i hh.neg).continuous

/-- The image of a coordinate cube under the graph shear. -/
def graphChartCube {n : ℕ} (i : Fin n) (h : EuclideanSpace ℝ (Fin n) → ℝ) (R : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) := graphShear i h '' coordinateCube n R

/-- The side of the graph chart lying above its boundary. -/
def graphChartHalfCube {n : ℕ} (i : Fin n) (h : EuclideanSpace ℝ (Fin n) → ℝ) (R : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) := graphShear i h '' coordinateHalfCube i R

lemma isOpen_graphChartCube {n : ℕ} (i : Fin n) (R : ℝ)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0} (hh : LipschitzWith L h) :
    IsOpen (graphChartCube i h R) :=
  (graphShearHomeomorph i hh).isOpenMap _ (isOpen_coordinateCube n R)

lemma isOpen_graphChartHalfCube {n : ℕ} (i : Fin n) (R : ℝ)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0} (hh : LipschitzWith L h) :
    IsOpen (graphChartHalfCube i h R) :=
  (graphShearHomeomorph i hh).isOpenMap _ (isOpen_coordinateHalfCube i R)

lemma mem_graphChartHalfCube_iff {n : ℕ} (i : Fin n)
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (R : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ graphChartHalfCube i h R ↔
      x ∈ graphChartCube i h R ∧ h (coordinateErase i x) < x i := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y, hy.1, rfl⟩, ?_⟩
    simp only [coordinateErase_graphShear, graphShear_apply, ite_true]
    have hp : 0 < y i := hy.2
    linarith
  · rintro ⟨⟨y, hy, rfl⟩, hheight⟩
    refine ⟨y, ⟨hy, ?_⟩, rfl⟩
    simp only [coordinateErase_graphShear, graphShear_apply, ite_true] at hheight
    change 0 < y i
    linarith

/-- Pull back to a flat cube, reflect there, and return to the original chart. -/
noncomputable def chartReflectionLinearMap {n : ℕ} (i : Fin n)
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n)) :
    (EuclideanSpace ℝ (Fin n) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n) → ℝ) where
  toFun g := fun x => g (e (coordinateFold i (e.symm x)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma chartReflection_eq_on_halfCube {n : ℕ} (i : Fin n) (R : ℝ)
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    EqOn (chartReflectionLinearMap i e g) g (e '' coordinateHalfCube i R) := by
  rintro x ⟨y, hy, rfl⟩
  change g (e (coordinateFold i (e.symm (e y)))) = g (e y)
  rw [e.symm_apply_apply, coordinateFold_eq_self hy.2.le]

/-- Even reflection in any bi-Lipschitz cube chart, with an explicit BV norm bound. -/
theorem bv_chart_reflection {n : ℕ} (i : Fin n) (R : ℝ)
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n)) {C K : ℝ≥0}
    (he : LipschitzWith C e) (heinverse : LipschitzWith K e.symm)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : IsBVOn g (e '' coordinateHalfCube i R)) :
    IsBVOn (chartReflectionLinearMap i e g) (e '' coordinateCube n R) ∧
      (∫ x in e '' coordinateCube n R, ‖chartReflectionLinearMap i e g x‖) +
          (variation (chartReflectionLinearMap i e g) (e '' coordinateCube n R)).toReal ≤
        (2 * (max 1 (C : ℝ) * (K : ℝ) ^ n) * (max 1 (K : ℝ) * (C : ℝ) ^ n)) *
          ((∫ y in e '' coordinateHalfCube i R, ‖g y‖) +
            (variation g (e '' coordinateHalfCube i R)).toReal) := by
  have hQ := isOpen_coordinateCube n R
  have hQplus := isOpen_coordinateHalfCube i R
  have hpull := bv_comp_of_lipschitz_leftInverse hQplus (e.isOpenMap _ hQplus)
    he.lipschitzOnWith heinverse.lipschitzOnWith
    (mapsTo_image _ _) (fun _ _ => e.symm_apply_apply _) hg
  have hreflect := bv_reflection_cube i R hpull.1
  have hpush := bv_comp_of_lipschitz_leftInverse (e.isOpenMap _ hQ) hQ
    heinverse.lipschitzOnWith he.lipschitzOnWith
    (fun _ hx => by obtain ⟨y, hy, rfl⟩ := hx; simpa only [e.symm_apply_apply] using hy)
    (fun _ _ => e.apply_symm_apply _) hreflect.1
  refine ⟨hpush.1, ?_⟩
  have hvreal : (variation ((g ∘ e) ∘ coordinateFold i) (coordinateCube n R)).toReal ≤
      2 * (variation (g ∘ e) (coordinateHalfCube i R)).toReal := by
    have h := ENNReal.toReal_mono (ENNReal.mul_lt_top (by norm_num) hpull.1.2).ne hreflect.2.2
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] using h
  have hsum : (∫ x in coordinateCube n R, ‖g (e (coordinateFold i x))‖) +
      (variation ((g ∘ e) ∘ coordinateFold i) (coordinateCube n R)).toReal ≤
        2 * ((∫ y in coordinateHalfCube i R, ‖g (e y)‖) +
          (variation (g ∘ e) (coordinateHalfCube i R)).toReal) := by
    simpa only [mul_add, Function.comp_def] using add_le_add hreflect.2.1 hvreal
  calc
    _ ≤ (max 1 (K : ℝ) * (C : ℝ) ^ n) *
        ((∫ x in coordinateCube n R, ‖g (e (coordinateFold i x))‖) +
          (variation ((g ∘ e) ∘ coordinateFold i) (coordinateCube n R)).toReal) := hpush.2
    _ ≤ (max 1 (K : ℝ) * (C : ℝ) ^ n) *
        (2 * ((∫ y in coordinateHalfCube i R, ‖g (e y)‖) +
          (variation (g ∘ e) (coordinateHalfCube i R)).toReal)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (max 1 (K : ℝ) * (C : ℝ) ^ n) *
        (2 * ((max 1 (C : ℝ) * (K : ℝ) ^ n) *
          ((∫ y in e '' coordinateHalfCube i R, ‖g y‖) +
            (variation g (e '' coordinateHalfCube i R)).toReal))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpull.2 (by norm_num)) (by positivity)
    _ = _ := by ring

/-- The graph-chart instance of the quantitative reflection construction. -/
theorem bv_graph_reflection {n : ℕ} (i : Fin n) (R : ℝ)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0} (hh : LipschitzWith L h)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : IsBVOn g (graphChartHalfCube i h R)) :
    IsBVOn (chartReflectionLinearMap i (graphShearHomeomorph i hh) g) (graphChartCube i h R) ∧
      (∫ x in graphChartCube i h R,
          ‖chartReflectionLinearMap i (graphShearHomeomorph i hh) g x‖) +
          (variation (chartReflectionLinearMap i (graphShearHomeomorph i hh) g)
            (graphChartCube i h R)).toReal ≤
        2 * ((1 + (L : ℝ)) * (1 + (L : ℝ)) ^ n) ^ 2 *
          ((∫ y in graphChartHalfCube i h R, ‖g y‖) +
            (variation g (graphChartHalfCube i h R)).toReal) := by
  have hb := bv_chart_reflection i R (graphShearHomeomorph i hh)
    (lipschitzWith_graphShear i hh) (lipschitzWith_graphShear i hh.neg) hg
  refine ⟨hb.1, ?_⟩
  have hmax : max 1 (1 + (L : ℝ)) = 1 + L := max_eq_right (by linarith [L.coe_nonneg])
  have heq : 2 * (max 1 ((1 + L : ℝ≥0) : ℝ) * (((1 + L : ℝ≥0) : ℝ)) ^ n) *
      (max 1 ((1 + L : ℝ≥0) : ℝ) * (((1 + L : ℝ≥0) : ℝ)) ^ n) =
      2 * ((1 + (L : ℝ)) * (1 + (L : ℝ)) ^ n) ^ 2 := by
    simp only [NNReal.coe_add, NNReal.coe_one, hmax]
    ring
  rw [heq] at hb
  exact hb.2

/-- A fixed compact cutoff acts boundedly on BV, with the quantitative full norm estimate. -/
theorem bv_norm_mul_compact_factor_le {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f ζ : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsBVOn f U)
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ U)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbζ : ∀ x, ‖ζ x‖ ≤ A) (hbgrad : ∀ x, ‖gradient ζ x‖ ≤ B) :
    IsBVOn (fun x => ζ x * f x) univ ∧
      (∫ x, ‖ζ x * f x‖) + (variation (fun x => ζ x * f x) univ).toReal ≤
        (A + B) * ((∫ x in U, ‖f x‖) + (variation f U).toReal) := by
  have hlocal := isLocallyBVOn_of_variation_lt_top hU hf.1.locallyIntegrableOn hf.2
  refine ⟨hlocal.isBVOn_mul_compact_factor hU hζ hcζ hsζ, ?_⟩
  have hv := variation_mul_compact_factor_le hU hf hζ hcζ hsζ hbζ hbgrad
  have hvreal := ENNReal.toReal_le_of_le_ofReal (by positivity) hv
  have hL := integral_norm_mul_compact_factor_le hf.1 hζ.continuous hcζ hsζ hbζ
  have hv0 : 0 ≤ (variation f U).toReal := ENNReal.toReal_nonneg
  nlinarith [mul_nonneg hB hv0]

/-- A local chart extension, multiplied by one fixed smooth cutoff. -/
noncomputable def cutoffChartReflectionLinearMap {n : ℕ} (i : Fin n)
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    (ζ : EuclideanSpace ℝ (Fin n) → ℝ) :
    (EuclideanSpace ℝ (Fin n) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n) → ℝ) where
  toFun g := fun x => ζ x * chartReflectionLinearMap i e g x
  map_add' f g := by
    ext x
    change ζ x * (f (e (coordinateFold i (e.symm x))) + g (e (coordinateFold i (e.symm x)))) = _
    simp only [mul_add, Pi.add_apply, chartReflectionLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
  map_smul' c g := by
    ext x
    change ζ x * (c * g (e (coordinateFold i (e.symm x)))) =
      c * (ζ x * g (e (coordinateFold i (e.symm x))))
    ring

/-- Compact local extension on a bi-Lipschitz chart, with uniform support and norm control. -/
theorem bv_cutoff_chart_reflection {n : ℕ} (i : Fin n) (R : ℝ)
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n)) {C K : ℝ≥0}
    (he : LipschitzWith C e) (heinverse : LipschitzWith K e.symm)
    {g ζ : EuclideanSpace ℝ (Fin n) → ℝ} (hg : IsBVOn g (e '' coordinateHalfCube i R))
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ)
    (hsζ : tsupport ζ ⊆ e '' coordinateCube n R)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbζ : ∀ x, ‖ζ x‖ ≤ A) (hbgrad : ∀ x, ‖gradient ζ x‖ ≤ B) :
    IsBVOn (cutoffChartReflectionLinearMap i e ζ g) univ ∧
      tsupport (cutoffChartReflectionLinearMap i e ζ g) ⊆ tsupport ζ ∧
      (∫ x, ‖cutoffChartReflectionLinearMap i e ζ g x‖) +
          (variation (cutoffChartReflectionLinearMap i e ζ g) univ).toReal ≤
        ((A + B) * (2 * (max 1 (C : ℝ) * (K : ℝ) ^ n) *
          (max 1 (K : ℝ) * (C : ℝ) ^ n))) *
          ((∫ y in e '' coordinateHalfCube i R, ‖g y‖) +
            (variation g (e '' coordinateHalfCube i R)).toReal) := by
  have hR := bv_chart_reflection i R e he heinverse hg
  have hb := bv_norm_mul_compact_factor_le (e.isOpenMap _ (isOpen_coordinateCube n R))
    hR.1 hζ hcζ hsζ hA hB hbζ hbgrad
  refine ⟨hb.1, tsupport_mul_subset_left, ?_⟩
  calc
    _ ≤ (A + B) *
        ((∫ x in e '' coordinateCube n R, ‖chartReflectionLinearMap i e g x‖) +
          (variation (chartReflectionLinearMap i e g) (e '' coordinateCube n R)).toReal) := hb.2
    _ ≤ (A + B) *
        ((2 * (max 1 (C : ℝ) * (K : ℝ) ^ n) * (max 1 (K : ℝ) * (C : ℝ) ^ n)) *
          ((∫ y in e '' coordinateHalfCube i R, ‖g y‖) +
            (variation g (e '' coordinateHalfCube i R)).toReal)) :=
      mul_le_mul_of_nonneg_left hR.2 (add_nonneg hA hB)
    _ = _ := (mul_assoc _ _ _).symm

/-- A reflected chart piece agrees with the cutoff times the original function everywhere
in the original domain, including outside the chart where the cutoff vanishes. -/
lemma cutoffChartReflection_eq_on_domain {n : ℕ} (i : Fin n) (R : ℝ)
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    {D : Set (EuclideanSpace ℝ (Fin n))}
    (hchart : e '' coordinateHalfCube i R = D ∩ e '' coordinateCube n R)
    {ζ : EuclideanSpace ℝ (Fin n) → ℝ} (hsζ : tsupport ζ ⊆ e '' coordinateCube n R)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    EqOn (cutoffChartReflectionLinearMap i e ζ g) (fun x => ζ x * g x) D := by
  intro x hxD
  change ζ x * chartReflectionLinearMap i e g x = ζ x * g x
  by_cases hx : ζ x = 0
  · simp only [hx, zero_mul]
  · have hxchart : x ∈ e '' coordinateCube n R := hsζ (subset_tsupport ζ hx)
    have hxhalf : x ∈ e '' coordinateHalfCube i R := hchart.symm ▸ ⟨hxD, hxchart⟩
    rw [chartReflection_eq_on_halfCube i R e g hxhalf]

/-- A local boundary-chart extension controlled by the BV norm on the entire domain. -/
theorem bv_local_chart_extension {n : ℕ} (i : Fin n) (R : ℝ)
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n)) {C K : ℝ≥0}
    (he : LipschitzWith C e) (heinverse : LipschitzWith K e.symm)
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (hchart : e '' coordinateHalfCube i R = D ∩ e '' coordinateCube n R)
    {g ζ : EuclideanSpace ℝ (Fin n) → ℝ} (hg : IsBVOn g D)
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ)
    (hsζ : tsupport ζ ⊆ e '' coordinateCube n R)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbζ : ∀ x, ‖ζ x‖ ≤ A) (hbgrad : ∀ x, ‖gradient ζ x‖ ≤ B) :
    IsBVOn (cutoffChartReflectionLinearMap i e ζ g) univ ∧
      EqOn (cutoffChartReflectionLinearMap i e ζ g) (fun x => ζ x * g x) D ∧
      tsupport (cutoffChartReflectionLinearMap i e ζ g) ⊆ tsupport ζ ∧
      (∫ x, ‖cutoffChartReflectionLinearMap i e ζ g x‖) +
          (variation (cutoffChartReflectionLinearMap i e ζ g) univ).toReal ≤
        ((A + B) * (2 * (max 1 (C : ℝ) * (K : ℝ) ^ n) *
          (max 1 (K : ℝ) * (C : ℝ) ^ n))) *
          ((∫ y in D, ‖g y‖) + (variation g D).toReal) := by
  have hsub : e '' coordinateHalfCube i R ⊆ D := by rw [hchart]; exact inter_subset_left
  have hv := variation_mono (f := g) hD.measurableSet hsub
  have hgsmall : IsBVOn g (e '' coordinateHalfCube i R) :=
    ⟨hg.1.mono_set hsub, hv.trans_lt hg.2⟩
  have hb := bv_cutoff_chart_reflection i R e he heinverse hgsmall
    hζ hcζ hsζ hA hB hbζ hbgrad
  refine ⟨hb.1, cutoffChartReflection_eq_on_domain i R e hchart hsζ g, hb.2.1, ?_⟩
  apply hb.2.2.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add
    (setIntegral_mono_set hg.1.norm (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall hsub)) (ENNReal.toReal_mono hg.2.ne hv)

/-- A graph chart allows an arbitrary rigid placement in Euclidean space. -/
noncomputable def placedGraphHomeomorph {n : ℕ} (i : Fin n)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0} (hh : LipschitzWith L h)
    (a : EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) :=
  (graphShearHomeomorph i hh).trans a.toHomeomorph

lemma lipschitzWith_placedGraphHomeomorph {n : ℕ} (i : Fin n)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0} (hh : LipschitzWith L h)
    (a : EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n)) :
    LipschitzWith (1 + L) (placedGraphHomeomorph i hh a) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (a (graphShear i h x)) (a (graphShear i h y)) ≤ _
  rw [a.isometry.dist_eq]
  exact (lipschitzWith_graphShear i hh).dist_le_mul x y

lemma lipschitzWith_placedGraphHomeomorph_symm {n : ℕ} (i : Fin n)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0} (hh : LipschitzWith L h)
    (a : EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n)) :
    LipschitzWith (1 + L) (placedGraphHomeomorph i hh a).symm := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (graphShear i (-h) (a.symm x)) (graphShear i (-h) (a.symm y)) ≤ _
  calc
    _ ≤ (1 + L : ℝ≥0) * dist (a.symm x) (a.symm y) :=
      (lipschitzWith_graphShear i hh.neg).dist_le_mul _ _
    _ = _ := by rw [a.symm.isometry.dist_eq]

/-- A one-sided Lipschitz graph chart, including its rotation and translation. -/
structure LipschitzGraphChart (n : ℕ) where
  normal : Fin n
  radius : ℝ
  radius_pos : 0 < radius
  height : EuclideanSpace ℝ (Fin n) → ℝ
  lip : ℝ≥0
  height_lipschitz : LipschitzWith lip height
  placement : EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n)

noncomputable def LipschitzGraphChart.homeomorph {n : ℕ} (c : LipschitzGraphChart n) :
    EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) :=
  placedGraphHomeomorph c.normal c.height_lipschitz c.placement

def LipschitzGraphChart.region {n : ℕ} (c : LipschitzGraphChart n) :
    Set (EuclideanSpace ℝ (Fin n)) := c.homeomorph '' coordinateCube n c.radius

def LipschitzGraphChart.upperRegion {n : ℕ} (c : LipschitzGraphChart n) :
    Set (EuclideanSpace ℝ (Fin n)) := c.homeomorph '' coordinateHalfCube c.normal c.radius

/-- The domain occupies precisely the side above the graph within the chart. -/
def LipschitzGraphChart.IsChartFor {n : ℕ} (c : LipschitzGraphChart n)
    (D : Set (EuclideanSpace ℝ (Fin n))) : Prop := c.upperRegion = D ∩ c.region

/-- Every boundary point has a neighborhood in which the domain is a one-sided
Lipschitz graph. The chart height is global; scalar Lipschitz extension permits
any height originally specified only on the tangential chart. -/
def HasLipschitzBoundary {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ x ∈ frontier D, ∃ c : LipschitzGraphChart n, c.IsChartFor D ∧ x ∈ c.region

lemma LipschitzGraphChart.lipschitz {n : ℕ} (c : LipschitzGraphChart n) :
    LipschitzWith (1 + c.lip) c.homeomorph :=
  lipschitzWith_placedGraphHomeomorph c.normal c.height_lipschitz c.placement

lemma LipschitzGraphChart.lipschitz_symm {n : ℕ} (c : LipschitzGraphChart n) :
    LipschitzWith (1 + c.lip) c.homeomorph.symm :=
  lipschitzWith_placedGraphHomeomorph_symm c.normal c.height_lipschitz c.placement

lemma LipschitzGraphChart.isOpen_region {n : ℕ} (c : LipschitzGraphChart n) :
    IsOpen c.region := c.homeomorph.isOpenMap _ (isOpen_coordinateCube n c.radius)

lemma LipschitzGraphChart.isOpen_upperRegion {n : ℕ} (c : LipschitzGraphChart n) :
    IsOpen c.upperRegion :=
  c.homeomorph.isOpenMap _ (isOpen_coordinateHalfCube c.normal c.radius)

lemma isBounded_coordinateCube (n : ℕ) (R : ℝ) :
    Bornology.IsBounded (coordinateCube n R) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨Real.sqrt (∑ _j : Fin n, |R| ^ 2), fun x hx => ?_⟩
  rw [PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro j _
  have hj : ‖x j‖ ≤ |R| := (hx j).le.trans (le_abs_self R)
  exact pow_le_pow_left₀ (norm_nonneg _) hj 2

lemma LipschitzGraphChart.isBounded_region {n : ℕ} (c : LipschitzGraphChart n) :
    Bornology.IsBounded c.region := c.lipschitz.isBounded_image
      (isBounded_coordinateCube n c.radius)

/-- The interior patch together with all valid boundary chart regions. -/
def boundaryExtensionRegion {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n))) :
    Option {c : LipschitzGraphChart n // c.IsChartFor D} → Set (EuclideanSpace ℝ (Fin n))
  | none => D
  | some c => c.val.region

/-- A bounded domain with Lipschitz boundary has a finite bounded open chart cover
of its closure, selected from the interior patch and boundary chart regions. -/
theorem exists_finite_boundary_chart_cover {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ s : Finset (Option {c : LipschitzGraphChart n // c.IsChartFor D}),
      (∀ i, IsOpen (boundaryExtensionRegion D i)) ∧
      (∀ i, Bornology.IsBounded (boundaryExtensionRegion D i)) ∧
      closure D ⊆ ⋃ i ∈ s, boundaryExtensionRegion D i := by
  have hopen : ∀ i, IsOpen (boundaryExtensionRegion D i) := by
    rintro (_ | c)
    · exact hD
    · exact c.val.isOpen_region
  have hbounded : ∀ i, Bornology.IsBounded (boundaryExtensionRegion D i) := by
    rintro (_ | c)
    · exact hbD
    · exact c.val.isBounded_region
  have hcover : closure D ⊆ ⋃ i, boundaryExtensionRegion D i := by
    rw [closure_eq_self_union_frontier]
    rintro x (hx | hx)
    · exact mem_iUnion.mpr ⟨none, hx⟩
    · obtain ⟨c, hc, hxc⟩ := hL x hx
      exact mem_iUnion.mpr ⟨some ⟨c, hc⟩, hxc⟩
  obtain ⟨s, hs⟩ := hbD.isCompact_closure.elim_finite_subcover
    (boundaryExtensionRegion D) hopen hcover
  exact ⟨s, hopen, hbounded, hs⟩


/-- The fixed interior cutoff or the fixed reflected boundary cutoff, according to
which member of the finite cover is being used. -/
noncomputable def boundaryExtensionPiece {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (i : Option {c : LipschitzGraphChart n // c.IsChartFor D})
    (ζ : EuclideanSpace ℝ (Fin n) → ℝ) :
    (EuclideanSpace ℝ (Fin n) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n) → ℝ) :=
  match i with
  | none => { toFun := fun g x => ζ x * g x
              map_add' := by intro f g; ext x; exact mul_add _ _ _
              map_smul' := by intro c g; ext x; exact mul_left_comm _ _ _ }
  | some c => cutoffChartReflectionLinearMap c.val.normal c.val.homeomorph ζ

/-- The operator bound for a partition piece with values in the unit interval. -/
noncomputable def boundaryExtensionPieceBound {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))}
    (i : Option {c : LipschitzGraphChart n // c.IsChartFor D}) (B : ℝ) : ℝ :=
  match i with
  | none => 1 + B
  | some c => (1 + B) * (2 * (max 1 ((1 + c.val.lip : ℝ≥0) : ℝ) *
      ((1 + c.val.lip : ℝ≥0) : ℝ) ^ n) *
      (max 1 ((1 + c.val.lip : ℝ≥0) : ℝ) * ((1 + c.val.lip : ℝ≥0) : ℝ) ^ n))

lemma boundaryExtensionPieceBound_nonneg {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))}
    (i : Option {c : LipschitzGraphChart n // c.IsChartFor D}) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ boundaryExtensionPieceBound i B := by
  cases i <;> simp only [boundaryExtensionPieceBound] <;> positivity

/-- Each partition piece extends its own cutoff times the input, with a fixed compact
support and a bound controlled by the BV norm on the original domain. -/
theorem bv_boundaryExtensionPiece {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (i : Option {c : LipschitzGraphChart n // c.IsChartFor D})
    {g ζ : EuclideanSpace ℝ (Fin n) → ℝ} (hg : IsBVOn g D)
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ)
    (hsζ : tsupport ζ ⊆ boundaryExtensionRegion D i)
    (hbζ : ∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1)
    {B : ℝ} (hB : 0 ≤ B) (hbgrad : ∀ x, ‖gradient ζ x‖ ≤ B) :
    IsBVOn (boundaryExtensionPiece D i ζ g) univ ∧
      EqOn (boundaryExtensionPiece D i ζ g) (fun x => ζ x * g x) D ∧
      tsupport (boundaryExtensionPiece D i ζ g) ⊆ tsupport ζ ∧
      (∫ x, ‖boundaryExtensionPiece D i ζ g x‖) +
          (variation (boundaryExtensionPiece D i ζ g) univ).toReal ≤
        boundaryExtensionPieceBound i B *
          ((∫ y in D, ‖g y‖) + (variation g D).toReal) := by
  have hnorm : ∀ x, ‖ζ x‖ ≤ (1 : ℝ) := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hbζ x).1]
    exact (hbζ x).2
  cases i with
  | none =>
    have hb := bv_norm_mul_compact_factor_le hD hg hζ hcζ hsζ
      (by norm_num : (0 : ℝ) ≤ 1) hB hnorm hbgrad
    exact ⟨hb.1, fun _ _ => rfl, tsupport_mul_subset_left, hb.2⟩
  | some c =>
    exact bv_local_chart_extension c.val.normal c.val.radius c.val.homeomorph
      c.val.lipschitz c.val.lipschitz_symm hD c.property hg hζ hcζ hsζ
      (by norm_num) hB hnorm hbgrad

/-- Finite partition assembly yields a linear BV extension on representatives.
The support set and the operator bound depend on the domain and charts only. -/
theorem exists_bv_extension_linearMap {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ T : (EuclideanSpace ℝ (Fin n) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n) → ℝ),
    ∃ K : Set (EuclideanSpace ℝ (Fin n)), ∃ C : ℝ,
      IsCompact K ∧ 0 ≤ C ∧ ∀ g, IsBVOn g D →
        IsBVOn (T g) univ ∧ EqOn (T g) g D ∧ tsupport (T g) ⊆ K ∧
        (∫ x, ‖T g x‖) + (variation (T g) univ).toReal ≤
          C * ((∫ x in D, ‖g x‖) + (variation g D).toReal) := by
  classical
  obtain ⟨s, hopen, hbounded, hcover⟩ := exists_finite_boundary_chart_cover hD hbD hL
  have hcover' : closure D ⊆ ⋃ i : ↥s, boundaryExtensionRegion D i.val := by
    simpa only [iUnion_subtype] using hcover
  obtain ⟨ζ, B, hζ, hsum, _⟩ := exists_finite_smooth_partition_of_bounded_open_cover
    hbD.isCompact_closure (fun i : ↥s => boundaryExtensionRegion D i.val)
    (fun i => hopen i.val) (fun i => hbounded i.val) hcover'
  let T := ∑ i : ↥s, boundaryExtensionPiece D i.val (ζ i)
  let K := ⋃ i : ↥s, tsupport (ζ i)
  let C := ∑ i : ↥s, boundaryExtensionPieceBound i.val (B i)
  have hK : IsCompact K := isCompact_iUnion (fun i => (hζ i).2.1)
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ =>
    boundaryExtensionPieceBound_nonneg i.val (hζ i).2.2.2.2.1
  refine ⟨T, K, C, hK, hC, fun g hg => ?_⟩
  have hpiece (i : ↥s) := bv_boundaryExtensionPiece hD i.val hg
    ((hζ i).1.of_le (by simp)) (hζ i).2.1 (hζ i).2.2.1
    (hζ i).2.2.2.1 (hζ i).2.2.2.2.1 (hζ i).2.2.2.2.2
  have hTeq : T g = fun x => ∑ i : ↥s, boundaryExtensionPiece D i.val (ζ i) g x := by
    ext x
    simp only [T, LinearMap.sum_apply, Finset.sum_apply]
  rw [hTeq]
  refine ⟨IsBVOn.finsetSum Finset.univ (fun i _ => (hpiece i).1), ?_, ?_, ?_⟩
  · intro x hx
    calc
      _ = ∑ i : ↥s, ζ i x * g x := Finset.sum_congr rfl fun i _ => (hpiece i).2.1 hx
      _ = (∑ i : ↥s, ζ i x) * g x := (Finset.sum_mul _ _ _).symm
      _ = g x := by rw [hsum x (subset_closure hx), one_mul]
  · apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hnot
    have hz (i : ↥s) : boundaryExtensionPiece D i.val (ζ i) g x = 0 := by
      by_contra hxne
      exact hnot (mem_iUnion.mpr ⟨i, (hpiece i).2.2.1 (subset_tsupport _ hxne)⟩)
    exact hx (by simp only [hz, Finset.sum_const_zero])
  · have hb := bv_norm_finsetSum_le Finset.univ (fun i _ => (hpiece i).1)
    simp only [setIntegral_univ] at hb
    apply hb.trans
    calc
      _ ≤ ∑ i : ↥s, boundaryExtensionPieceBound i.val (B i) *
          ((∫ x in D, ‖g x‖) + (variation g D).toReal) :=
        Finset.sum_le_sum fun i _ => (hpiece i).2.2.2
      _ = _ := (Finset.sum_mul _ _ _).symm


/-- Extending a height from its tangential cube changes neither the shear on the
cube nor either graph-chart region. Only the tangential restriction needs to be Lipschitz. -/
theorem exists_lipschitz_graph_height_extension {n : ℕ} (i : Fin n) (R : ℝ)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hh : LipschitzOnWith L h (coordinateErase i '' coordinateCube n R)) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ, LipschitzWith L g ∧
      EqOn h g (coordinateErase i '' coordinateCube n R) ∧
      EqOn (graphShear i h) (graphShear i g) (coordinateCube n R) ∧
      graphChartCube i h R = graphChartCube i g R ∧
      graphChartHalfCube i h R = graphChartHalfCube i g R := by
  obtain ⟨g, hg, heq⟩ := exists_lipschitz_extension_real hh
  have hshear : EqOn (graphShear i h) (graphShear i g) (coordinateCube n R) := by
    intro x hx
    simp only [graphShear, heq (mem_image_of_mem (coordinateErase i) hx)]
  exact ⟨g, hg, heq, hshear, image_congr hshear,
    image_congr fun x hx => hshear hx.1⟩

/-- The closure of a smaller coordinate cube is contained in a larger open cube. -/
lemma closure_coordinateCube_subset_of_lt {n : ℕ} {r R : ℝ} (hrR : r < R) :
    closure (coordinateCube n r) ⊆ coordinateCube n R := by
  intro x hx j
  have hclosed : IsClosed {y : EuclideanSpace ℝ (Fin n) | |y j| ≤ r} :=
    isClosed_le (EuclideanSpace.proj j).continuous.abs continuous_const
  have hsub : coordinateCube n r ⊆ {y : EuclideanSpace ℝ (Fin n) | |y j| ≤ r} :=
    fun y hy => (hy j).le
  exact (closure_minimal hsub hclosed hx).trans_lt hrR

/-- A locally Lipschitz height on a tangential cube admits a global Lipschitz
representative on every strictly smaller cube. The shrinking is essential without
a uniform Lipschitz bound on the original open tangential cube. -/
theorem exists_lipschitz_graph_height_extension_of_locallyLipschitz {n : ℕ}
    (i : Fin n) {r R : ℝ} (hrR : r < R)
    {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hh : LocallyLipschitzOn (coordinateErase i '' coordinateCube n R) h) :
    ∃ L : ℝ≥0, ∃ g : EuclideanSpace ℝ (Fin n) → ℝ, LipschitzWith L g ∧
      EqOn h g (coordinateErase i '' coordinateCube n r) ∧
      EqOn (graphShear i h) (graphShear i g) (coordinateCube n r) ∧
      graphChartCube i h r = graphChartCube i g r ∧
      graphChartHalfCube i h r = graphChartHalfCube i g r := by
  have hc : IsCompact (coordinateErase i '' closure (coordinateCube n r)) :=
    (isBounded_coordinateCube n r).isCompact_closure.image
      (lipschitzWith_coordinateErase i).continuous
  have hsmall := hh.mono (image_mono (closure_coordinateCube_subset_of_lt hrR))
  obtain ⟨L, hL⟩ := hsmall.exists_lipschitzOnWith_of_compact hc
  obtain ⟨g, hg⟩ := exists_lipschitz_graph_height_extension i r
    (hL.mono (image_mono subset_closure))
  exact ⟨L, g, hg⟩

/-- Any linear map with the BV norm bound respects almost-everywhere equivalence
of BV inputs. This permits descent from representatives to the actual BV spaces. -/
lemma bv_bounded_linearMap_congr_ae {n m : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} {V : Set (EuclideanSpace ℝ (Fin m))}
    (T : (EuclideanSpace ℝ (Fin n) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin m) → ℝ))
    {C : ℝ} (hT : ∀ f, IsBVOn f D → IsBVOn (T f) V ∧
      (∫ x in V, ‖T f x‖) + (variation (T f) V).toReal ≤
        C * ((∫ x in D, ‖f x‖) + (variation f D).toReal))
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsBVOn f D) (hg : IsBVOn g D)
    (hfg : f =ᵐ[volume.restrict D] g) : T f =ᵐ[volume.restrict V] T g := by
  have hzero : (f - g) =ᵐ[volume.restrict D] (0 : EuclideanSpace ℝ (Fin n) → ℝ) := by
    filter_upwards [hfg] with x hx
    simp only [Pi.sub_apply, Pi.zero_apply, hx, sub_self]
  have hvzero : variation (f - g) D = 0 :=
    (variation_congr_ae D hzero).trans (variation_zero D)
  have hLzero : (∫ x in D, ‖(f - g) x‖) = 0 := by
    calc
      _ = ∫ x in D, ‖(0 : EuclideanSpace ℝ (Fin n) → ℝ) x‖ :=
        integral_congr_ae (hzero.fun_comp norm)
      _ = 0 := by simp
  have hb := hT (f - g) (hf.sub hg)
  rw [hvzero, hLzero, ENNReal.toReal_zero, add_zero, mul_zero] at hb
  have heq : (∫ x in V, ‖T (f - g) x‖) = 0 :=
    le_antisymm (hb.2.trans' (le_add_of_nonneg_right ENNReal.toReal_nonneg))
      (integral_nonneg fun _ => norm_nonneg _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => norm_nonneg (T (f - g) x))
    hb.1.1.norm).mp heq
  filter_upwards [hae] with x hx
  have hxzero : (T (f - g)) x = 0 := norm_eq_zero.mp hx
  simpa only [map_sub, Pi.sub_apply, sub_eq_zero] using hxzero

/-- The compact-support conclusion can be expressed in one fixed bounded open
neighborhood of the domain's closure, as in the blueprint extension lemma. -/
theorem exists_bv_extension_in_bounded_neighborhood {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ T : (EuclideanSpace ℝ (Fin n) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n) → ℝ),
    ∃ W : Set (EuclideanSpace ℝ (Fin n)), ∃ C : ℝ,
      IsOpen W ∧ Bornology.IsBounded W ∧ closure D ⊆ W ∧ 0 ≤ C ∧
      (∀ g, IsBVOn g D → IsBVOn (T g) univ ∧ EqOn (T g) g D ∧
        tsupport (T g) ⊆ W ∧
        (∫ x, ‖T g x‖) + (variation (T g) univ).toReal ≤
          C * ((∫ x in D, ‖g x‖) + (variation g D).toReal)) ∧
      (∀ f g, IsBVOn f D → IsBVOn g D → f =ᵐ[volume.restrict D] g →
        T f =ᵐ[volume] T g) := by
  obtain ⟨T, K, C, hK, hC, hT⟩ := exists_bv_extension_linearMap hD hbD hL
  obtain ⟨R, _, hR⟩ := (hbD.closure.union hK.isBounded).exists_pos_norm_lt
  have hDK : closure D ∪ K ⊆ ball 0 R := by
    intro x hx
    simpa only [mem_ball, dist_zero_right] using hR x hx
  refine ⟨T, ball 0 R, C, isOpen_ball, isBounded_ball, fun x hx => hDK (Or.inl hx),
    hC, ?_, ?_⟩
  · intro g hg
    have hb := hT g hg
    exact ⟨hb.1, hb.2.1, fun x hx => hDK (Or.inr (hb.2.2.1 hx)), hb.2.2.2⟩
  · intro f g hf hg hfg
    have hnorm : ∀ u, IsBVOn u D → IsBVOn (T u) univ ∧
        (∫ x in univ, ‖T u x‖) + (variation (T u) univ).toReal ≤
          C * ((∫ x in D, ‖u x‖) + (variation u D).toReal) := by
      intro u hu
      simpa only [setIntegral_univ] using ⟨(hT u hu).1, (hT u hu).2.2.2⟩
    simpa only [Measure.restrict_univ] using bv_bounded_linearMap_congr_ae T hnorm hf hg hfg

/-- Blueprint `lem:bv-extension`: a bounded open set with Lipschitz boundary admits
a bounded linear extension on the normed spaces of BV classes. All output classes
have compactly supported representatives inside one fixed bounded open neighborhood.
The construction works in every finite dimension and does not require connectedness. -/
theorem exists_bv_extension {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ E : BVSpace D →L[ℝ] BVSpace (univ : Set (EuclideanSpace ℝ (Fin n))),
    ∃ W : Set (EuclideanSpace ℝ (Fin n)), ∃ C : ℝ,
      IsOpen W ∧ Bornology.IsBounded W ∧ closure D ⊆ W ∧ 0 ≤ C ∧ ‖E‖ ≤ C ∧
      ∀ g : BVSpace D,
        (⇑(E g) =ᵐ[volume.restrict D] g) ∧ ‖E g‖ ≤ C * ‖g‖ ∧
        ∃ f : EuclideanSpace ℝ (Fin n) → ℝ,
          IsBVOn f univ ∧ HasCompactSupport f ∧ tsupport f ⊆ W ∧
          (⇑(E g) =ᵐ[volume] f) ∧ EqOn f g D := by
  obtain ⟨T, W, C, hoW, hbW, hDW, hC, hT, hAE⟩ :=
    exists_bv_extension_in_bounded_neighborhood hD hbD hL
  have hBV : ∀ f, IsBVOn f D → IsBVOn (T f) univ := fun f hf => (hT f hf).1
  have hAE' : ∀ f g, IsBVOn f D → IsBVOn g D → f =ᵐ[volume.restrict D] g →
      T f =ᵐ[volume.restrict univ] T g := by
    simpa only [Measure.restrict_univ] using hAE
  have hbound : ∀ f, IsBVOn f D →
      (∫ x in univ, ‖T f x‖) + (variation (T f) univ).toReal ≤
        C * ((∫ x in D, ‖f x‖) + (variation f D).toReal) := by
    intro f hf
    simpa only [setIntegral_univ] using (hT f hf).2.2.2
  let E := BVSpace.liftContinuousLinearMap T hBV hAE' C hbound
  refine ⟨E, W, C, hoW, hbW, hDW, hC,
    BVSpace.norm_liftContinuousLinearMap_le T hBV hAE' C hbound hC, fun g => ?_⟩
  have hg := hT g g.isBVOn
  have hae : ⇑(E g) =ᵐ[volume] T g := by
    simpa only [Measure.restrict_univ] using
      BVSpace.coeFn_liftContinuousLinearMap T hBV hAE' C hbound g
  have hnorm : ‖E g‖ ≤ C * ‖g‖ :=
    BVSpace.norm_liftLinearMap_le T hBV hAE' C hbound g
  have haeD : ⇑(E g) =ᵐ[volume.restrict D] T g := ae_restrict_of_ae hae
  have hTD : T g =ᵐ[volume.restrict D] g :=
    ae_restrict_of_forall_mem hD.measurableSet hg.2.1
  refine ⟨haeD.trans hTD, hnorm, T g, hg.1, ?_,
      hg.2.2.1, hae, hg.2.1⟩
  exact isCompact_of_isClosed_isBounded (isClosed_tsupport _) (hbW.subset hg.2.2.1)

end LiquidDrop
