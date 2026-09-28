import NoCompromise.Area.AlmostLinear
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Normed.Lp.Matrix
import NoCompromise.Area.UniformDerivative
import NoCompromise.Measure.FinitePartition

/-!
# Null image of the rank-deficient set

For a planar linear map with zero Gram Jacobian, expansion along its kernel gives
an injective planar comparison map with Jacobian `ε * (s₀ + ε)`. Comparing an
almost-linear map with this anisotropic model through Lipschitz distortion gives
an area bound `4 * ε * (s₀ + ε) * |B|` without any nonlinear area formula.

Uniform differentiability and a finite measurable partition make this estimate
uniform on compact pieces. Compact extraction, arbitrarily small discarded source
measure, and countable exhaustion prove the full zero-Jacobian image theorem.
Rademacher's theorem handles the nondifferentiability set.
-/

noncomputable section
open MeasureTheory Set Module Filter Metric
open scoped ENNReal NNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- A globally Lipschitz planar map sends Lebesgue-null sets to area-null sets. -/
lemma hausdorffMeasure2_image_null {m : ℕ} {K : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    (hf : LipschitzWith K f) {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : volume A = 0) : hausdorffMeasure2 m (f '' A) = 0 := by
  have h := hausdorffMeasure2_image_le_of_lipschitzOn (hf.lipschitzOnWith (s := A))
  rw [hausdorffMeasure2_plane, hA, mul_zero] at h
  exact le_zero_iff.mp h

/-- The image of the nondifferentiability set is area-null by Rademacher. -/
lemma hausdorffMeasure2_image_nondifferentiable {m : ℕ} {K : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    (hf : LipschitzWith K f) :
    hausdorffMeasure2 m (f '' {x | ¬DifferentiableAt ℝ f x}) = 0 :=
  hausdorffMeasure2_image_null hf (ae_iff.mp (hf.ae_differentiableAt (μ := volume)))

lemma jacobian2Linear_eq_zero_iff_not_injective {m : ℕ}
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    jacobian2Linear L = 0 ↔ ¬Function.Injective L := by
  rw [← jacobian2Linear_pos_iff_injective, not_lt]
  exact ⟨fun h => h.le, fun h => le_antisymm h (jacobian2Linear_nonneg L)⟩

lemma singularValues_one_eq_zero_of_jacobian_eq_zero {m : ℕ}
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hL : jacobian2Linear L = 0) : L.singularValues 1 = 0 := by
  have h := (jacobian2Linear_eq_zero_iff_not_injective L).mp hL
  by_contra hnot
  have hpos : 0 < L.singularValues 1 :=
    lt_of_le_of_ne (L.singularValues_nonneg 1) (Ne.symm hnot)
  apply h
  apply L.injective_iff_forall_lt_finrank_singularValues_pos.mpr
  intro i hi
  have hi1 : i ≤ 1 := by simp only [finrank_euclideanSpace_fin] at hi; omega
  exact hpos.trans_le (L.singularValues_antitone hi1)

/-- A planar linear comparison controls the area of a map into any Euclidean codomain. -/
lemma hausdorffMeasure2_image_le_of_linear_domination {m : ℕ}
    (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (hA : Function.Injective A) {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    {B : Set (EuclideanSpace ℝ (Fin 2))} {K : ℝ≥0}
    (hf : ∀ x ∈ B, ∀ y ∈ B, ‖f x - f y‖ ≤ (K : ℝ) * ‖A (x - y)‖) :
    hausdorffMeasure2 m (f '' B) ≤
      (K : ℝ≥0∞) ^ 2 * ENNReal.ofReal (jacobian2Linear A) * volume B := by
  have hi := hA.injOn (s := B)
  have hq : LipschitzOnWith K (f ∘ Function.invFunOn A B) (A '' B) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simpa only [Function.comp_apply, hi.leftInvOn_invFunOn hx,
      hi.leftInvOn_invFunOn hy, dist_eq_norm, ← A.map_sub] using hf x hx y hy
  have heq : (f ∘ Function.invFunOn A B) '' (A '' B) = f '' B := by
    simp only [Function.comp_def]
    rw [← Set.image_image f (Function.invFunOn A B), hi.invFunOn_image Subset.rfl]
  have h := hausdorffMeasure2_image_le_of_lipschitzOn hq
  rw [heq, hausdorffMeasure2_image_linear A hA, ← mul_assoc] at h
  exact h

/-- A diagonal stretch on the Euclidean plane. -/
def planarDiagonal (a b : ℝ) : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ((Matrix.diagonal (fun i : Fin 2 => if i = 0 then a else b)).toLpLin 2 2).toContinuousLinearMap

lemma planarDiagonal_apply (a b : ℝ) (x : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    planarDiagonal a b x i = (if i = 0 then a else b) * x i := by
  simp [planarDiagonal, Matrix.toLpLin_apply, Matrix.mulVec_diagonal]

lemma planarDiagonal_norm_sq (a b : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    ‖planarDiagonal a b x‖ ^ 2 = a ^ 2 * (x 0) ^ 2 + b ^ 2 * (x 1) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  simp only [planarDiagonal_apply, ↓reduceIte, Fin.isValue, one_ne_zero, mul_pow]

lemma planarDiagonal_det (a b : ℝ) : (planarDiagonal a b).det = a * b := by
  change (((Matrix.diagonal (fun i : Fin 2 => if i = 0 then a else b)).toLpLin 2 2)).det = _
  rw [LinearMap.det_toLpLin, Matrix.det_diagonal, Fin.prod_univ_two]
  simp

lemma exists_planar_singular_basis {m : ℕ}
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    ∃ b : OrthonormalBasis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)),
      ∀ x, ‖L x‖ ^ 2 = L.singularValues 0 ^ 2 * (b.repr x 0) ^ 2 +
        L.singularValues 1 ^ 2 * (b.repr x 1) ^ 2 := by
  let T := L.toLinearMap.adjoint.comp L.toLinearMap
  let hT := L.toLinearMap.isSymmetric_adjoint_comp_self
  let b := hT.eigenvectorBasis (by simp : finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2)
  refine ⟨b, fun x => ?_⟩
  have hdiag (i : Fin 2) : b.repr (T x) i = L.singularValues i ^ 2 * b.repr x i := by
    rw [L.toLinearMap.sq_singularValues_fin (by simp)]
    exact hT.eigenvectorBasis_apply_self_apply (by simp) x i
  calc
    ‖L x‖ ^ 2 = inner ℝ (T x) x := by
      simp only [T, LinearMap.comp_apply, LinearMap.adjoint_inner_left,
        ContinuousLinearMap.coe_coe, real_inner_self_eq_norm_sq]
    _ = inner ℝ (b.repr (T x)) (b.repr x) := (b.repr.inner_map_map _ _).symm
    _ = _ := by
      rw [PiLp.inner_apply, Fin.sum_univ_two, hdiag, hdiag]
      simp only [RCLike.inner_apply, conj_trivial, Fin.val_zero, Fin.val_one]
      ring

/-- A small expansion along the kernel turns a rank-deficient model into an injective
planar comparison map with small Jacobian. -/
lemma exists_rankDeficient_comparison {m : ℕ}
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hL : jacobian2Linear L = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2),
      Function.Injective A ∧ jacobian2Linear A = ε * (L.singularValues 0 + ε) ∧
      ∀ v, ‖L v‖ ≤ ‖A v‖ ∧ ε * ‖v‖ ≤ ‖A v‖ := by
  obtain ⟨b, hb⟩ := exists_planar_singular_basis L
  have hz := singularValues_one_eq_zero_of_jacobian_eq_zero L hL
  let D := planarDiagonal (L.singularValues 0 + ε) ε
  let A := D.comp b.repr.toContinuousLinearEquiv.toContinuousLinearMap
  have hnorm (v) : ‖v‖ ^ 2 = (b.repr v 0) ^ 2 + (b.repr v 1) ^ 2 := by
    rw [← b.repr.norm_map v, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have hA (v) : ‖A v‖ ^ 2 =
      (L.singularValues 0 + ε) ^ 2 * (b.repr v 0) ^ 2 + ε ^ 2 * (b.repr v 1) ^ 2 :=
    planarDiagonal_norm_sq _ _ _
  have hs := L.singularValues_nonneg 0
  have hsbound : L.singularValues 0 ^ 2 ≤ (L.singularValues 0 + ε) ^ 2 := by nlinarith
  have hebound : ε ^ 2 ≤ (L.singularValues 0 + ε) ^ 2 := by nlinarith
  have hbounds (v) : ‖L v‖ ≤ ‖A v‖ ∧ ε * ‖v‖ ≤ ‖A v‖ := by
    constructor
    · apply le_of_sq_le_sq _ (norm_nonneg _)
      rw [hb, hz, zero_pow (by omega), zero_mul, add_zero, hA]
      nlinarith [mul_le_mul_of_nonneg_right hsbound (sq_nonneg (b.repr v 0)),
        mul_nonneg (sq_nonneg ε) (sq_nonneg (b.repr v 1))]
    · apply le_of_sq_le_sq _ (norm_nonneg _)
      rw [mul_pow, hnorm, hA]
      nlinarith [mul_le_mul_of_nonneg_right hebound (sq_nonneg (b.repr v 0))]
  refine ⟨A, ?_, ?_, hbounds⟩
  · intro x y hxy
    have h := (hbounds (x - y)).2
    rw [map_sub, hxy, sub_self, norm_zero] at h
    have hz : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  · rw [jacobian2Linear_eq_normDet]
    change LinearMap.normDet (D.toLinearMap.comp b.repr.toLinearEquiv.toLinearMap) = _
    have hb1 : b.repr.toLinearEquiv.toLinearMap.normDet = 1 :=
      b.repr.toLinearIsometry.normDet_eq_one
    rw [LinearMap.normDet_comp_of_finrank_eq _ _ rfl, hb1, mul_one,
      LinearMap.normDet_eq_abs_det]
    change |D.det| = _
    rw [planarDiagonal_det, abs_of_pos (mul_pos (by linarith) hε)]
    ring

/-- Rank-deficient almost-linear maps have arbitrarily small area distortion as the
pairwise remainder tends to zero. -/
theorem rankDeficient_almostLinear_area_le {m : ℕ}
    (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hL : jacobian2Linear L = 0) {ε : ℝ} (hε : 0 < ε)
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    {B : Set (EuclideanSpace ℝ (Fin 2))}
    (hf : ∀ x ∈ B, ∀ y ∈ B, ‖f x - f y - L (x - y)‖ ≤ ε * ‖x - y‖) :
    hausdorffMeasure2 m (f '' B) ≤
      ENNReal.ofReal (4 * ε * (L.singularValues 0 + ε)) * volume B := by
  obtain ⟨A, hA, hj, hb⟩ := exists_rankDeficient_comparison L hL hε
  have hdom : ∀ x ∈ B, ∀ y ∈ B, ‖f x - f y‖ ≤ (2 : ℝ≥0) * ‖A (x - y)‖ := by
    intro x hx y hy
    have h := norm_add_le (f x - f y - L (x - y)) (L (x - y))
    rw [sub_add_cancel] at h
    have hb' := hb (x - y)
    norm_num only [NNReal.coe_ofNat]
    linarith [hf x hx y hy]
  have h := hausdorffMeasure2_image_le_of_linear_domination A hA hdom
  rw [hj] at h
  convert h using 1
  rw [mul_assoc (4 : ℝ) ε (L.singularValues 0 + ε),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

/-- Uniform remainder control gives uniform small-patch area distortion on the
rank-deficient set, with a constant depending only on the global Lipschitz bound. -/
lemma exists_rankDeficient_patch_area_bound {m : ℕ} {C : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)} (hf : LipschitzWith C f)
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hrem : UniformRemainderOn f K)
    (hJ : ∀ x ∈ K, jacobian2 f x = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ c ∈ K, ∀ B ⊆ K,
      (∀ x ∈ B, ‖x - c‖ ≤ r) → (∀ x ∈ B, ∀ y ∈ B, ‖x - y‖ ≤ r) →
      hausdorffMeasure2 m (f '' B) ≤ ENNReal.ofReal (4 * ε * ((C : ℝ) + ε)) * volume B := by
  obtain ⟨s, hs, hsrem⟩ := hrem (ε / 2) (by positivity)
  obtain ⟨δ, hδ, hder⟩ := Metric.uniformContinuousOn_iff.mp
    (hrem.uniformContinuousOn_fderiv hf) (ε / 2) (by positivity)
  let r := min s δ / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrs : r < s := by dsimp [r]; have := min_le_left s δ; linarith
  have hrδ : r < δ := by dsimp [r]; have := min_le_right s δ; linarith
  refine ⟨r, hr, fun c hc B hBK hbase hdiam => ?_⟩
  have he : ∀ x ∈ B, ∀ y ∈ B,
      ‖f x - f y - fderiv ℝ f c (x - y)‖ ≤ ε * ‖x - y‖ := by
    intro x hx y hy
    have h₁ := hsrem y (hBK hy) x ((hdiam x hx y hy).trans_lt hrs)
    have h₂ : ‖fderiv ℝ f y - fderiv ℝ f c‖ < ε / 2 := by
      have hyc : dist y c < δ := by
        simpa only [dist_eq_norm] using ((hbase y hy).trans_lt hrδ)
      simpa only [dist_eq_norm] using hder y (hBK hy) c hc hyc
    have h₃ := (fderiv ℝ f y - fderiv ℝ f c).le_opNorm (x - y)
    have h₄ : ‖(fderiv ℝ f y - fderiv ℝ f c) (x - y)‖ ≤ ε / 2 * ‖x - y‖ :=
      h₃.trans (mul_le_mul_of_nonneg_right h₂.le (norm_nonneg _))
    have heq : f x - f y - fderiv ℝ f c (x - y) =
        (f x - f y - fderiv ℝ f y (x - y)) +
          (fderiv ℝ f y - fderiv ℝ f c) (x - y) := by
      simp only [sub_apply]
      abel
    rw [heq]
    exact (norm_add_le _ _).trans (by linarith)
  have h := rankDeficient_almostLinear_area_le (fderiv ℝ f c) (hJ c hc) hε he
  apply h.trans
  apply mul_le_mul' ?_ le_rfl
  apply ENNReal.ofReal_le_ofReal
  have hb := (singularValues_zero_le_norm (fderiv ℝ f c)).trans
    (norm_fderiv_le_of_lipschitz ℝ hf)
  nlinarith

/-- A compact uniformly differentiable rank-deficient carrier has null image. -/
theorem hausdorffMeasure2_image_rankDeficient_compact {m : ℕ} {C : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)} (hf : LipschitzWith C f)
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K)
    (hrem : UniformRemainderOn f K) (hJ : ∀ x ∈ K, jacobian2 f x = 0) :
    hausdorffMeasure2 m (f '' K) = 0 := by
  have hb (ε : ℝ) (hε : 0 < ε) : hausdorffMeasure2 m (f '' K) ≤
      ENNReal.ofReal (4 * ε * ((C : ℝ) + ε)) * volume K := by
    obtain ⟨r, hr, hpatch⟩ := exists_rankDeficient_patch_area_bound hf hrem hJ hε
    obtain ⟨k, B, c, hm, hd, hu, hsub, hbase, hdiam⟩ :=
      exists_finite_measurable_partition_of_compact_subset hK hK.measurableSet Subset.rfl hr
    calc
      _ = hausdorffMeasure2 m (⋃ i, f '' B i) := by rw [← image_iUnion, hu]
      _ ≤ ∑' i, hausdorffMeasure2 m (f '' B i) := measure_iUnion_le _
      _ ≤ ∑' i, ENNReal.ofReal (4 * ε * ((C : ℝ) + ε)) * volume (B i) :=
        ENNReal.tsum_le_tsum fun i => hpatch (c i) (c i).property (B i)
          (hsub i) (hbase i) (hdiam i)
      _ = _ := by rw [ENNReal.tsum_mul_left, ← measure_iUnion hd hm, hu]
  have ht : Tendsto (fun ε : ℝ => ENNReal.ofReal (4 * ε * ((C : ℝ) + ε)) * volume K)
      (𝓝[>] 0) (𝓝 0) := by
    have hreal : Tendsto (fun ε : ℝ => 4 * ε * ((C : ℝ) + ε)) (𝓝[>] 0) (𝓝 0) := by
      have h : Continuous (fun ε : ℝ => 4 * ε * ((C : ℝ) + ε)) := by fun_prop
      simpa using (h.tendsto 0).mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    simpa only [ENNReal.ofReal_zero, zero_mul] using
      ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hreal)
        (Or.inr (hK.measure_lt_top (μ := volume)).ne)
  exact le_zero_iff.mp (ge_of_tendsto ht (by
    filter_upwards [self_mem_nhdsWithin] with ε hε using hb ε hε))

/-- Finite-measure differentiability sets with zero Jacobian have null image. -/
theorem hausdorffMeasure2_image_rankDeficient_of_measure_ne_top {m : ℕ} {C : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)} (hf : LipschitzWith C f)
    {S : Set (EuclideanSpace ℝ (Fin 2))} (hS : MeasurableSet S) (hSf : volume S ≠ ∞)
    (hdiff : ∀ x ∈ S, DifferentiableAt ℝ f x) (hJ : ∀ x ∈ S, jacobian2 f x = 0) :
    hausdorffMeasure2 m (f '' S) = 0 := by
  have hb (ε : ℝ) (hε : 0 < ε) :
      hausdorffMeasure2 m (f '' S) ≤ (C : ℝ≥0∞) ^ 2 * ENNReal.ofReal ε := by
    obtain ⟨K, hKS, hK, hsmall, hrem⟩ := exists_compact_uniformRemainderOn
      hf.continuous hS hSf hdiff (ENNReal.ofReal_pos.mpr hε)
    have hzero := hausdorffMeasure2_image_rankDeficient_compact hf hK hrem
      (fun x hx => hJ x (hKS hx))
    have hcover : f '' S ⊆ f '' K ∪ f '' (S \ K) := by
      rw [← image_union, union_sdiff_cancel hKS]
    calc
      _ ≤ hausdorffMeasure2 m (f '' K) + hausdorffMeasure2 m (f '' (S \ K)) :=
        (measure_mono hcover).trans (measure_union_le _ _)
      _ = hausdorffMeasure2 m (f '' (S \ K)) := by rw [hzero, zero_add]
      _ ≤ (C : ℝ≥0∞) ^ 2 * hausdorffMeasure2 2 (S \ K) :=
        hausdorffMeasure2_image_le_of_lipschitzOn hf.lipschitzOnWith
      _ ≤ _ := by rw [hausdorffMeasure2_plane]; exact mul_le_mul' le_rfl hsmall.le
  have ht : Tendsto (fun ε : ℝ => (C : ℝ≥0∞) ^ 2 * ENNReal.ofReal ε)
      (𝓝[>] 0) (𝓝 0) := by
    have hreal : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id'.2 nhdsWithin_le_nhds
    simpa only [ENNReal.ofReal_zero, mul_zero] using
      ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal hreal)
        (Or.inr (by finiteness : (C : ℝ≥0∞) ^ 2 ≠ ∞))
  exact le_zero_iff.mp (ge_of_tendsto ht (by
    filter_upwards [self_mem_nhdsWithin] with ε hε using hb ε hε))

/-- Blueprint `lem:rank-deficient`: the whole zero-Jacobian set, including points
where the total derivative is zero because differentiability fails, has null image. -/
theorem hausdorffMeasure2_image_jacobian2_eq_zero {m : ℕ} {C : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)} (hf : LipschitzWith C f) :
    hausdorffMeasure2 m (f '' {x | jacobian2 f x = 0}) = 0 := by
  let S (n : ℕ) : Set (EuclideanSpace ℝ (Fin 2)) :=
    {x | DifferentiableAt ℝ f x ∧ jacobian2 f x = 0} ∩ closedBall 0 n
  have hS (n) : MeasurableSet (S n) :=
    ((measurableSet_of_differentiableAt ℝ f).inter
      (measurableSet_eq_fun (measurable_jacobian2 f) measurable_const)).inter
        measurableSet_closedBall
  have hn (n) : hausdorffMeasure2 m (f '' S n) = 0 :=
    hausdorffMeasure2_image_rankDeficient_of_measure_ne_top hf (hS n)
      (ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono inter_subset_right))
      (fun _ hx => hx.1.1) (fun _ hx => hx.1.2)
  have hcover : {x | jacobian2 f x = 0} ⊆
      {x | ¬DifferentiableAt ℝ f x} ∪ ⋃ n, S n := by
    intro x hx
    by_cases hdiff : DifferentiableAt ℝ f x
    · right
      obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
      exact mem_iUnion.mpr ⟨n, ⟨hdiff, hx⟩, by
        simpa only [mem_closedBall, dist_zero_right] using hn.le⟩
    · exact Or.inl hdiff
  apply measure_mono_null (image_mono hcover)
  rw [image_union, image_iUnion]
  exact measure_union_null (hausdorffMeasure2_image_nondifferentiable hf) (measure_iUnion_null hn)

end LiquidDrop
