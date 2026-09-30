module

public import NoCompromise.Sobolev.H1Algebra
public import NoCompromise.Sobolev.H1Calculus
public import NoCompromise.Sobolev.H1TestApprox

@[expose] public section

/-!
# Caccioppoli's inequality for local weak solutions

Positive uniform ellipticity is explicit. Coefficients are measurable bounded
linear operators, and the weak equation is initially tested only against C¹
functions with compact support inside the open domain.
-/

noncomputable section

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- Local L² membership is required only on compact subsets of the domain. -/
def IsLocallyL2On {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    (f : EuclideanSpace ℝ (Fin n) → F) (U : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ K, IsCompact K → K ⊆ U → MemLp f 2 (volume.restrict K)

/-- A specified local H¹ weak gradient. No global L² assumption is imposed. -/
structure HasLocallyH1GradientOn {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n))) : Prop extends HasWeakGradientOn f G U where
  locallyL2_function : IsLocallyL2On f U
  locallyL2_gradient : IsLocallyL2On G U

/-- Local L² membership restricts to smaller domains. -/
lemma IsLocallyL2On.mono {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {U V : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → E}
    (hf : IsLocallyL2On f U) (hVU : V ⊆ U) : IsLocallyL2On f V := by
  intro K hK hKV
  exact hf K hK (hKV.trans hVU)

/-- A global H¹ representative on a domain satisfies the local interface. -/
lemma HasH1GradientOn.locallyH1 {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G U) : HasLocallyH1GradientOn f G U :=
  ⟨hf.toHasWeakGradientOn,
    fun _ _ hKU => hf.memLp_function.mono_measure (Measure.restrict_mono hKU le_rfl),
    fun _ _ hKU => hf.memLp_gradient.mono_measure (Measure.restrict_mono hKU le_rfl)⟩

/-- The local H¹ relation restricts to every smaller domain. -/
lemma HasLocallyH1GradientOn.mono {n : ℕ} {U V : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasLocallyH1GradientOn f G U) (hVU : V ⊆ U) : HasLocallyH1GradientOn f G V :=
  ⟨hf.toHasWeakGradientOn.mono hVU,
    hf.locallyL2_function.mono hVU, hf.locallyL2_gradient.mono hVU⟩

/-- The local interface gives ordinary H¹ on every compact subset. -/
lemma HasLocallyH1GradientOn.on_compact {n : ℕ}
    {U K : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasLocallyH1GradientOn f G U) (hK : IsCompact K) (hKU : K ⊆ U) :
    HasH1GradientOn f G K :=
  ⟨hf.toHasWeakGradientOn.mono hKU,
    hf.locallyL2_function K hK hKU, hf.locallyL2_gradient K hK hKU⟩

/-- A compact C¹ cutoff turns local H¹ into global H¹, with its exact weak gradient. -/
lemma HasLocallyH1GradientOn.mul_compact_cutoff {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {f ζ : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasLocallyH1GradientOn f G U) (hζ : ContDiff ℝ 1 ζ)
    (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ U) :
    HasH1GradientOn (fun x => ζ x * f x)
      (fun x => ζ x • G x + f x • gradient ζ x) univ := by
  obtain ⟨A, hA⟩ := hcζ.exists_bound_of_continuous hζ.continuous
  have hcgrad : HasCompactSupport (gradient ζ) :=
    hcζ.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset ζ)
  obtain ⟨B, hB⟩ := hcgrad.exists_bound_of_continuous (continuous_gradient_of_contDiff hζ)
  exact ((hf.on_compact hcζ hsζ).mul_compact_cutoff (isClosed_tsupport ζ).measurableSet
    hζ hcζ Subset.rfl hA hB).1

/-- Pointwise inner products of two L² functions are integrable. -/
lemma integrable_inner_of_memLp_two {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure α} {f g : α → E}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) : Integrable (fun x => inner ℝ (f x) (g x)) μ := by
  apply (hf.norm.integrable_mul hg.norm).mono' (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
  exact Eventually.of_forall fun x => norm_inner_le_norm _ _

/-- The L² Hilbert inner product agrees with the pairing of any L² representatives. -/
lemma inner_toLp_eq_integral_inner {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure α} {f g : α → E}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, inner ℝ (f x) (g x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hg] with x hx hy
  rw [hx, hy]

/-- L² convergence of the second factor gives convergence of its pairing with a fixed L² field. -/
lemma tendsto_integral_inner_of_eLpNorm_sub {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure α}
    {F : α → E} {g : ℕ → α → E} {G : α → E}
    (hF : MemLp F 2 μ) (hg : ∀ j, MemLp (g j) 2 μ) (hG : MemLp G 2 μ)
    (ht : Tendsto (fun j => eLpNorm (g j - G) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, inner ℝ (F x) (g j x) ∂μ) atTop
      (𝓝 (∫ x, inner ℝ (F x) (G x) ∂μ)) := by
  have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g hg G hG).mpr ht
  have hp := ((innerSL ℝ (hF.toLp F)).continuous.tendsto (hG.toLp G)).comp h
  simpa only [Function.comp_def, innerSL_apply_apply, inner_toLp_eq_integral_inner] using hp

/-- A locally L² vector field annihilating C¹ compact gradients also annihilates
compact H¹ tests with a compactly supported specified gradient. -/
theorem integral_inner_eq_zero_of_compact_h1_test {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hF : IsLocallyL2On F U)
    (hEq : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ x, inner ℝ (F x) (gradient φ x)) = 0)
    {v : EuclideanSpace ℝ (Fin n) → ℝ}
    {W : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hv : HasH1GradientOn v W univ)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKU : K ⊆ U)
    (hsv : tsupport v ⊆ K) (hsW : tsupport W ⊆ K) :
    (∫ x, inner ℝ (F x) (W x)) = 0 := by
  have hcv : HasCompactSupport v := hK.of_isClosed_subset (isClosed_tsupport _) hsv
  obtain ⟨V, hV, _, hcV, hVU, _, g, hg, _, ht⟩ :=
    hv.exists_smooth_compact_test_approximation hU hcv (hsv.trans hKU)
  let L := closure V ∪ K
  have hcL : IsCompact L := hcV.union hK
  have hLU : L ⊆ U := union_subset hVU hKU
  have hFL : MemLp (L.indicator F) 2 volume :=
    (memLp_indicator_iff_restrict hcL.measurableSet).mpr (hF L hcL hLU)
  have hm (j : ℕ) : MemLp (gradient (g j)) 2 volume := by
    simpa only [Measure.restrict_univ] using (hg j).2.2.2.memLp_gradient
  have hmW : MemLp W 2 volume := by
    simpa only [Measure.restrict_univ] using hv.memLp_gradient
  have hp := tendsto_integral_inner_of_eLpNorm_sub hFL hm hmW ht
  have heq (j : ℕ) : (∫ x, inner ℝ (L.indicator F x) (gradient (g j) x)) = 0 := by
    convert hEq (g j) ((hg j).1.of_le (by simp)) (hg j).2.1
      ((hg j).2.2.1.trans (subset_closure.trans hVU)) using 1
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ L
      · simp only [indicator_of_mem hx]
      · have hxg : x ∉ tsupport (g j) := fun hs =>
          hx (Or.inl (subset_closure ((hg j).2.2.1 hs)))
        simp [gradient_eq_zero_of_notMem_tsupport hxg]
  have hlim : (∫ x, inner ℝ (L.indicator F x) (W x)) = 0 :=
    tendsto_nhds_unique hp (by simpa only [heq] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
  rw [← hlim]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ L
    · simp only [indicator_of_mem hx]
    · have hxW : x ∉ tsupport W := fun hs => hx (Or.inr (hsW hs))
      simp [image_eq_zero_of_notMem_tsupport hxW]

/-- Compact continuous scalar multipliers send local L² fields into global L². -/
lemma IsLocallyL2On.smul_compact_scalar {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → E}
    {ζ : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsLocallyL2On f U)
    (hζ : Continuous ζ) (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ U) :
    MemLp (fun x => ζ x • f x) 2 volume := by
  obtain ⟨A, hA⟩ := hcζ.exists_bound_of_continuous hζ
  exact (memLp_smul_supported_scalar (isClosed_tsupport ζ).measurableSet
    (hf (tsupport ζ) hcζ hsζ) hζ Subset.rfl hA).1

/-- Compact continuous vector multipliers send local scalar L² functions into global L². -/
lemma IsLocallyL2On.smul_compact_vector {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : IsLocallyL2On f U) (hX : Continuous X) (hcX : HasCompactSupport X)
    (hsX : tsupport X ⊆ U) : MemLp (fun x => f x • X x) 2 volume := by
  obtain ⟨B, hB⟩ := hcX.exists_bound_of_continuous hX
  exact (memLp_smul_supported_vector (isClosed_tsupport X).measurableSet
    (hf (tsupport X) hcX hsX) hX Subset.rfl hB).1

/-- Bounded measurable coefficient fields act on local L² vector fields. -/
lemma IsLocallyL2On.clm_apply {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hG : IsLocallyL2On G U) (hA : AEStronglyMeasurable A (volume.restrict U))
    {cap : ℝ} (hb : ∀ᵐ x ∂volume.restrict U, ‖A x‖ ≤ cap) :
    IsLocallyL2On (fun x => A x (G x)) U := by
  intro K hK hKU
  have hGK := hG K hK hKU
  have hAK := hA.mono_measure (Measure.restrict_mono hKU le_rfl)
  have hbK := ae_mono (Measure.restrict_mono hKU le_rfl) hb
  apply hGK.of_le_mul (c := cap)
  · exact isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable (hAK.prodMk hGK.aestronglyMeasurable)
  · filter_upwards [hbK] with x hx
    exact (A x).le_opNorm (G x) |>.trans
      (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

/-- Local L² fields are closed under subtraction. -/
lemma IsLocallyL2On.sub {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {U : Set (EuclideanSpace ℝ (Fin n))} {f g : EuclideanSpace ℝ (Fin n) → E}
    (hf : IsLocallyL2On f U) (hg : IsLocallyL2On g U) :
    IsLocallyL2On (fun x => f x - g x) U := by
  intro K hK hKU
  exact (hf K hK hKU).sub (hg K hK hKU)

/-- The weak divergence equation, with the usual C¹ compact scalar test functions.
The test gradient vanishes outside `U`, so these are the distributional identities on `U`. -/
def IsWeakDivergenceEquationOn {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (D G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
    tsupport φ ⊆ U → (∫ x, inner ℝ (A x (D x) - G x) (gradient φ x)) = 0

/-- Compact H¹ density justifies testing the original C¹ weak equation with `η²u`. -/
lemma integral_inner_cutoff_sq_eq_zero {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u η : EuclideanSpace ℝ (Fin n) → ℝ}
    {D F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hu : HasLocallyH1GradientOn u D U) (hF : IsLocallyL2On F U)
    (hEq : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
        (∫ x, inner ℝ (F x) (gradient φ x)) = 0)
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ U) :
    (∫ x, inner ℝ (F x)
      (η x ^ 2 • D x + (2 * η x * u x) • gradient η x)) = 0 := by
  have hs2 : tsupport (fun x => η x ^ 2) ⊆ tsupport η := by
    simpa only [pow_two] using (tsupport_mul_subset_left (f := η) (g := η))
  have hc2 : HasCompactSupport (fun x => η x ^ 2) :=
    hcη.of_isClosed_subset (isClosed_tsupport _) hs2
  have hw := hu.mul_compact_cutoff (hη.pow 2) hc2 (hs2.trans hsη)
  have hsv : tsupport (fun x => η x ^ 2 * u x) ⊆ tsupport η :=
    tsupport_mul_subset_left.trans hs2
  have hsW : tsupport (fun x => η x ^ 2 • D x + u x • gradient (fun y => η y ^ 2) x) ⊆
      tsupport η :=
    (tsupport_add _ _).trans (union_subset
      ((tsupport_smul_subset_left _ _).trans hs2)
      ((tsupport_smul_subset_right _ _).trans ((tsupport_gradient_subset _).trans hs2)))
  have htest := integral_inner_eq_zero_of_compact_h1_test hU hF hEq hw hcη hsη hsv hsW
  have hgrad (x : EuclideanSpace ℝ (Fin n)) :
      gradient (fun y => η y ^ 2) x = (2 * η x) • gradient η x := by
    simpa only [pow_two, two_mul, add_smul] using gradient_mul hη hη x
  convert htest using 1
  congr 1
  ext x
  rw [hgrad, smul_smul, show 2 * η x * u x = u x * (2 * η x) by ring]

/-- The algebraic coercivity and Young estimate underlying Caccioppoli. -/
lemma caccioppoli_vector_energy {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A : E →L[ℝ] E} {lam cap : ℝ} (hlam : 0 < lam)
    (hell : ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A v)) (hA : ‖A‖ ≤ cap)
    (v w z : E) :
    lam ^ 2 * ‖v‖ ^ 2 ≤ (8 * cap ^ 2 + 2 * lam + 2) * (‖w‖ ^ 2 + ‖z‖ ^ 2) +
      2 * lam * inner ℝ (A v - z) (v + (2 : ℝ) • w) := by
  have hv := hell v
  rw [real_inner_comm] at hv
  have hzv := real_inner_le_norm z v
  have hzw := real_inner_le_norm z w
  have havw : -(cap * ‖v‖ * ‖w‖) ≤ inner ℝ (A v) w := by
    have h1 := (abs_real_inner_le_norm (A v) w).trans
      (mul_le_mul_of_nonneg_right
        ((A.le_opNorm v).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg v)))
        (norm_nonneg w))
    exact (abs_le.mp h1).1
  have hlow : lam * ‖v‖ ^ 2 - ‖z‖ * ‖v‖ - 2 * cap * ‖v‖ * ‖w‖ -
      2 * ‖z‖ * ‖w‖ ≤ inner ℝ (A v - z) (v + (2 : ℝ) • w) := by
    simp only [inner_add_right, inner_sub_left, inner_smul_right]
    linarith
  have hmul := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 2 * lam by positivity)
  nlinarith [sq_nonneg (lam * ‖v‖ - 2 * ‖z‖),
    sq_nonneg (lam * ‖v‖ - 4 * cap * ‖w‖),
    mul_nonneg hlam.le (sq_nonneg (‖w‖ - ‖z‖)), sq_nonneg ‖w‖,
    mul_nonneg (sq_nonneg cap) (sq_nonneg ‖z‖)]

/-- Caccioppoli for measurable uniformly elliptic coefficients and local weak H¹ solutions.
The explicit constant depends only on the positive ellipticity and operator-norm bounds. -/
theorem caccioppoli {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u η : EuclideanSpace ℝ (Fin n) → ℝ}
    {D G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {lam cap : ℝ} (hlam : 0 < lam) (_hlamcap : lam ≤ cap)
    (hA : AEStronglyMeasurable A (volume.restrict U))
    (hell : ∀ᵐ x ∂volume.restrict U, ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v))
    (hbA : ∀ᵐ x ∂volume.restrict U, ‖A x‖ ≤ cap)
    (hu : HasLocallyH1GradientOn u D U) (hG : IsLocallyL2On G U)
    (hEq : IsWeakDivergenceEquationOn A D G U)
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ U) :
    (∫ x, η x ^ 2 * ‖D x‖ ^ 2) ≤ ((8 * cap ^ 2 + 2 * lam + 2) / lam ^ 2) *
      ((∫ x, u x ^ 2 * ‖gradient η x‖ ^ 2) + ∫ x, η x ^ 2 * ‖G x‖ ^ 2) := by
  let v (x : EuclideanSpace ℝ (Fin n)) := η x • D x
  let w (x : EuclideanSpace ℝ (Fin n)) := u x • gradient η x
  let z (x : EuclideanSpace ℝ (Fin n)) := η x • G x
  let P (x : EuclideanSpace ℝ (Fin n)) := η x • (A x (D x) - G x)
  let Q (x : EuclideanSpace ℝ (Fin n)) := v x + (2 : ℝ) • w x
  have hF : IsLocallyL2On (fun x => A x (D x) - G x) U :=
    (hu.locallyL2_gradient.clm_apply hA hbA).sub hG
  have hv : MemLp v 2 volume := hu.locallyL2_gradient.smul_compact_scalar hη.continuous hcη hsη
  have hz : MemLp z 2 volume := hG.smul_compact_scalar hη.continuous hcη hsη
  have hcgrad : HasCompactSupport (gradient η) :=
    hcη.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset η)
  have hw : MemLp w 2 volume := hu.locallyL2_function.smul_compact_vector
    (continuous_gradient_of_contDiff hη) hcgrad ((tsupport_gradient_subset η).trans hsη)
  have hP : MemLp P 2 volume := hF.smul_compact_scalar hη.continuous hcη hsη
  have hQ : MemLp Q 2 volume := hv.add (hw.const_smul (2 : ℝ))
  have hiV : Integrable (fun x => ‖v x‖ ^ 2) := hv.integrable_norm_pow (by norm_num)
  have hiW : Integrable (fun x => ‖w x‖ ^ 2) := hw.integrable_norm_pow (by norm_num)
  have hiZ : Integrable (fun x => ‖z x‖ ^ 2) := hz.integrable_norm_pow (by norm_num)
  have hiPQ := integrable_inner_of_memLp_two hP hQ
  have heqP (x : EuclideanSpace ℝ (Fin n)) : A x (v x) - z x = P x := by
    simp only [v, z, P, map_smul, smul_sub]
  have htest : (∫ x, inner ℝ (P x) (Q x)) = 0 := by
    convert integral_inner_cutoff_sq_eq_zero hU hu hF hEq hη hcη hsη using 1
    congr 1
    ext x
    simp only [P, Q, v, w, real_inner_smul_left, inner_add_right, inner_smul_right]
    ring
  have hpoint : ∀ᵐ x ∂volume, lam ^ 2 * ‖v x‖ ^ 2 ≤
      (8 * cap ^ 2 + 2 * lam + 2) * (‖w x‖ ^ 2 + ‖z x‖ ^ 2) +
        2 * lam * inner ℝ (P x) (Q x) := by
    filter_upwards [(ae_restrict_iff' hU.measurableSet).mp hell,
      (ae_restrict_iff' hU.measurableSet).mp hbA] with x hxell hxb
    by_cases hx : x ∈ U
    · simpa only [heqP, Q] using
        caccioppoli_vector_energy hlam (hxell hx) (hxb hx) (v x) (w x) (z x)
    · have hxη : x ∉ tsupport η := fun hs => hx (hsη hs)
      simp [v, w, z, P, Q, image_eq_zero_of_notMem_tsupport hxη,
        gradient_eq_zero_of_notMem_tsupport hxη]
  have hint := integral_mono_ae (hiV.const_mul (lam ^ 2))
    (((hiW.add hiZ).const_mul (8 * cap ^ 2 + 2 * lam + 2)).add
      (hiPQ.const_mul (2 * lam))) hpoint
  change (∫ x, lam ^ 2 * ‖v x‖ ^ 2) ≤
    ∫ x, (8 * cap ^ 2 + 2 * lam + 2) * (‖w x‖ ^ 2 + ‖z x‖ ^ 2) +
      2 * lam * inner ℝ (P x) (Q x) at hint
  rw [integral_const_mul,
    integral_add (f := fun x => (8 * cap ^ 2 + 2 * lam + 2) * (‖w x‖ ^ 2 + ‖z x‖ ^ 2))
      (g := fun x => 2 * lam * inner ℝ (P x) (Q x))
      ((hiW.add hiZ).const_mul _) (hiPQ.const_mul _),
    integral_const_mul, integral_add hiW hiZ, integral_const_mul, htest,
    mul_zero, add_zero] at hint
  have hres : (∫ x, ‖v x‖ ^ 2) ≤ ((8 * cap ^ 2 + 2 * lam + 2) / lam ^ 2) *
      ((∫ x, ‖w x‖ ^ 2) + ∫ x, ‖z x‖ ^ 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hlam)]
    nlinarith [hint]
  simpa only [v, w, z, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] using hres

/-- The weakly harmonic case of Caccioppoli, with an explicit universal constant. -/
theorem caccioppoli_harmonic {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u η : EuclideanSpace ℝ (Fin n) → ℝ}
    {D : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hu : HasLocallyH1GradientOn u D U)
    (hharm : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
        (∫ x, inner ℝ (D x) (gradient φ x)) = 0)
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ U) :
    (∫ x, η x ^ 2 * ‖D x‖ ^ 2) ≤ 12 * ∫ x, u x ^ 2 * ‖gradient η x‖ ^ 2 := by
  have hzero : IsLocallyL2On (fun _ : EuclideanSpace ℝ (Fin n) =>
      (0 : EuclideanSpace ℝ (Fin n))) U := by
    intro K _ _
    exact MemLp.zero
  have h := caccioppoli (A := fun _ => ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
    (G := fun _ => 0) (lam := 1) (cap := 1) hU (by norm_num) le_rfl
    aestronglyMeasurable_const
    (Eventually.of_forall fun x v => by simp)
    (Eventually.of_forall fun _ => ContinuousLinearMap.norm_id_le) hu hzero
    (by
      intro φ hφ hcφ hsφ
      simpa only [ContinuousLinearMap.id_apply, sub_zero] using hharm φ hφ hcφ hsφ)
    hη hcη hsη
  norm_num at h ⊢
  exact h

end LiquidDrop
