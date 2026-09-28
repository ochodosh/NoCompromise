import NoCompromise.Sobolev.W11Calculus
import NoCompromise.Sobolev.H1Algebra

/-!
# Algebra of W¹,¹ representatives

The distributional identity is closed under finite sums and scalar multiples.
The sum of the function and gradient L¹ norms obeys the corresponding triangle
inequality, used when assembling the finite boundary partition.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace LiquidDrop

lemma HasWeakGradientOn.integrable_test_pairings {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasWeakGradientOn f G U) (i : Fin n)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ U) :
    IntegrableOn (fun x => f x * fderiv ℝ φ x (EuclideanSpace.single i 1)) U ∧
      IntegrableOn (fun x => φ x * G x i) U := by
  refine ⟨?_, (integrable_mul_compact_factor_on
    (locallyIntegrableOn_component hf.locallyIntegrable_gradient i)
    hφ.continuous hcφ hsφ).integrableOn⟩
  have hi := (integrable_mul_compact_factor_on hf.locallyIntegrable_function
    ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    (hcφ.fderiv_apply ℝ (EuclideanSpace.single i 1))
    ((tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := φ) _).trans hsφ)).integrableOn (s := U)
  simpa only [mul_comm] using hi

theorem HasW11GradientOn.zero {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) :
    HasW11GradientOn (fun _ => 0) (fun _ => 0) U :=
  ⟨(HasH1GradientOn.zero U).toHasWeakGradientOn, integrable_zero _ _ _, integrable_zero _ _ _⟩

theorem HasW11GradientOn.add {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {G H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasW11GradientOn f G U) (hg : HasW11GradientOn g H U) :
    HasW11GradientOn (fun x => f x + g x) (fun x => G x + H x) U := by
  refine ⟨⟨hf.locallyIntegrable_function.add hg.locallyIntegrable_function,
    hf.locallyIntegrable_gradient.add hg.locallyIntegrable_gradient, ?_⟩,
    hf.integrable_function.add hg.integrable_function,
    hf.integrable_gradient.add hg.integrable_gradient⟩
  intro i φ hφ hcφ hsφ
  obtain ⟨hif, hiG⟩ := hf.toHasWeakGradientOn.integrable_test_pairings i hφ hcφ hsφ
  obtain ⟨hig, hiH⟩ := hg.toHasWeakGradientOn.integrable_test_pairings i hφ hcφ hsφ
  simp_rw [PiLp.add_apply, add_mul, mul_add]
  rw [integral_add hif hig, integral_add hiG hiH]
  linarith [hf.test_eq i φ hφ hcφ hsφ, hg.test_eq i φ hφ hcφ hsφ]

theorem HasW11GradientOn.const_mul {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasW11GradientOn f G U) (c : ℝ) :
    HasW11GradientOn (fun x => c * f x) (fun x => c • G x) U := by
  have hif : IntegrableOn (fun x => c * f x) U := hf.integrable_function.const_mul c
  have hiG : IntegrableOn (fun x => c • G x) U := hf.integrable_gradient.smul c
  refine ⟨⟨hif.locallyIntegrableOn, hiG.locallyIntegrableOn, ?_⟩, hif, hiG⟩
  intro i φ hφ hcφ hsφ
  simp only [PiLp.smul_apply, smul_eq_mul]
  simp_rw [mul_assoc c, mul_left_comm (φ _) c, integral_const_mul]
  linarith [congrArg (fun v : ℝ => c * v) (hf.test_eq i φ hφ hcφ hsφ)]

theorem HasW11GradientOn.neg {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasW11GradientOn f G U) :
    HasW11GradientOn (fun x => -f x) (fun x => -G x) U := by
  simpa only [neg_one_mul, neg_one_smul] using hf.const_mul (-1)

theorem HasW11GradientOn.sub {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {G H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasW11GradientOn f G U) (hg : HasW11GradientOn g H U) :
    HasW11GradientOn (fun x => f x - g x) (fun x => G x - H x) U := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem HasW11GradientOn.finsetSum {n : ℕ} {ι : Type*}
    {U : Set (EuclideanSpace ℝ (Fin n))} (s : Finset ι)
    {f : ι → EuclideanSpace ℝ (Fin n) → ℝ}
    {G : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : ∀ i ∈ s, HasW11GradientOn (f i) (G i) U) :
    HasW11GradientOn (fun x => ∑ i ∈ s, f i x) (fun x => ∑ i ∈ s, G i x) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasW11GradientOn.zero U
  | @insert i s hi hs =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self i s)).add (hs fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem w11_lpNorm_finsetSum_le {n : ℕ} {ι : Type*}
    {U : Set (EuclideanSpace ℝ (Fin n))} (s : Finset ι)
    {f : ι → EuclideanSpace ℝ (Fin n) → ℝ}
    {G : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : ∀ i ∈ s, HasW11GradientOn (f i) (G i) U) :
    lpNorm (fun x => ∑ i ∈ s, f i x) 1 (volume.restrict U) +
      lpNorm (fun x => ∑ i ∈ s, G i x) 1 (volume.restrict U) ≤
        ∑ i ∈ s, (lpNorm (f i) 1 (volume.restrict U) +
          lpNorm (G i) 1 (volume.restrict U)) := by
  simpa only [← Finset.sum_apply, Finset.sum_add_distrib] using
    add_le_add (lpNorm_sum_le (fun i hi => (hf i hi).memLp_function) (by norm_num))
      (lpNorm_sum_le (fun i hi => (hf i hi).memLp_gradient) (by norm_num))

theorem HasW11GradientOn.mono {n : ℕ} {U V : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasW11GradientOn f G U) (hVU : V ⊆ U) : HasW11GradientOn f G V :=
  ⟨hf.toHasWeakGradientOn.mono hVU,
    hf.integrable_function.mono_set hVU, hf.integrable_gradient.mono_set hVU⟩

end LiquidDrop
