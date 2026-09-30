module

public import NoCompromise.Sobolev.H1Zero
public import NoCompromise.Sobolev.H1TestApprox
public import NoCompromise.Sobolev.H1DifferenceQuotient

@[expose] public section

/-!
# Interior approximation for the zero-boundary Sobolev space

Compactly supported global H¹ functions lying inside an open domain belong to
its actual H¹₀ closure. Inward translations extend this criterion to functions
whose support can meet the boundary.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma tendsto_lpNorm_sub_of_eLpNorm {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] {μ : Measure α} {f : ℕ → α → F} {g : α → F}
    (hf : ∀ j, MemLp (f j) 2 μ) (hg : MemLp g 2 μ)
    (ht : Tendsto (fun j => eLpNorm (f j - g) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun j => lpNorm (f j - g) 2 μ) atTop (𝓝 0) := by
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
  simpa only [Function.comp_def, toReal_eLpNorm, ENNReal.toReal_zero] using h

/-- Compact support in the open domain gives membership in the defining H¹ closure,
without any boundary regularity assumption. -/
theorem HasH1GradientOn.mem_h1Zero_of_compact_support {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G univ) (hcf : HasCompactSupport f) (hsf : tsupport f ⊆ U) :
    H1Space.ofFunction f G (hf.mono (subset_univ U)) ∈ h1ZeroSubmodule hU := by
  obtain ⟨V, _, _, _, hVU, _, v, hv, hcv, hcG⟩ :=
    hf.exists_smooth_compact_test_approximation hU hcf hsf
  have hmf : MemLp f 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_function
  have hmG : MemLp G 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_gradient
  have hmv (j : ℕ) : MemLp (v j) 2 volume := by
    simpa only [Measure.restrict_univ] using (hv j).2.2.2.memLp_function
  have hmvg (j : ℕ) : MemLp (gradient (v j)) 2 volume := by
    simpa only [Measure.restrict_univ] using (hv j).2.2.2.memLp_gradient
  have hconv := H1Space.tendsto_ofFunction_restrict hU hf (fun j => (hv j).2.2.2)
    (tendsto_lpNorm_sub_of_eLpNorm hmv hmf hcv)
    (tendsto_lpNorm_sub_of_eLpNorm hmvg hmG hcG)
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hconv
  apply Eventually.of_forall
  intro j
  apply subset_closure
  let w : h1ZeroTestFunctions U :=
    ⟨v j, (hv j).1, (hv j).2.1, (hv j).2.2.1.trans (subset_closure.trans hVU)⟩
  exact ⟨w, rfl⟩

/-- A strong global H¹ limit of functions compactly supported inside U belongs
to H¹₀(U), regardless of how those interior representatives were produced. -/
theorem HasH1GradientOn.mem_h1Zero_of_interior_approximation {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G univ)
    {v : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    {H : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hv : ∀ j, HasH1GradientOn (v j) (H j) univ)
    (hcv : ∀ j, HasCompactSupport (v j)) (hsv : ∀ j, tsupport (v j) ⊆ U)
    (hfconv : Tendsto (fun j => lpNorm (v j - f) 2 volume) atTop (𝓝 0))
    (hGconv : Tendsto (fun j => lpNorm (H j - G) 2 volume) atTop (𝓝 0)) :
    H1Space.ofFunction f G (hf.mono (subset_univ U)) ∈ h1ZeroSubmodule hU :=
  (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
    (H1Space.tendsto_ofFunction_restrict hU hf hv hfconv hGconv)
    (Eventually.of_forall fun j => (hv j).mem_h1Zero_of_compact_support hU (hcv j) (hsv j))

/-- Compact global H¹ functions which admit arbitrarily small inward translations
are in H¹₀(U). The support condition makes the geometric requirement explicit. -/
theorem HasH1GradientOn.mem_h1Zero_of_inward_translations {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G univ) (hcf : HasCompactSupport f)
    {a : ℕ → EuclideanSpace ℝ (Fin n)} (ha : Tendsto a atTop (𝓝 0))
    (hs : ∀ j, tsupport (fun x => f (x - a j)) ⊆ U) :
    H1Space.ofFunction f G (hf.mono (subset_univ U)) ∈ h1ZeroSubmodule hU := by
  have hv (j : ℕ) : HasH1GradientOn (fun x => f (x - a j)) (fun x => G (x - a j)) univ := by
    simpa only [sub_eq_add_neg] using
      hf.translate isOpen_univ isOpen_univ (-a j) (fun _ _ => mem_univ _)
  have hc (j : ℕ) : HasCompactSupport (fun x => f (x - a j)) :=
    hcf.comp_homeomorph (Homeomorph.subRight (a j))
  have hmf : MemLp f 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_function
  have hmG : MemLp G 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_gradient
  have hmfj (j : ℕ) : MemLp (fun x => f (x - a j)) 2 volume :=
    hmf.comp_measurePreserving (measurePreserving_sub_right volume (a j))
  have hmGj (j : ℕ) : MemLp (fun x => G (x - a j)) 2 volume :=
    hmG.comp_measurePreserving (measurePreserving_sub_right volume (a j))
  exact hf.mem_h1Zero_of_interior_approximation hU hv hc hs
    (tendsto_lpNorm_sub_of_eLpNorm hmfj hmf
      ((tendsto_eLpNorm_translate_sub_zero (by norm_num) hmf).comp ha))
    (tendsto_lpNorm_sub_of_eLpNorm hmGj hmG
      ((tendsto_eLpNorm_translate_sub_zero (by norm_num) hmG).comp ha))

/-- A compact global H¹ function supported on the closed upper half-space belongs
to H¹₀ of the open half-space. Translation gives strict interior clearance. -/
theorem HasH1GradientOn.mem_h1Zero_upperHalfspace_of_support {n : ℕ} (i : Fin n)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasH1GradientOn f G univ) (hcf : HasCompactSupport f)
    (hs : ∀ x ∈ tsupport f, 0 ≤ x i) :
    H1Space.ofFunction f G
        (hf.mono (subset_univ {x : EuclideanSpace ℝ (Fin n) | 0 < x i})) ∈
      h1ZeroSubmodule (show IsOpen {x : EuclideanSpace ℝ (Fin n) | 0 < x i} from
        isOpen_lt continuous_const (EuclideanSpace.proj i).continuous) := by
  let a (j : ℕ) := (1 / ((j : ℝ) + 1)) • EuclideanSpace.single i (1 : ℝ)
  have ha : Tendsto a atTop (𝓝 0) := by
    simpa only [zero_smul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul
        (tendsto_const_nhds (x := EuclideanSpace.single i (1 : ℝ)))
  apply hf.mem_h1Zero_of_inward_translations
    (isOpen_lt continuous_const (EuclideanSpace.proj i).continuous) hcf ha
  intro j x hx
  have hpre : x - a j ∈ tsupport f :=
    tsupport_comp_subset_preimage f (continuous_id.sub continuous_const) hx
  have h := hs (x - a j) hpre
  simp only [PiLp.sub_apply, a, PiLp.smul_apply, PiLp.single_apply, ite_true, smul_eq_mul,
    mul_one] at h
  have hj : 0 < 1 / ((j : ℝ) + 1) := by positivity
  change 0 < x i
  linarith

end LiquidDrop
