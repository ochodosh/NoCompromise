module

public import NoCompromise.Sobolev.H1PositivePartApprox
public import NoCompromise.Sobolev.H1TraceOperator
public import NoCompromise.Sobolev.H1MeanZero

@[expose] public section

/-!
# Positive parts in H¹ and their actual traces

Smooth nonnegative scalar approximations and smooth H¹ density give a bounded
sequence whose scalar components converge strongly in L². Weak Hilbert-space
compactness identifies a genuine H¹ positive part, its actual trace, and the
energy contraction. No nonlinear Sobolev chain rule or zero-trace equivalence
is assumed.
-/

noncomputable section
open MeasureTheory Filter Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma tendsto_lpNorm_sub_of_toLp_tendsto {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] {μ : Measure α} {f : ℕ → α → F} {g : α → F}
    (hf : ∀ j, MemLp (f j) 2 μ) (hg : MemLp g 2 μ)
    (ht : Tendsto (fun j => (hf j).toLp (f j)) atTop (𝓝 (hg.toLp g))) :
    Tendsto (fun j => lpNorm (f j - g) 2 μ) atTop (𝓝 0) := by
  have he := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).mp ht
  have hr := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).tendsto.comp he
  simpa only [Function.comp_def, toReal_eLpNorm,
    ENNReal.toReal_zero] using hr

lemma toLp_tendsto_of_lpNorm_sub {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] {μ : Measure α} {f : ℕ → α → F} {g : α → F}
    (hf : ∀ j, MemLp (f j) 2 μ) (hg : MemLp g 2 μ)
    (ht : Tendsto (fun j => lpNorm (f j - g) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun j => (hf j).toLp (f j)) atTop (𝓝 (hg.toLp g)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).mpr
  have he := (ENNReal.continuous_ofReal.tendsto 0).comp ht
  simpa only [Function.comp_def, ofReal_lpNorm ((hf _).sub hg), ENNReal.ofReal_zero] using he

lemma norm_sq_le_inner_of_strong_weak_limit {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {a b : ℕ → H} {u v : H} {C : ℝ}
    (ha : Tendsto a atTop (𝓝 u))
    (hb : ∀ ℓ : H →L[ℝ] ℝ, Tendsto (fun j => ℓ (b j)) atTop (𝓝 (ℓ v)))
    (hbound : ∀ j, ‖b j‖ ≤ C) (he : ∀ j, ‖b j‖ ^ 2 ≤ inner ℝ (a j) (b j)) :
    ‖v‖ ^ 2 ≤ inner ℝ u v := by
  have herr : Tendsto (fun j => inner ℝ (a j - u) (b j)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun j => (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hbound j) (norm_nonneg _)))
    simpa using ((ha.sub (tendsto_const_nhds (x := u))).norm).mul_const C
  have hpair : Tendsto (fun j => inner ℝ (a j) (b j)) atTop (𝓝 (inner ℝ u v)) := by
    have h := herr.add (hb (innerSL ℝ u))
    simp only [innerSL_apply_apply, inner_sub_left, sub_add_cancel, zero_add] at h
    exact h
  have hnonneg (j) : 0 ≤ inner ℝ (a j) (b j) -
      2 * inner ℝ v (b j) + ‖v‖ ^ 2 := by
    have hn := sq_nonneg ‖b j - v‖
    rw [norm_sub_sq_real] at hn
    have hi : inner ℝ (b j) v = inner ℝ v (b j) := real_inner_comm _ _
    rw [hi] at hn
    linarith [he j]
  have ht := (hpair.sub ((hb (innerSL ℝ v)).const_mul 2)).add
    (tendsto_const_nhds (x := ‖v‖ ^ 2))
  have h := ge_of_tendsto ht (Eventually.of_forall hnonneg)
  simp only [innerSL_apply_apply, real_inner_self_eq_norm_sq] at h
  linarith

/-- A positive-part H¹ representative, with its actual trace and energy contraction.
The trace map is any continuous linear map agreeing with continuous representatives. -/
theorem H1Space.exists_positivePart_of_trace_of_finite_measure {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D)
    {μ : Measure (EuclideanSpace ℝ (Fin n))} [IsFiniteMeasure μ]
    (T : H1Space D →L[ℝ] Lp ℝ 2 μ)
    (hT : ∀ f G (hf : HasH1GradientOn f G D), Continuous f →
      ⇑(T (H1Space.ofFunction f G hf)) =ᵐ[μ] f) (u : H1Space D) :
    ∃ v : H1Space D,
      (v =ᵐ[volume.restrict D] fun x => max (u x) 0) ∧
      (⇑(T v) =ᵐ[μ] fun x => max (T u x) 0) ∧
      ‖v.gradientLp‖ ^ 2 ≤ inner ℝ u.gradientLp v.gradientLp := by
  let : IsFiniteMeasure (volume.restrict D) := ⟨by simpa using hbD.measure_lt_top⟩
  obtain ⟨f, hf, hfc, hconv⟩ := exists_smooth_approx_on_domain hD hbD hL u
  let w (j : ℕ) := H1Space.ofFunction (f j) (gradient (f j)) (hf j)
  change Tendsto w atTop (𝓝 u) at hconv
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto w hconv).exists_norm_le
  have hwC (j : ℕ) : ‖w j‖ ≤ C := hC _ (mem_range_self j)
  let ε (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hεpos (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hεle (j : ℕ) : ε j ≤ 1 := by
    dsimp [ε]
    exact (div_le_one (by positivity)).mpr (by
      linarith [Nat.cast_nonneg (α := ℝ) j])
  let q (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) := smoothPositivePart (ε j) (f j x)
  have hq (j) : HasH1GradientOn (q j) (gradient (q j)) D :=
    hasH1GradientOn_smoothPositivePart_comp hD hbD.measure_lt_top
      ((hfc j).of_le (by simp)) (hf j) (hεpos j)
  have hqc (j) : Continuous (q j) :=
    (contDiff_smoothPositivePart (hεpos j)).continuous.comp (hfc j).continuous
  let z (j : ℕ) := H1Space.ofFunction (q j) (gradient (q j)) (hq j)
  have hzB (j) : ‖z j‖ ≤ 2 * C + (1 / 2 : ℝ) * (volume D).toReal ^ (1 / 2 : ℝ) := by
    have hz := norm_h1_smoothPositivePart_le hD hbD.measure_lt_top
      ((hfc j).of_le (by simp)) (hf j) (hεpos j)
    change ‖z j‖ ≤ _ at hz
    have he := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hεle j)
      (by norm_num : (0 : ℝ) ≤ 2))
      (by positivity : 0 ≤ (volume D).toReal ^ (1 / 2 : ℝ))
    exact hz.trans (add_le_add (mul_le_mul_of_nonneg_left (hwC j) (by norm_num)) he)
  obtain ⟨v, σ, hσ, _, hweak, hweakf, hweakG⟩ :=
    exists_subseq_weakly_tendsto_h1_components z hzB
  have hfstrong : Tendsto (fun j =>
      lpNorm (f j - (u : EuclideanSpace ℝ (Fin n) → ℝ)) 2 (volume.restrict D))
      atTop (𝓝 0) := by
    apply tendsto_lpNorm_sub_of_toLp_tendsto (fun j => (hf j).memLp_function)
      (Lp.memLp u.toLp)
    rw [Lp.toLp_coeFn]
    exact (H1Space.toLpCLM.continuous.tendsto u).comp hconv
  have hum : MemLp (fun x => max (u x) 0) 2 (volume.restrict D) :=
    memLp_real_positivePart (Lp.memLp u.toLp)
  have hqstrong := toLp_tendsto_of_lpNorm_sub (fun j => (hq j).memLp_function) hum
    (tendsto_lpNorm_smoothPositivePart_sub_max (fun j => (hf j).memLp_function)
      (Lp.memLp u.toLp) hfstrong hε hεpos)
  have hveq : hum.toLp (fun x => max (u x) 0) = v.toLp := by
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
    intro ℓ
    exact tendsto_nhds_unique
      ((ℓ.continuous.tendsto _).comp (hqstrong.comp hσ.tendsto_atTop)) (hweakf ℓ)
  have hvae : v =ᵐ[volume.restrict D] fun x => max (u x) 0 :=
    (Lp.ext_iff.mp hveq).symm.trans hum.coeFn_toLp
  have htfeq (j) : ⇑(T (w j)) =ᵐ[μ] f j :=
    hT _ _ (hf j) (hfc j).continuous
  have htfm (j) : MemLp (f j) 2 μ := (Lp.memLp (T (w j))).ae_eq (htfeq j)
  have htfun (j) : (htfm j).toLp (f j) = T (w j) := by
    apply Lp.ext
    exact (htfm j).coeFn_toLp.trans (htfeq j).symm
  have htstrong : Tendsto (fun j => lpNorm (f j - ⇑(T u)) 2 μ) atTop (𝓝 0) := by
    apply tendsto_lpNorm_sub_of_toLp_tendsto htfm (Lp.memLp (T u))
    simpa only [htfun, Lp.toLp_coeFn, Function.comp_def] using (T.continuous.tendsto u).comp hconv
  have htqm (j) : MemLp (q j) 2 μ := memLp_smoothPositivePart_comp (htfm j) (hεpos j)
  have htm : MemLp (fun x => max (T u x) 0) 2 μ := memLp_real_positivePart (Lp.memLp (T u))
  have htqstrong := toLp_tendsto_of_lpNorm_sub htqm htm
    (tendsto_lpNorm_smoothPositivePart_sub_max htfm (Lp.memLp (T u))
      htstrong hε hεpos)
  have htqfun (j) : (htqm j).toLp (q j) = T (z j) := by
    apply Lp.ext
    exact (htqm j).coeFn_toLp.trans (hT _ _ (hq j) (hqc j)).symm
  have htv : htm.toLp (fun x => max (T u x) 0) = T v := by
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
    intro ℓ
    have ht := (ℓ.continuous.tendsto _).comp (htqstrong.comp hσ.tendsto_atTop)
    simp only [htqfun] at ht
    exact tendsto_nhds_unique ht (hweak (ℓ.comp T))
  refine ⟨v, hvae, (Lp.ext_iff.mp htv).symm.trans htm.coeFn_toLp, ?_⟩
  apply norm_sq_le_inner_of_strong_weak_limit
    (((H1Space.gradientCLM.continuous.tendsto u).comp hconv).comp hσ.tendsto_atTop)
    hweakG (C := C)
  · intro j
    have hh := norm_gradientLp_smoothPositivePart_le hD hbD.measure_lt_top
      ((hfc (σ j)).of_le (by simp)) (hf (σ j)) (hεpos (σ j))
    exact hh.trans ((w (σ j)).norm_gradientLp_le.trans (hwC (σ j)))
  · intro j
    exact gradientLp_smoothPositivePart_energy_le hD hbD.measure_lt_top
      ((hfc (σ j)).of_le (by simp)) (hf (σ j)) (hεpos (σ j))

/-- Agreement with the constant function already forces finite trace measure
on a domain of finite volume. -/
lemma measure_lt_top_of_h1_trace {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (hvol : volume D < ∞)
    {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (T : H1Space D →L[ℝ] Lp ℝ 2 μ)
    (hT : ∀ f G (hf : HasH1GradientOn f G D), Continuous f →
      ⇑(T (H1Space.ofFunction f G hf)) =ᵐ[μ] f) : μ univ < ∞ := by
  have hm : MemLp (fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ)) 2 μ :=
    (Lp.memLp (T (H1Space.const hD hvol 1))).ae_eq
      (hT _ _ (hasH1GradientOn_const_of_finite_volume hD hvol 1) continuous_const)
  exact ((memLp_const_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).mp hm).resolve_left one_ne_zero

/-- Positive parts preserve the actual trace and satisfy the gradient energy
inequality, without an assumed nonlinear H¹ chain rule. -/
theorem H1Space.exists_positivePart_of_trace {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D)
    {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (T : H1Space D →L[ℝ] Lp ℝ 2 μ)
    (hT : ∀ f G (hf : HasH1GradientOn f G D), Continuous f →
      ⇑(T (H1Space.ofFunction f G hf)) =ᵐ[μ] f) (u : H1Space D) :
    ∃ v : H1Space D,
      (v =ᵐ[volume.restrict D] fun x => max (u x) 0) ∧
      (⇑(T v) =ᵐ[μ] fun x => max (T u x) 0) ∧
      ‖v.gradientLp‖ ^ 2 ≤ inner ℝ u.gradientLp v.gradientLp := by
  let : IsFiniteMeasure μ := ⟨measure_lt_top_of_h1_trace hD hbD.measure_lt_top T hT⟩
  exact exists_positivePart_of_trace_of_finite_measure hD hbD hL T hT u

/-- Every H¹ function on a bounded Lipschitz domain has its genuine positive
part in H¹, with the energy contraction used by the weak maximum principle. -/
theorem H1Space.exists_positivePart {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) (u : H1Space D) :
    ∃ v : H1Space D,
      (v =ᵐ[volume.restrict D] fun x => max (u x) 0) ∧
      ‖v.gradientLp‖ ^ 2 ≤ inner ℝ u.gradientLp v.gradientLp := by
  obtain ⟨v, hv, _, he⟩ := exists_positivePart_of_trace hD hbD hL
    (0 : H1Space D →L[ℝ] Lp ℝ 2 (0 : Measure (EuclideanSpace ℝ (Fin n))))
    (by intros; simp only [Filter.EventuallyEq, ae_zero]; exact Filter.eventually_bot) u
  exact ⟨v, hv, he⟩

end LiquidDrop
