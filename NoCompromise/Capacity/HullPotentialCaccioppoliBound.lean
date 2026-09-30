module

public import NoCompromise.Capacity.HullPotentialCaccioppoli

@[expose] public section

/-!
# L² gradient bound for the capacitary potential up to the obstacle

For the capacitary potential `u` of a closed set `K` (`u = 1` on `K`, `0 < u < 1` and
harmonic off `K`), testing the weak Laplace equation with `η² Θε(1 - u)`, where
`Θε t = t χ(t/ε - 1)` cuts off the values near `0`, gives the Caccioppoli bound
`∫ η² Θε'(1 - u) |∇u|² ≤ 4 ∫ |∇η|²`, uniform in `ε`. Letting `ε → 0` by monotone convergence
shows that `|∇u|²` is integrable on `Kᶜ ∩ ball z r`.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The cut-off `Θε t = t χ(t/ε - 1)`: zero for `t ≤ ε`, the identity for `t ≥ 2ε`. -/
private def hullCaccTheta (ε t : ℝ) : ℝ := t * Real.smoothTransition (t / ε - 1)

private lemma hullCaccTheta_contDiff (ε : ℝ) : ContDiff ℝ 1 (hullCaccTheta ε) := by
  unfold hullCaccTheta
  exact contDiff_id.mul
    (Real.smoothTransition.contDiff.comp ((contDiff_id.div_const ε).sub contDiff_const))

private lemma hullCaccTheta_eq_zero {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ ε) :
    hullCaccTheta ε t = 0 := by
  unfold hullCaccTheta
  rw [Real.smoothTransition.zero_of_nonpos, mul_zero]
  rw [sub_nonpos, div_le_one hε]
  exact ht

private lemma hullCaccTheta_deriv_eq_zero {ε t : ℝ} (hε : 0 < ε) (ht : t < ε) :
    deriv (hullCaccTheta ε) t = 0 := by
  have h : hullCaccTheta ε =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact hullCaccTheta_eq_zero hε (le_of_lt hs)
  rw [h.deriv_eq, deriv_const]

private lemma hullCaccTheta_eq_self {ε t : ℝ} (hε : 0 < ε) (ht : 2 * ε ≤ t) :
    hullCaccTheta ε t = t := by
  unfold hullCaccTheta
  rw [Real.smoothTransition.one_of_one_le, mul_one]
  rw [le_sub_iff_add_le, le_div_iff₀ hε]
  linarith

private lemma hullCaccTheta_deriv_eq_one {ε t : ℝ} (hε : 0 < ε) (ht : 2 * ε < t) :
    deriv (hullCaccTheta ε) t = 1 := by
  have h : hullCaccTheta ε =ᶠ[𝓝 t] fun s => s := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact hullCaccTheta_eq_self hε (le_of_lt hs)
  rw [h.deriv_eq, deriv_id'']

private lemma hullCaccTheta_hasDerivAt (ε t : ℝ) :
    HasDerivAt (hullCaccTheta ε) (Real.smoothTransition (t / ε - 1) +
      t * (deriv Real.smoothTransition (t / ε - 1) * (1 / ε))) t := by
  have h1 : HasDerivAt (fun s : ℝ => s / ε - 1) (1 / ε) t := by
    simpa using ((hasDerivAt_id t).div_const ε).sub_const 1
  have h2 : HasDerivAt (fun s => Real.smoothTransition (s / ε - 1))
      (deriv Real.smoothTransition (t / ε - 1) * (1 / ε)) t :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp) _).hasDerivAt.comp t h1
  have h3 := (hasDerivAt_id t).mul h2
  simp only [id, one_mul] at h3
  exact h3

private lemma hullCaccTheta_le_deriv {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    Real.smoothTransition (t / ε - 1) ≤ deriv (hullCaccTheta ε) t := by
  rw [(hullCaccTheta_hasDerivAt ε t).deriv]
  have h0 : 0 ≤ deriv Real.smoothTransition (t / ε - 1) :=
    Real.smoothTransition.monotone.deriv_nonneg
  have : 0 ≤ t * (deriv Real.smoothTransition (t / ε - 1) * (1 / ε)) := by positivity
  linarith

/-- A function C¹ on an open set whose topological support lies in the set is C¹. -/
private lemma hullCacc_contDiff_of_tsupport {V : Set (EuclideanSpace ℝ (Fin 3))} (hV : IsOpen V)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiffOn ℝ 1 f V) (hs : tsupport f ⊆ V) :
    ContDiff ℝ 1 f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ V
  · exact hf.contDiffAt (hV.mem_nhds hx)
  · have h : f =ᶠ[𝓝 x] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hs h))
    exact contDiffAt_const.congr_of_eventuallyEq h

/-- A compactly supported function continuous on an open set containing its topological support
is integrable. -/
private lemma hullCacc_integrable {V : Set (EuclideanSpace ℝ (Fin 3))} (hV : IsOpen V)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContinuousOn f V) (hs : tsupport f ⊆ V)
    (hc : HasCompactSupport f) : Integrable f :=
  (hf.continuous_of_tsupport_subset hV hs).integrable_of_hasCompactSupport hc

/-- The Caccioppoli bound with the cut-off `Θε`: testing the weak Laplace equation with
`η² Θε(1 - u)` gives `∫ η² Θε'(1 - u) |∇u|² ≤ 4 ∫ |∇η|²`. -/
private lemma hullCacc_energy_le {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsClosed K)
    {u : EuclideanSpace ℝ (Fin 3) → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (h1 : ∀ x ∈ K, u x = 1) (hs : ∀ x ∈ Kᶜ, 0 < u x ∧ u x < 1)
    {η : EuclideanSpace ℝ (Fin 3) → ℝ} (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    {ε : ℝ} (hε : 0 < ε) :
    (∀ x, 0 ≤ η x ^ 2 * deriv (hullCaccTheta ε) (1 - u x) * ‖gradient u x‖ ^ 2) ∧
    Integrable (fun x => η x ^ 2 * deriv (hullCaccTheta ε) (1 - u x) * ‖gradient u x‖ ^ 2) ∧
    (∫ x, η x ^ 2 * deriv (hullCaccTheta ε) (1 - u x) * ‖gradient u x‖ ^ 2) ≤
      4 * ∫ x, ‖gradient η x‖ ^ 2 := by
  have hKo : IsOpen Kᶜ := hK.isOpen_compl
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) u Kᶜ :=
    hh.contDiffOn_of_continuous (by norm_num) hKo hu.continuousOn
  have hu1 : ContDiffOn ℝ 1 u Kᶜ := hsm.of_le (by exact_mod_cast le_top)
  have hC0 := isWeakDivergenceEquationOn_id_of_harmonic hKo hu.continuousOn hh
  have hule : ∀ x, u x ≤ 1 := fun x => by
    by_cases hx : x ∈ K
    · exact (h1 x hx).le
    · exact (hs x hx).2.le
  have hΘ : ContDiff ℝ 1 (hullCaccTheta ε) := hullCaccTheta_contDiff ε
  have hF : IsClosed {x : EuclideanSpace ℝ (Fin 3) | u x ≤ 1 - ε} :=
    isClosed_le hu continuous_const
  have hFK : {x : EuclideanSpace ℝ (Fin 3) | u x ≤ 1 - ε} ⊆ Kᶜ := by
    intro x hx hxK
    have h : u x ≤ 1 - ε := hx
    rw [h1 x hxK] at h
    linarith
  -- the test function `ψ = η² Θε(1 - u)`
  let ψ : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => η x ^ 2 * hullCaccTheta ε (1 - u x)
  have hψF : Function.support ψ ⊆ {x | u x ≤ 1 - ε} := by
    intro x hx
    by_contra hxF
    apply hx
    have h : 1 - u x ≤ ε := by
      have : ¬ u x ≤ 1 - ε := hxF
      linarith
    simp only [ψ, hullCaccTheta_eq_zero hε h, mul_zero]
  have hψη : Function.support ψ ⊆ Function.support η := by
    intro x hx hηx
    apply hx
    have h : η x = 0 := hηx
    simp only [ψ, h]
    ring
  have htψ : tsupport ψ ⊆ Kᶜ := (closure_minimal hψF hF).trans hFK
  have hcψ : HasCompactSupport ψ := hcη.mono hψη
  have hψ : ContDiff ℝ 1 ψ := by
    apply hullCacc_contDiff_of_tsupport hKo _ htψ
    exact (hη.contDiffOn.pow 2).mul (hΘ.comp_contDiffOn (contDiffOn_const.sub hu1))
  have hint0 := hC0 ψ hψ hcψ htψ
  simp only [ContinuousLinearMap.id_apply, sub_zero] at hint0
  -- the two pieces of `⟪∇u, ∇ψ⟫`
  let a : EuclideanSpace ℝ (Fin 3) → ℝ := fun x =>
    η x ^ 2 * deriv (hullCaccTheta ε) (1 - u x) * ‖gradient u x‖ ^ 2
  let b : EuclideanSpace ℝ (Fin 3) → ℝ := fun x =>
    2 * η x * hullCaccTheta ε (1 - u x) * ⟪gradient η x, gradient u x⟫
  have hgx : ∀ x, ⟪gradient u x, gradient ψ x⟫ = b x - a x := by
    intro x
    by_cases hx : x ∈ Kᶜ
    · have hux : HasFDerivAt u (fderiv ℝ u x) x :=
        ((hu1.differentiableOn one_ne_zero x hx).differentiableAt (hKo.mem_nhds hx)).hasFDerivAt
      have hηx : HasFDerivAt η (fderiv ℝ η x) x := (hη.differentiable one_ne_zero x).hasFDerivAt
      have hΘx : HasDerivAt (hullCaccTheta ε) (deriv (hullCaccTheta ε) (1 - u x)) (1 - u x) :=
        (hΘ.differentiable one_ne_zero _).hasDerivAt
      have hcx : HasFDerivAt (fun y => hullCaccTheta ε (1 - u y))
          (deriv (hullCaccTheta ε) (1 - u x) • -fderiv ℝ u x) x :=
        HasDerivAt.comp_hasFDerivAt (h₂ := hullCaccTheta ε) x hΘx (hux.const_sub 1)
      have hψx : HasFDerivAt ψ _ x := (hηx.pow 2).mul hcx
      have e1 : fderiv ℝ u x (gradient u x) = ‖gradient u x‖ ^ 2 := by
        rw [← inner_gradient_left, real_inner_self_eq_norm_sq]
      have e2 : fderiv ℝ η x (gradient u x) = ⟪gradient η x, gradient u x⟫ :=
        inner_gradient_left.symm
      rw [real_inner_comm, inner_gradient_left, hψx.fderiv]
      simp only [_root_.add_apply, _root_.smul_apply, _root_.neg_apply, smul_eq_mul, e1, e2, a, b]
      push_cast
      ring
    · have hxψ : x ∉ tsupport ψ := fun h => hx (htψ h)
      rw [gradient_eq_zero_of_notMem_tsupport hxψ, inner_zero_right]
      have hux : u x = 1 := h1 x (not_not.mp hx)
      simp only [a, b, hux, sub_self, hullCaccTheta_eq_zero hε hε.le,
        hullCaccTheta_deriv_eq_zero hε hε]
      ring
  -- integrability of the pieces
  have hgu : ContinuousOn (gradient u) Kᶜ := continuousOn_gradient_of_contDiffOn hKo hu1
  have hgη : Continuous (gradient η) := continuous_gradient_of_contDiff hη
  have hdΘ : Continuous (deriv (hullCaccTheta ε)) := hΘ.continuous_deriv le_rfl
  have haF : Function.support a ⊆ {x | u x ≤ 1 - ε} := by
    intro x hx
    by_contra hxF
    apply hx
    have h : 1 - u x < ε := by
      have : ¬ u x ≤ 1 - ε := hxF
      linarith
    simp only [a, hullCaccTheta_deriv_eq_zero hε h, mul_zero, zero_mul]
  have hbF : Function.support b ⊆ {x | u x ≤ 1 - ε} := by
    intro x hx
    by_contra hxF
    apply hx
    have h : 1 - u x ≤ ε := by
      have : ¬ u x ≤ 1 - ε := hxF
      linarith
    simp only [b, hullCaccTheta_eq_zero hε h, mul_zero, zero_mul]
  have haη : Function.support a ⊆ Function.support η := by
    intro x hx hηx
    apply hx
    have h : η x = 0 := hηx
    simp only [a, h]
    ring
  have hbη : Function.support b ⊆ Function.support η := by
    intro x hx hηx
    apply hx
    have h : η x = 0 := hηx
    simp only [b, h]
    ring
  have hac : ContinuousOn a Kᶜ :=
    (((hη.continuous.pow 2).mul (hdΘ.comp (continuous_const.sub hu))).continuousOn).mul
      (hgu.norm.pow 2)
  have hbc : ContinuousOn b Kᶜ :=
    (((continuous_const.mul hη.continuous).mul
      (hΘ.continuous.comp (continuous_const.sub hu))).continuousOn).mul
      (hgη.continuousOn.inner hgu)
  have hai : Integrable a :=
    hullCacc_integrable hKo hac ((closure_minimal haF hF).trans hFK) (hcη.mono haη)
  have hbi : Integrable b :=
    hullCacc_integrable hKo hbc ((closure_minimal hbF hF).trans hFK) (hcη.mono hbη)
  have hNs : Function.support (fun x => ‖gradient η x‖ ^ 2) ⊆ tsupport η := by
    intro x hx
    by_contra hxη
    apply hx
    simp only [gradient_eq_zero_of_notMem_tsupport hxη, norm_zero]
    ring
  have hNi : Integrable (fun x => ‖gradient η x‖ ^ 2) :=
    (hgη.norm.pow 2).integrable_of_hasCompactSupport (hcη.mono' hNs)
  -- pointwise bounds
  have hann : ∀ x, 0 ≤ a x := by
    intro x
    have ht : 0 ≤ 1 - u x := by linarith [hule x]
    have hd : 0 ≤ deriv (hullCaccTheta ε) (1 - u x) :=
      (Real.smoothTransition.nonneg _).trans (hullCaccTheta_le_deriv hε ht)
    have : 0 ≤ η x ^ 2 * deriv (hullCaccTheta ε) (1 - u x) := mul_nonneg (sq_nonneg _) hd
    exact mul_nonneg this (sq_nonneg _)
  have hpt : ∀ x, b x ≤ a x / 2 + 2 * ‖gradient η x‖ ^ 2 := by
    intro x
    by_cases hx : x ∈ Kᶜ
    · set t := 1 - u x with ht
      have ht0 : 0 < t := by linarith [(hs x hx).2]
      have ht1 : t ≤ 1 := by linarith [(hs x hx).1]
      set c := Real.smoothTransition (t / ε - 1) with hc
      have hc0 : 0 ≤ c := Real.smoothTransition.nonneg _
      have hc1 : c ≤ 1 := Real.smoothTransition.le_one _
      set d := deriv (hullCaccTheta ε) t with hd
      have hcd : c ≤ d := hullCaccTheta_le_deriv hε ht0.le
      have hΘt : hullCaccTheta ε t = t * c := rfl
      set e := η x with he
      set G := ‖gradient u x‖ with hG
      set N := ‖gradient η x‖ with hN
      set P := ⟪gradient η x, gradient u x⟫ with hP
      have hPle : |P| ≤ N * G := abs_real_inner_le_norm _ _
      have hG0 : 0 ≤ G := norm_nonneg _
      have hN0 : 0 ≤ N := norm_nonneg _
      have hab : a x = e ^ 2 * d * G ^ 2 := rfl
      have hbb : b x = 2 * e * (t * c) * P := rfl
      rw [hab, hbb]
      have htc : 0 ≤ t * c := mul_nonneg ht0.le hc0
      have hq1 : e * P ≤ |e| * (N * G) := by
        calc e * P ≤ |e * P| := le_abs_self _
          _ = |e| * |P| := abs_mul _ _
          _ ≤ |e| * (N * G) := mul_le_mul_of_nonneg_left hPle (abs_nonneg e)
      have hq2 : 2 * e * (t * c) * P ≤ 2 * (t * c) * (|e| * (N * G)) := by
        have := mul_le_mul_of_nonneg_left hq1 (mul_nonneg zero_le_two htc)
        linarith
      have hq3 : 2 * (t * c) * (|e| * (N * G)) ≤
          c * (e ^ 2 * G ^ 2) / 2 + 2 * (c * t ^ 2) * N ^ 2 := by
        have h0 := mul_nonneg hc0 (sq_nonneg (|e| * G - 2 * t * N))
        rw [← sq_abs e]
        linarith
      have hq4 : c * (e ^ 2 * G ^ 2) ≤ d * (e ^ 2 * G ^ 2) :=
        mul_le_mul_of_nonneg_right hcd (by positivity)
      have hq5 : c * t ^ 2 ≤ 1 := by
        have : t ^ 2 ≤ 1 := by nlinarith
        calc c * t ^ 2 ≤ 1 * 1 := mul_le_mul hc1 this (sq_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      have hq6 : (c * t ^ 2) * N ^ 2 ≤ N ^ 2 := by
        have := mul_le_mul_of_nonneg_right hq5 (sq_nonneg N)
        linarith
      linarith
    · have hux : u x = 1 := h1 x (not_not.mp hx)
      have hb0 : b x = 0 := by
        simp only [b, hux, sub_self, hullCaccTheta_eq_zero hε hε.le, mul_zero, zero_mul]
      have ha0 : a x = 0 := by
        simp only [a, hux, sub_self, hullCaccTheta_deriv_eq_zero hε hε, mul_zero, zero_mul]
      rw [ha0, hb0]
      positivity
  -- integrate
  have hgb : (fun x => ⟪gradient u x, gradient ψ x⟫) = fun x => b x - a x := funext hgx
  rw [hgb, integral_sub hbi hai] at hint0
  have hmono : ∫ x, b x ≤ ∫ x, (a x / 2 + 2 * ‖gradient η x‖ ^ 2) :=
    integral_mono hbi ((hai.div_const 2).add (hNi.const_mul 2)) hpt
  rw [integral_add (hai.div_const 2) (hNi.const_mul 2), integral_div, integral_const_mul] at hmono
  refine ⟨hann, hai, ?_⟩
  change ∫ x, a x ≤ 4 * ∫ x, ‖gradient η x‖ ^ 2
  linarith

/-- **Boundary Caccioppoli, qualitative form.** For a continuous function `u` which is `1` on a
closed set `K`, takes values in `(0, 1)` and is distributionally harmonic off `K` (the capacitary
potential of `K`), `|∇u|²` is integrable on `Kᶜ ∩ ball z r` for every ball. -/
theorem exterior_gradient_sq_integrableOn {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsClosed K)
    {u : EuclideanSpace ℝ (Fin 3) → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (h1 : ∀ x ∈ K, u x = 1) (hs : ∀ x ∈ Kᶜ, 0 < u x ∧ u x < 1)
    (z : EuclideanSpace ℝ (Fin 3)) (r : ℝ) :
    IntegrableOn (fun x => ‖gradient u x‖ ^ 2) (Kᶜ ∩ Metric.ball z r) := by
  have hKo : IsOpen Kᶜ := hK.isOpen_compl
  have hu1 : ContDiffOn ℝ 1 u Kᶜ :=
    (hh.contDiffOn_of_continuous (by norm_num) hKo hu.continuousOn).of_le
      (by exact_mod_cast le_top)
  let η : ContDiffBump z := ⟨|r| + 1, |r| + 2, by positivity, by linarith⟩
  have hη : ContDiff ℝ 1 η := η.contDiff
  have hcη : HasCompactSupport η := η.hasCompactSupport
  have hη1 : ∀ x ∈ Metric.ball z r, η x = 1 := by
    intro x hx
    apply η.one_of_mem_closedBall
    rw [Metric.mem_closedBall]
    have h1 := Metric.mem_ball.mp hx
    have h2 : r ≤ |r| := le_abs_self r
    change dist x z ≤ |r| + 1
    linarith
  let S : ℕ → Set (EuclideanSpace ℝ (Fin 3)) := fun n =>
    Kᶜ ∩ Metric.ball z r ∩ {x | u x < 1 - 2 * (1 / ((n : ℝ) + 1))}
  have hSo : ∀ n, IsOpen (S n) := fun n =>
    (hKo.inter isOpen_ball).inter (isOpen_lt hu continuous_const)
  have hSle : ∀ n, ∫⁻ x in S n, ENNReal.ofReal (‖gradient u x‖ ^ 2) ≤
      ENNReal.ofReal (4 * ∫ x, ‖gradient η x‖ ^ 2) := by
    intro n
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨hann, hai, hle⟩ := hullCacc_energy_le hK hu hh h1 hs hη hcη hε
    calc ∫⁻ x in S n, ENNReal.ofReal (‖gradient u x‖ ^ 2)
        = ∫⁻ x in S n, ENNReal.ofReal (η x ^ 2 *
            deriv (hullCaccTheta (1 / ((n : ℝ) + 1))) (1 - u x) * ‖gradient u x‖ ^ 2) := by
          refine setLIntegral_congr_fun (hSo n).measurableSet (fun x hx => ?_)
          have hxb : x ∈ Metric.ball z r := hx.1.2
          have hxu : u x < 1 - 2 * (1 / ((n : ℝ) + 1)) := hx.2
          rw [hη1 x hxb, hullCaccTheta_deriv_eq_one hε (by linarith)]
          ring_nf
      _ ≤ ∫⁻ x, ENNReal.ofReal (η x ^ 2 *
            deriv (hullCaccTheta (1 / ((n : ℝ) + 1))) (1 - u x) * ‖gradient u x‖ ^ 2) :=
          setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (∫ x, η x ^ 2 *
            deriv (hullCaccTheta (1 / ((n : ℝ) + 1))) (1 - u x) * ‖gradient u x‖ ^ 2) :=
          (ofReal_integral_eq_lintegral_ofReal hai (ae_of_all _ hann)).symm
      _ ≤ ENNReal.ofReal (4 * ∫ x, ‖gradient η x‖ ^ 2) := ENNReal.ofReal_le_ofReal hle
  have hmono : Monotone S := by
    intro m n hmn x hx
    refine ⟨hx.1, ?_⟩
    have hx2 : u x < 1 - 2 * (1 / ((m : ℝ) + 1)) := hx.2
    change u x < 1 - 2 * (1 / ((n : ℝ) + 1))
    have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
    linarith
  have hU : Kᶜ ∩ Metric.ball z r = ⋃ n, S n := by
    ext x
    simp only [mem_iUnion]
    constructor
    · intro hx
      have hlt : 0 < (1 - u x) / 2 := by linarith [(hs x hx.1).2]
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hlt
      exact ⟨n, hx, show u x < 1 - 2 * (1 / ((n : ℝ) + 1)) by linarith⟩
    · rintro ⟨n, hx⟩
      exact hx.1
  have hfin : ∫⁻ x in Kᶜ ∩ Metric.ball z r, ENNReal.ofReal (‖gradient u x‖ ^ 2) < ∞ := by
    rw [hU, setLIntegral_iUnion_of_directed _ hmono.directed_le]
    exact lt_of_le_of_lt (iSup_le hSle) ENNReal.ofReal_lt_top
  have hcont : ContinuousOn (fun x => ‖gradient u x‖ ^ 2) (Kᶜ ∩ Metric.ball z r) :=
    ((continuousOn_gradient_of_contDiffOn hKo hu1).norm.pow 2).mono inter_subset_left
  refine ⟨hcont.aestronglyMeasurable (hKo.inter isOpen_ball).measurableSet, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => sq_nonneg _)).mpr hfin

end LiquidDrop
