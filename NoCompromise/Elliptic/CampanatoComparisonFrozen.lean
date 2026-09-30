module

public import NoCompromise.Elliptic.CampanatoComparison
public import NoCompromise.Elliptic.VariationalHilbert
public import NoCompromise.Sobolev.H1TraceKernelApprox

@[expose] public section

/-!
# Construction of the frozen harmonic replacement

Nonsymmetric coercive Hilbert solvability is proved here from Riesz
representation, closed range, and orthogonal complements. Bounded-domain
Poincaré makes the frozen elliptic form coercive on the genuine H¹₀ space.
The resulting replacement satisfies the original compact C¹ weak tests and
the full squared-gradient comparison in every positive dimension.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Nonsymmetric coercive Hilbert solvability derived from Riesz representation,
closed range, and the orthogonal complement, without invoking Lax–Milgram. -/
theorem campanato_exists_coercive_bilinear_solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ u, κ * ‖u‖ ^ 2 ≤ B u u) (ℓ : E →L[ℝ] ℝ) :
    ∃ u : E, ∀ v, B u v = ℓ v := by
  let T : E →L[ℝ] E := (toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp B
  have hT (u v : E) : inner ℝ (T u) v = B u v := toDual_symm_apply
  have hbelow (u : E) : ‖u‖ ≤ κ⁻¹ * ‖T u‖ := by
    have hh : κ * ‖u‖ ≤ ‖T u‖ := by
      by_cases hu : ‖u‖ = 0
      · rw [hu, mul_zero]
        exact norm_nonneg _
      · have hp : 0 < ‖u‖ := (norm_nonneg _).lt_of_ne (Ne.symm hu)
        apply (mul_le_mul_iff_left₀ hp).mp
        have he := (hb u).trans_eq (hT u u).symm
        have hn := real_inner_le_norm (T u) u
        nlinarith
    exact (le_inv_mul_iff₀ hκ).mpr hh
  have ha : AntilipschitzWith ⟨κ⁻¹, inv_nonneg.mpr hκ.le⟩ T :=
    ContinuousLinearMap.antilipschitz_of_bound T hbelow
  have hc : IsClosed (T.range : Set E) := ha.isClosed_range T.uniformContinuous
  let : CompleteSpace T.range := hc.completeSpace_coe
  have hrange : T.range = ⊤ := by
    rw [← T.range.orthogonal_orthogonal]
    rw [Submodule.eq_top_iff']
    intro v w hw
    have hw0 : w = 0 := by
      have he : B w w = 0 := (hT w w).symm.trans (hw _ ⟨w, rfl⟩)
      have hh := hb w
      rw [he] at hh
      have hs : ‖w‖ ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right hh hκ
      have hn : ‖w‖ = 0 := by nlinarith [norm_nonneg w]
      exact norm_eq_zero.mp hn
    rw [hw0, inner_zero_left]
  let y : E := (toDual ℝ E).symm ℓ
  have hy : y ∈ T.range := by rw [hrange]; trivial
  obtain ⟨u, hu⟩ := hy
  change T u = y at hu
  refine ⟨u, fun v => ?_⟩
  rw [← hT, hu]
  exact toDual_symm_apply

/-- The frozen Dirichlet correction exists in every positive dimension on a
bounded open domain, with the actual H¹₀ boundary relation. -/
theorem exists_campanato_frozen_solution {n : ℕ} (hn : 0 < n)
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (hbD : Bornology.IsBounded D)
    (A₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {lam : ℝ} (hlam : 0 < lam) (hell : ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A₀ ξ) ξ)
    (w : H1Space D) :
    ∃ h : H1Space D, h - w ∈ h1ZeroSubmodule hD ∧
      IsWeakDivergenceEquationOn (fun _ => A₀) h.gradientLp (fun _ => 0) D := by
  obtain ⟨C, hC, hp⟩ := H1ZeroSpace.poincare_bounded hn hD hbD
  let L := H1Space.gradientCLM.comp (h1ZeroSubmodule hD).subtypeL
  let M := A₀.compLpL 2 (volume.restrict D)
  let B : H1ZeroSpace hD →L[ℝ] H1ZeroSpace hD →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp (M.comp L) L
  let ℓ : H1ZeroSpace hD →L[ℝ] ℝ := -(innerSL ℝ (M w.gradientLp)).comp L
  let κ : ℝ := lam / (C + 1) ^ 2
  have hκ : 0 < κ := div_pos hlam (sq_pos_of_pos (by linarith))
  have hb (u : H1ZeroSpace hD) : κ * ‖u‖ ^ 2 ≤ B u u := by
    have hu : ‖u‖ ≤ (C + 1) * ‖u.val.gradientLp‖ := by
      have hs := u.val.norm_le_sum
      have ht := hp u
      change ‖u.val‖ ≤ _
      nlinarith
    have hs := mul_self_le_mul_self (norm_nonneg u) hu
    have hs' := mul_le_mul_of_nonneg_left hs hκ.le
    have he : κ * (C + 1) ^ 2 = lam := by
      dsimp [κ]
      field_simp
    have hec := campanato_coercive_compLp A₀ hell u.val.gradientLp
    change κ * ‖u‖ ^ 2 ≤ inner ℝ (A₀.compLp u.val.gradientLp) u.val.gradientLp
    nlinarith
  obtain ⟨u, hu⟩ := campanato_exists_coercive_bilinear_solution B hκ hb ℓ
  let h : H1Space D := w + u.val
  have hh (v : H1ZeroSpace hD) : inner ℝ (A₀.compLp h.gradientLp) v.val.gradientLp = 0 := by
    have he := hu v
    change inner ℝ (A₀.compLp u.val.gradientLp) v.val.gradientLp =
      -inner ℝ (A₀.compLp w.gradientLp) v.val.gradientLp at he
    change inner ℝ (M (w + u.val).gradientLp) v.val.gradientLp = 0
    rw [H1Space.gradientLp_add, map_add, inner_add_left]
    change inner ℝ (A₀.compLp w.gradientLp) v.val.gradientLp +
      inner ℝ (A₀.compLp u.val.gradientLp) v.val.gradientLp = 0
    linarith
  refine ⟨h, by simpa only [h, add_sub_cancel_left] using u.property, ?_⟩
  intro φ hφ hcφ hsφ
  have hφH : HasH1GradientOn φ (gradient φ) univ :=
    ⟨hasWeakGradientOn_of_contDiffOn isOpen_univ hφ.contDiffOn,
      hφ.continuous.memLp_of_hasCompactSupport hcφ,
      (continuous_gradient_of_contDiff hφ).memLp_of_hasCompactSupport
        (hcφ.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset _))⟩
  let v : H1ZeroSpace hD := ⟨H1Space.ofFunction φ (gradient φ)
    (hφH.mono (subset_univ D)), hφH.mem_h1Zero_of_compact_support hD hcφ hsφ⟩
  have hv := hh v
  rw [L2.inner_def] at hv
  have hi : (∫ x in D, inner ℝ (A₀ (h.gradientLp x)) (gradient φ x)) = 0 := by
    convert hv using 1
    apply integral_congr_ae
    filter_upwards [A₀.coeFn_compLp h.gradientLp,
      H1Space.gradientLp_ofFunction φ (gradient φ) (hφH.mono (subset_univ D))] with x hx hy
    rw [hx]
    exact congrArg (fun z => inner ℝ (A₀ (h.gradientLp x)) z) hy.symm
  simp only [sub_zero]
  rw [← hi]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [gradient_eq_zero_of_notMem_tsupport (fun ht => hx (hsφ ht)), inner_zero_right]

/-- Existence and the exact displayed squared-gradient comparison are obtained
together, in particular in both dimensions required by the blueprint. -/
theorem exists_campanato_comparison {n : ℕ} (hn : 0 < n)
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (hbD : Bornology.IsBounded D)
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (A₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (G₀ : EuclideanSpace ℝ (Fin n)) (w : H1Space D)
    (hA : AEStronglyMeasurable A (volume.restrict D))
    {cap lam : ℝ} (hbA : ∀ᵐ x ∂volume.restrict D, ‖A x‖ ≤ cap)
    (hG : MemLp G 2 (volume.restrict D)) (hlam : 0 < lam)
    (hell : ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A₀ ξ) ξ)
    (hw : IsWeakDivergenceEquationOn A w.gradientLp G D) :
    ∃ h : H1Space D, h - w ∈ h1ZeroSubmodule hD ∧
      IsWeakDivergenceEquationOn (fun _ => A₀) h.gradientLp (fun _ => 0) D ∧
      (∫ x in D, ‖w.gradientLp x - h.gradientLp x‖ ^ 2) ≤
        (2 / lam ^ 2) * (∫ x in D, ‖A x - A₀‖ ^ 2 * ‖w.gradientLp x‖ ^ 2) +
        (2 / lam ^ 2) * (∫ x in D, ‖G x - G₀‖ ^ 2) := by
  obtain ⟨h, hbd, hh⟩ := exists_campanato_frozen_solution hn hD hbD A₀ hlam hell w
  exact ⟨h, hbd, hh, campanato_comparison hD hbD.measure_lt_top A A₀ G G₀ w h
    hA hbA hG hlam hell hw hh hbd⟩

/-- The ball-centered frozen solution and comparison with `A(x₀)` and `G(x₀)`.
This applies to the restriction of any solution on a larger open domain. -/
theorem exists_campanato_comparison_ball {n : ℕ} (hn : 0 < n)
    (x₀ : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (w : H1Space (ball x₀ r))
    (hA : AEStronglyMeasurable A (volume.restrict (ball x₀ r)))
    {cap lam : ℝ} (hbA : ∀ᵐ x ∂volume.restrict (ball x₀ r), ‖A x‖ ≤ cap)
    (hG : MemLp G 2 (volume.restrict (ball x₀ r))) (hlam : 0 < lam)
    (hell : ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x₀ ξ) ξ)
    (hw : IsWeakDivergenceEquationOn A w.gradientLp G (ball x₀ r)) :
    ∃ h : H1Space (ball x₀ r), h - w ∈ h1ZeroSubmodule isOpen_ball ∧
      IsWeakDivergenceEquationOn (fun _ => A x₀) h.gradientLp (fun _ => 0) (ball x₀ r) ∧
      (∫ x in ball x₀ r, ‖w.gradientLp x - h.gradientLp x‖ ^ 2) ≤
        (2 / lam ^ 2) * (∫ x in ball x₀ r, ‖A x - A x₀‖ ^ 2 * ‖w.gradientLp x‖ ^ 2) +
        (2 / lam ^ 2) * (∫ x in ball x₀ r, ‖G x - G x₀‖ ^ 2) :=
  exists_campanato_comparison hn isOpen_ball isBounded_ball A (A x₀) G (G x₀) w
    hA hbA hG hlam hell hw

end LiquidDrop
