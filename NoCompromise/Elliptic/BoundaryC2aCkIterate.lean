module

public import NoCompromise.Elliptic.BoundaryC2aCkLevel
public import NoCompromise.Elliptic.BoundaryNeumannCkIterate

@[expose] public section

/-!
# The step of the Dirichlet boundary higher-regularity iteration (`thm:boundary-C2a`)

We prove `BoundaryDirichletCkLevel k → BoundaryDirichletCkLevel (k + 1)`, and hence every
level from level `0`.

* For a tangential direction `i`, `∂ᵢu` solves the differentiated equation
  `div(A ∇∂ᵢu) = div(∂ᵢG - (∂ᵢA) ∇u)` on the half ball of radius `R`
  (`IsWeakDivergenceEquationOn.coordinate_derivative`), hence on the half ball of radius
  `R/2`, with the smooth boundary datum `∂ᵢφ`: at a face point `x` of the closed half ball of
  radius `R/2` the segment `x + t eᵢ`, `|t| < R/2`, stays on the face inside the closed half
  ball of radius `R`, where `u = φ`, so `∂ᵢ(u - φ)(x) = 0`. The datum `∂ᵢG - (∂ᵢA)∇u` and
  `∂ᵢu` are `C^{k+1,α}`, and level `k` at radius `R/2` makes `∂ᵢu` of class `C^{k+2,α}` on the
  half ball of radius `(3/8)(1/2)^{k+1} R`.
* The normal derivative `∂₃u` has partials `∂ₗ∂₃u = ∂₃∂ₗu` (`l` tangential) and `∂₃∂₃u`,
  which equals the `C^{k+1,α}` expression obtained by solving the classical equation
  (`IsWeakDivergenceEquationOn.pointwise_equation`) for it, using `A₃₃ ≥ lam > 0`. Hence all
  coordinate partials of `u` are `C^{k+2,α}` and `u` is `C^{k+3,α}`.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- A point of the open ball of radius `R` with nonnegative last coordinate lies in the
closure of the open half ball of radius `R`. -/
lemma boundaryC2aCkIterate_mem_closure {R : ℝ} {y : EuclideanSpace ℝ (Fin 3)}
    (hy : ‖y‖ < R) (hy2 : 0 ≤ y (Fin.last 2)) : y ∈ closure (boundaryHalfBall R) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  set t := min (R - ‖y‖) ε / 2 with ht_def
  have ht : 0 < t := by
    have : 0 < min (R - ‖y‖) ε := lt_min (by linarith) hε
    rw [ht_def]; linarith
  have htR : t < R - ‖y‖ := by
    have hh := min_le_left (R - ‖y‖) ε
    rw [ht_def]; linarith
  have htε : t < ε := by
    have hh := min_le_right (R - ‖y‖) ε
    rw [ht_def]; linarith
  have hnt : ‖EuclideanSpace.single (Fin.last 2) t‖ = t := by
    rw [PiLp.norm_single, Real.norm_eq_abs, abs_of_pos ht]
  refine ⟨y + EuclideanSpace.single (Fin.last 2) t, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_ball, dist_zero_right]
    calc ‖y + EuclideanSpace.single (Fin.last 2) t‖
        ≤ ‖y‖ + ‖EuclideanSpace.single (Fin.last 2) t‖ := norm_add_le _ _
      _ < R := by rw [hnt]; linarith
  · change 0 < (y + EuclideanSpace.single (Fin.last 2) t) (Fin.last 2)
    have h : (y + EuclideanSpace.single (Fin.last 2) t) (Fin.last 2) = y (Fin.last 2) + t := by
      simp
    rw [h]
    linarith
  · rw [dist_eq_norm, sub_add_cancel_left, norm_neg, hnt]
    exact htε

/-- The face condition for a tangential derivative: if `u = φ` on the face part of the closed
half ball of radius `R`, `u` is differentiable near the closed half ball of radius `R / 2` and
`φ` is differentiable, then `∂ᵢu = ∂ᵢφ` on the face part of the closed half ball of radius
`R / 2`, for every tangential direction `i`. -/
lemma boundaryC2aCkIterate_face {R : ℝ} (hR : 0 < R) {u φ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hface : ∀ x ∈ closure (boundaryHalfBall R), x (Fin.last 2) = 0 → u x = φ x)
    {i : Fin 3} (hi : i ≠ Fin.last 2) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ closure (boundaryHalfBall (R / 2))) (hx2 : x (Fin.last 2) = 0)
    (hu : DifferentiableAt ℝ u x) (hφ : DifferentiableAt ℝ φ x) :
    fderiv ℝ u x (EuclideanSpace.single i 1) = fderiv ℝ φ x (EuclideanSpace.single i 1) := by
  set e : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single i 1 with he
  have hxn : ‖x‖ ≤ R / 2 := by
    have h1 : closure (boundaryHalfBall (R / 2)) ⊆ closedBall 0 (R / 2) :=
      (closure_mono (fun _ hy => hy.1 : boundaryHalfBall (R / 2) ⊆ ball 0 (R / 2))).trans
        closure_ball_subset_closedBall
    simpa [mem_closedBall, dist_zero_right] using h1 hx
  have he1 : ‖e‖ = 1 := by simp [he]
  -- `u - φ` vanishes along the segment through `x` in direction `e`
  have hvan : (fun t : ℝ => u (x + t • e) - φ (x + t • e)) =ᶠ[𝓝 0] fun _ => 0 := by
    have hb : ball (0 : ℝ) (R / 2) ∈ 𝓝 (0 : ℝ) := ball_mem_nhds _ (by linarith)
    filter_upwards [hb] with t ht
    rw [mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
    have hlast : (x + t • e) (Fin.last 2) = 0 := by
      have hi' : (2 : Fin 3) ≠ i := fun h => hi (by rw [← h]; rfl)
      have hx2' : x (2 : Fin 3) = 0 := hx2
      simp [he, hi', hx2']
    have hnorm : ‖x + t • e‖ < R := by
      calc ‖x + t • e‖ ≤ ‖x‖ + ‖t • e‖ := norm_add_le _ _
        _ = ‖x‖ + |t| := by rw [norm_smul, he1, mul_one, Real.norm_eq_abs]
        _ < R := by linarith
    have hmem := boundaryC2aCkIterate_mem_closure hnorm hlast.ge
    rw [hface _ hmem hlast, sub_self]
  have hline : HasDerivAt (fun t : ℝ => u (x + t • e) - φ (x + t • e))
      (fderiv ℝ u x e - fderiv ℝ φ x e) 0 := by
    have hpath : HasDerivAt (fun t : ℝ => x + t • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
    have hu' : HasFDerivAt u (fderiv ℝ u x) (x + (0 : ℝ) • e) := by
      simpa using hu.hasFDerivAt
    have hφ' : HasFDerivAt φ (fderiv ℝ φ x) (x + (0 : ℝ) • e) := by
      simpa using hφ.hasFDerivAt
    exact (hu'.comp_hasDerivAt (0 : ℝ) hpath).sub (hφ'.comp_hasDerivAt (0 : ℝ) hpath)
  have h0 : HasDerivAt (fun _ : ℝ => (0 : ℝ)) (fderiv ℝ u x e - fderiv ℝ φ x e) 0 :=
    hline.congr_of_eventuallyEq hvan.symm
  have := h0.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  linarith

/-- The step of the Dirichlet boundary higher-regularity iteration: level `k` gives level
`k + 1`. -/
theorem boundaryDirichletCkLevel_succ (k : ℕ) (ih : BoundaryDirichletCkLevel k) :
    BoundaryDirichletCkLevel (k + 1) := by
  intro α lam cap R hα hα1 hlam hR hR1 U hU hUc A G u φ hA hφ hG hu hcap' hell hface he
  have hKc := boundaryNeumannCkIterate_isCompact_closure R
  have hKv : Convex ℝ (closure (boundaryHalfBall R)) := (convex_boundaryHalfBall R).closure
  have hKb := hKc.isBounded
  have hB := isOpen_boundaryHalfBall R
  have hBU : boundaryHalfBall R ⊆ U := subset_closure.trans hUc
  have hA2 : ContDiffOn ℝ 2 A U := hA.of_le (by simp : (2 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))
  have hG2 : ContDiffOn ℝ 2 G U := hG.contDiffOn.of_le (by norm_cast; omega)
  have hu2 : ContDiffOn ℝ 2 u U := hu.contDiffOn.of_le (by norm_cast; omega)
  have hAk : ∀ m : ℕ, HasCkHolderOn m α A U (closure (boundaryHalfBall R)) :=
    HasCkHolderOn.of_contDiffOn_smooth hα1.le hU hUc hKv hKc hA
  have hgrad : HasCkHolderOn (k + 1) α (gradient u) U (closure (boundaryHalfBall R)) :=
    ((((HasCkHolderOn.succ_iff hU).1 hu).2.2).clm_comp hU hUc
      (toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.toContinuousLinearEquiv.toContinuousLinearMap
      ).congr hU hUc fun x _ => rfl
  have hK2 : closure (boundaryHalfBall (R / 2)) ⊆ closure (boundaryHalfBall R) :=
    closure_mono (boundaryHalfBall_mono (by linarith))
  have hK2U := hK2.trans hUc
  have hfin : ∀ t : Fin 3, t = 0 ∨ t = 1 ∨ t = 2 := by decide
  have h0 : (0 : Fin 3) ≠ Fin.last 2 := by decide
  have h1 : (1 : Fin 3) ≠ Fin.last 2 := by decide
  -- the tangential derivatives are `C^{k+2,α}`
  have htan : ∀ i : Fin 3, i ≠ Fin.last 2 →
      HasCkHolderOn (k + 2) α (fun x => fderiv ℝ u x (EuclideanSpace.single i 1))
        (boundaryHalfBall (3 / 8 * (1 / 2) ^ (k + 1) * R))
        (boundaryHalfBall (3 / 8 * (1 / 2) ^ (k + 1) * R)) := by
    intro i hi
    have heqR := he.coordinate_derivative hB ((hA2.of_le (by norm_num)).mono hBU)
      ((hG2.of_le (by norm_num)).mono hBU) (hu2.mono hBU) i
    have heq : IsWeakDivergenceEquationOn A
        (gradient (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)))
        (fun x => fderiv ℝ G x (EuclideanSpace.single i 1) -
          fderiv ℝ A x (EuclideanSpace.single i 1) (gradient u x))
        (boundaryHalfBall (R / 2)) := fun ψ hψ hcψ hsψ =>
      heqR ψ hψ hcψ (hsψ.trans (boundaryHalfBall_mono (by linarith)))
    have hGi : HasCkHolderOn (k + 1) α (fun x => fderiv ℝ G x (EuclideanSpace.single i 1) -
          fderiv ℝ A x (EuclideanSpace.single i 1) (gradient u x)) U
        (closure (boundaryHalfBall R)) := by
      have h1 := hG.partial hU hUc (EuclideanSpace.single i 1)
      have h2 := (hAk (k + 2)).partial hU hUc (EuclideanSpace.single i 1)
      have h3 := h2.bilinear hα1.le hU hUc hKv hKb
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)))
        hgrad
      exact (h1.sub hU hUc h3).congr hU hUc fun x _ => rfl
    have hvi : HasCkHolderOn (k + 1) α (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) U
        (closure (boundaryHalfBall R)) := hu.partial hU hUc _
    have hφi : ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
      (contDiff_infty_iff_fderiv.1 hφ).2.clm_apply contDiff_const
    have hfacei : ∀ x ∈ closure (boundaryHalfBall (R / 2)), x (Fin.last 2) = 0 →
        fderiv ℝ u x (EuclideanSpace.single i 1) = fderiv ℝ φ x (EuclideanSpace.single i 1) :=
      fun x hx hx2 => boundaryC2aCkIterate_face hR hface hi hx hx2
        ((hu2.contDiffAt (hU.mem_nhds (hK2U hx))).differentiableAt two_ne_zero)
        (hφ.differentiable (by simp)).differentiableAt
    have h := ih hα hα1 hlam (half_pos hR) (by linarith) hU hK2U hA hφi
      (boundaryNeumannCkIterate_mono hGi subset_rfl hK2)
      (boundaryNeumannCkIterate_mono hvi subset_rfl hK2)
      (fun x hx => hcap' x (hK2 hx)) (fun x hx => hell x (hK2 hx)) hfacei heq
    have hρ : 3 / 8 * (1 / 2 : ℝ) ^ k * (R / 2) = 3 / 8 * (1 / 2) ^ (k + 1) * R := by ring
    rwa [hρ] at h
  -- the half ball `S` of the conclusion
  have hρR : 3 / 8 * (1 / 2 : ℝ) ^ (k + 1) * R ≤ R := by
    have : (1 / 2 : ℝ) ^ (k + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  set S := boundaryHalfBall (3 / 8 * (1 / 2 : ℝ) ^ (k + 1) * R) with hSdef
  have hS : IsOpen S := isOpen_boundaryHalfBall _
  have hSv : Convex ℝ S := convex_boundaryHalfBall _
  have hSb : Bornology.IsBounded S := boundaryNeumannCkIterate_isBounded _
  have hSR : S ⊆ boundaryHalfBall R := boundaryHalfBall_mono hρR
  have hSK : S ⊆ closure (boundaryHalfBall R) := hSR.trans subset_closure
  have hSU : S ⊆ U := hSK.trans hUc
  have hsymm : ∀ x ∈ S, ∀ i j : Fin 3,
      boundaryNeumannC2Entry u x i j = boundaryNeumannC2Entry u x j i :=
    fun x hx i j => boundaryNeumannCkIterate_entry_comm hU hu2 (hSU hx) i j
  -- the pieces of the classical equation are `C^{k+1,α}` on `S`
  have ha : ∀ i j : Fin 3,
      HasCkHolderOn (k + 1) α (fun x => A x (EuclideanSpace.single j 1) i) S S := fun i j =>
    boundaryNeumannCkIterate_mono
      (((hAk (k + 1)).clm_comp hU hUc (ContinuousLinearMap.apply ℝ
        (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace.single j 1))).clm_comp hU hUc
        (EuclideanSpace.proj i)) hSU hSK
  have hdA : ∀ i j : Fin 3, HasCkHolderOn (k + 1) α
      (fun x => fderiv ℝ A x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) i)
      S S := fun i j =>
    boundaryNeumannCkIterate_mono
      ((((hAk (k + 2)).partial hU hUc (EuclideanSpace.single i 1)).clm_comp hU hUc
        (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin 3))
          (EuclideanSpace.single j 1))).clm_comp hU hUc (EuclideanSpace.proj i)) hSU hSK
  have hdu : ∀ j : Fin 3,
      HasCkHolderOn (k + 1) α (fun x => fderiv ℝ u x (EuclideanSpace.single j 1)) S S :=
    fun j => boundaryNeumannCkIterate_mono (hu.partial hU hUc _) hSU hSK
  have hdG : ∀ i : Fin 3,
      HasCkHolderOn (k + 1) α (fun x => fderiv ℝ G x (EuclideanSpace.single i 1) i) S S :=
    fun i => boundaryNeumannCkIterate_mono
      ((hG.partial hU hUc (EuclideanSpace.single i 1)).clm_comp hU hUc
        (EuclideanSpace.proj i)) hSU hSK
  have hdivG : HasCkHolderOn (k + 1) α (divergenceN G) S S :=
    (((hdG 0).add hS subset_rfl (hdG 1)).add hS subset_rfl (hdG 2)).congr hS subset_rfl
      fun x _ => by simp only [divergenceN, Fin.sum_univ_three]
  have hE : ∀ i j : Fin 3, j ≠ Fin.last 2 →
      HasCkHolderOn (k + 1) α (fun x => boundaryNeumannC2Entry u x i j) S S :=
    fun i j hj => (htan j hj).partial hS subset_rfl (EuclideanSpace.single i 1)
  have hlow : ∀ x ∈ S, lam ≤ A x (EuclideanSpace.single 2 1) 2 := by
    intro x hx
    have h := hell x (hSK hx) (EuclideanSpace.single 2 1)
    simpa [EuclideanSpace.inner_single_right, PiLp.norm_single] using h
  -- the normal second derivative solved from the classical equation
  let T : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => ∑ i, ∑ j,
    fderiv ℝ A x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) i *
      fderiv ℝ u x (EuclideanSpace.single j 1)
  let R' : EuclideanSpace ℝ (Fin 3) → ℝ := fun x =>
    A x (EuclideanSpace.single 0 1) 0 * boundaryNeumannC2Entry u x 0 0 +
    A x (EuclideanSpace.single 1 1) 0 * boundaryNeumannC2Entry u x 0 1 +
    A x (EuclideanSpace.single 2 1) 0 * boundaryNeumannC2Entry u x 2 0 +
    A x (EuclideanSpace.single 0 1) 1 * boundaryNeumannC2Entry u x 1 0 +
    A x (EuclideanSpace.single 1 1) 1 * boundaryNeumannC2Entry u x 1 1 +
    A x (EuclideanSpace.single 2 1) 1 * boundaryNeumannC2Entry u x 2 1 +
    A x (EuclideanSpace.single 0 1) 2 * boundaryNeumannC2Entry u x 2 0 +
    A x (EuclideanSpace.single 1 1) 2 * boundaryNeumannC2Entry u x 2 1
  let Q : EuclideanSpace ℝ (Fin 3) → ℝ := fun x =>
    (divergenceN G x - T x - R' x) / A x (EuclideanSpace.single 2 1) 2
  have hTij : ∀ i j : Fin 3, HasCkHolderOn (k + 1) α
      (fun x => fderiv ℝ A x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) i *
        fderiv ℝ u x (EuclideanSpace.single j 1)) S S :=
    fun i j => (hdA i j).mul hα1.le hS subset_rfl hSv hSb (hdu j)
  have hTi : ∀ i : Fin 3, HasCkHolderOn (k + 1) α (fun x => ∑ j,
      fderiv ℝ A x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) i *
        fderiv ℝ u x (EuclideanSpace.single j 1)) S S := fun i =>
    (((hTij i 0).add hS subset_rfl (hTij i 1)).add hS subset_rfl (hTij i 2)).congr hS
      subset_rfl fun x _ => by simp only [Fin.sum_univ_three]
  have hT : HasCkHolderOn (k + 1) α T S S :=
    (((hTi 0).add hS subset_rfl (hTi 1)).add hS subset_rfl (hTi 2)).congr hS
      subset_rfl fun x _ => by simp only [T, Fin.sum_univ_three]
  have hm : ∀ i j l m : Fin 3, m ≠ Fin.last 2 → HasCkHolderOn (k + 1) α
      (fun x => A x (EuclideanSpace.single j 1) i * boundaryNeumannC2Entry u x l m) S S :=
    fun i j l m hm => (ha i j).mul hα1.le hS subset_rfl hSv hSb (hE l m hm)
  have hR' : HasCkHolderOn (k + 1) α R' S S := by
    have := ((((((((hm 0 0 0 0 h0).add hS subset_rfl (hm 0 1 0 1 h1)).add hS subset_rfl
      (hm 0 2 2 0 h0)).add hS subset_rfl (hm 1 0 1 0 h0)).add hS subset_rfl
      (hm 1 1 1 1 h1)).add hS subset_rfl (hm 1 2 2 1 h1)).add hS subset_rfl
      (hm 2 0 2 0 h0)).add hS subset_rfl (hm 2 1 2 1 h1))
    exact this
  have hinv : HasCkHolderOn (k + 1) α (fun x => (A x (EuclideanSpace.single 2 1) 2)⁻¹) S S :=
    (ha 2 2).inv hα1.le hS subset_rfl hSv hSb
      (fun x hx => (hlam.trans_le (hlow x hx)).ne')
      ⟨lam, hlam, fun x hx => (hlow x hx).trans (le_abs_self _)⟩
  have hQ : HasCkHolderOn (k + 1) α Q S S :=
    (((hdivG.sub hS subset_rfl hT).sub hS subset_rfl hR').mul hα1.le hS subset_rfl hSv hSb
      hinv).congr hS subset_rfl fun x _ => by simp only [Q, div_eq_mul_inv]
  have hQeq : ∀ x ∈ S, boundaryNeumannC2Entry u x 2 2 = Q x := by
    intro x hx
    have hx1 := hSR hx
    have heqn := he.pointwise_equation hB
      ((hA.of_le (by simp : (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))).mono hBU)
      ((hG2.of_le (by norm_num)).mono hBU) (hu2.mono hBU) x hx1
    have hpos : 0 < A x (EuclideanSpace.single 2 1) 2 := hlam.trans_le (hlow x hx)
    simp only [Fin.sum_univ_three] at heqn
    rw [hsymm x hx 0 2, hsymm x hx 1 2] at heqn
    simp only [Q, T, R']
    rw [eq_div_iff hpos.ne']
    simp only [Fin.sum_univ_three]
    linear_combination heqn
  -- the normal derivative is `C^{k+2,α}`
  have hN : HasCkHolderOn (k + 2) α (fun x => fderiv ℝ u x (EuclideanSpace.single 2 1)) S S := by
    refine hasCkHolderOn_succ_of_partials (k := k + 1) hS subset_rfl
      ((hdu 2).contDiffOn.differentiableOn (by exact_mod_cast Nat.succ_ne_zero k)) ?_
      fun l => ?_
    · obtain ⟨B, hB⟩ := (hdu 2).bounded 0 (Nat.zero_le _)
      refine ⟨B, fun x hx => ?_⟩
      have h := hB x hx
      rwa [norm_iteratedFDeriv_zero] at h
    · obtain rfl | rfl | rfl := hfin l
      · exact (hE 2 0 h0).congr hS subset_rfl fun y hy => hsymm y hy 0 2
      · exact (hE 2 1 h1).congr hS subset_rfl fun y hy => hsymm y hy 1 2
      · exact hQ.congr hS subset_rfl fun y hy => hQeq y hy
  -- all coordinate partials of `u` are `C^{k+2,α}`, so `u` is `C^{k+3,α}`
  have hub : ∃ B, ∀ x ∈ S, ‖u x‖ ≤ B := by
    obtain ⟨B, hB⟩ := hu.bounded 0 (Nat.zero_le _)
    refine ⟨B, fun x hx => ?_⟩
    have h := hB x (hSK hx)
    rwa [norm_iteratedFDeriv_zero] at h
  refine hasCkHolderOn_succ_of_partials (k := k + 2) hS subset_rfl
    ((hu2.mono hSU).differentiableOn two_ne_zero) hub fun i => ?_
  obtain rfl | rfl | rfl := hfin i
  · exact htan 0 h0
  · exact htan 1 h1
  · exact hN

/-- All levels of the flat Dirichlet boundary higher-regularity iteration from level `0`
(blueprint `thm:boundary-C2a`, iteration): if level `0` holds, then for every `k` a smooth
coefficient and boundary datum and a `C^{k+1,α}` datum and solution near the closed half ball
of radius `R ≤ 1` give a `C^{k+2,α}` solution on the half ball of radius `(3/8)(1/2)ᵏ R`. -/
theorem boundaryDirichletCkLevel_of_zero (h0 : BoundaryDirichletCkLevel 0) (k : ℕ) :
    BoundaryDirichletCkLevel k := by
  induction k with
  | zero => exact h0
  | succ k ih => exact boundaryDirichletCkLevel_succ k ih

end LiquidDrop
