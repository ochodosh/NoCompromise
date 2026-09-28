import NoCompromise.Elliptic.BoundaryNondivC2Trace
import NoCompromise.Elliptic.BoundaryNondivC2

/-!
# Nonzero trace: the zero-trace data for `z - φ`

For a nonzero trace, `thm:boundary-nondiv` subtracts a C² extension `φ` of the
boundary value. Given the original data for `z` (except the trace condition) and
such a `φ`, the difference `z - φ` satisfies the zero-trace closed data with the
right side `f - Lφ`, `Lφ` the classical nondivergence operator, and an explicit
norm bound. The ambient differentiability of `z` at points of the closed half ball
is an explicit hypothesis: the closed-data norms use the ambient `fderiv`.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- Hölder finiteness and the Hölder norm only depend on values on the set. -/
lemma HasFiniteHolderNormOn.congr_eqOn {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {α : ℝ} {f g : E → F} {U : Set E} (hf : HasFiniteHolderNormOn α f U)
    (h : EqOn g f U) :
    HasFiniteHolderNormOn α g U ∧ holderNorm α g U = holderNorm α f U := by
  have h1 : (fun x => ‖g x‖) '' U = (fun x => ‖f x‖) '' U :=
    Set.image_congr (fun x hx => by rw [h hx])
  have h2 : (fun p : E × E => ‖g p.1 - g p.2‖ / ‖p.1 - p.2‖ ^ α) '' (U ×ˢ U) =
      (fun p : E × E => ‖f p.1 - f p.2‖ / ‖p.1 - p.2‖ ^ α) '' (U ×ˢ U) :=
    Set.image_congr (fun p hp => by rw [h hp.1, h hp.2])
  refine ⟨⟨by rw [h1]; exact hf.uniform_bounded, by rw [h2]; exact hf.seminorm_bounded⟩, ?_⟩
  simp only [holderNorm, holderUniformNorm, holderSeminorm, h1, h2]

/-- Subtracting a C² extension of the trace produces zero-trace closed data. -/
theorem boundary_nondiv_closedData_sub_trace {α lam cap M : ℝ} (hα : 0 < α)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {z f φ : EuclideanSpace ℝ (Fin 3) → ℝ} {V : Set (EuclideanSpace ℝ (Fin 3))}
    (hV : IsOpen V) (hKV : closure (boundaryHalfBall 1) ⊆ V)
    (hA : HasC1HolderOn α A (closure (boundaryHalfBall 1)))
    (hb : HasFiniteHolderNormOn α b (closure (boundaryHalfBall 1)))
    (hz : HasC1HolderOn α z (closure (boundaryHalfBall 1)))
    (hf : HasFiniteHolderNormOn α f (closure (boundaryHalfBall 1)))
    (hAn : nondivC1HolderNorm α A (closure (boundaryHalfBall 1)) ≤ M)
    (hbn : holderNorm α b (closure (boundaryHalfBall 1)) ≤ M)
    (hcap : ∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap)
    (hell : ∀ x ∈ closure (boundaryHalfBall 1), ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v))
    (he : IsWeakNondivergenceEquationOn A b z f (boundaryHalfBall 1))
    (hzd : ∀ x ∈ closure (boundaryHalfBall 1), DifferentiableAt ℝ z x)
    (hφ2 : ContDiffOn ℝ 2 φ V)
    (hφ : HasC1HolderOn α φ (closure (boundaryHalfBall 1)))
    (hL : HasFiniteHolderNormOn α (nondivClassicalOperator A b φ) (closure (boundaryHalfBall 1)))
    (htrace : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 → z x = φ x) :
    BoundaryNondivClosedData α lam cap M
      (nondivC1HolderNorm α z (closure (boundaryHalfBall 1)) +
        nondivC1HolderNorm α φ (closure (boundaryHalfBall 1)) +
        holderNorm α f (closure (boundaryHalfBall 1)) +
        holderNorm α (nondivClassicalOperator A b φ) (closure (boundaryHalfBall 1)))
      A b (fun x => z x - φ x) (fun x => f x - nondivClassicalOperator A b φ x) := by
  set K := closure (boundaryHalfBall (1 : ℝ))
  have hU := isOpen_boundaryHalfBall (1 : ℝ)
  have hfd : EqOn (fderiv ℝ (fun x => z x - φ x)) (fun x => fderiv ℝ z x - fderiv ℝ φ x) K := by
    intro x hx
    have hφd : DifferentiableAt ℝ φ x :=
      (hφ2.contDiffAt (hV.mem_nhds (hKV hx))).differentiableAt (by norm_num)
    change fderiv ℝ (z - φ) x = _
    exact ((hzd x hx).hasFDerivAt.sub hφd.hasFDerivAt).fderiv
  obtain ⟨hv, hvb⟩ := nondiv_holder_sub hz.function_holder hφ.function_holder
  obtain ⟨hD, hDb⟩ := nondiv_holder_sub hz.derivative_holder hφ.derivative_holder
  obtain ⟨hD', hD'e⟩ := hD.congr_eqOn hfd
  obtain ⟨hs, hsb⟩ := nondiv_holder_sub hf hL
  have hAU : ContDiffOn ℝ 1 A (boundaryHalfBall 1) := hA.contDiff.mono subset_closure
  have hbU : ContinuousOn b (boundaryHalfBall 1) := (hb.nondiv_continuousOn hα).mono subset_closure
  have hφU : ContDiffOn ℝ 2 φ (boundaryHalfBall 1) := hφ2.mono (subset_closure.trans hKV)
  refine
    { coefficient := hA
      drift := hb
      solution := ⟨hz.contDiff.sub hφ.contDiff, hv, hD'⟩
      source := hs
      coefficient_norm := hAn
      drift_norm := hbn
      coefficient_bound := hcap
      elliptic := hell
      equation := IsWeakNondivergenceEquationOn.sub hU hAU hbU
        (hz.contDiff.mono subset_closure) (hφU.of_le (by norm_num))
        ((hf.nondiv_continuousOn hα).mono subset_closure)
        (continuousOn_nondivClassicalOperator hU hAU.continuousOn hbU hφU) he
        (isWeakNondivergenceEquationOn_of_contDiffOn hU hAU hbU hφU)
      trace_zero := fun x hx h0 => sub_eq_zero.mpr (htrace x hx h0)
      norm_bound := ?_ }
  change holderNorm α (fun x => z x - φ x) K + holderNorm α (fderiv ℝ (fun x => z x - φ x)) K +
    holderNorm α (fun x => f x - nondivClassicalOperator A b φ x) K ≤ _
  rw [hD'e]
  simp only [nondivC1HolderNorm]
  linarith

/-- Blueprint `thm:boundary-nondiv` for a nonzero trace, in the reduced form: after
subtracting a C² extension `φ` of the trace, `z - φ` has the C²,α conclusion of
`boundary_nondiv_c2_holder` on the fixed slab, with constant fixed by the displayed
bounds (including an upper bound `N` for the combined norms of `z`, `φ`, `f`, `Lφ`). -/
theorem boundary_nondiv_c2_holder_sub_trace {α lam cap M N : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hlamcap : lam ≤ cap)
    (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3))
      (b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (z f φ : EuclideanSpace ℝ (Fin 3) → ℝ) (V : Set (EuclideanSpace ℝ (Fin 3))),
      IsOpen V → closure (boundaryHalfBall 1) ⊆ V →
      HasC1HolderOn α A (closure (boundaryHalfBall 1)) →
      HasFiniteHolderNormOn α b (closure (boundaryHalfBall 1)) →
      HasC1HolderOn α z (closure (boundaryHalfBall 1)) →
      HasFiniteHolderNormOn α f (closure (boundaryHalfBall 1)) →
      nondivC1HolderNorm α A (closure (boundaryHalfBall 1)) ≤ M →
      holderNorm α b (closure (boundaryHalfBall 1)) ≤ M →
      (∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap) →
      (∀ x ∈ closure (boundaryHalfBall 1), ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      IsWeakNondivergenceEquationOn A b z f (boundaryHalfBall 1) →
      (∀ x ∈ closure (boundaryHalfBall 1), DifferentiableAt ℝ z x) →
      ContDiffOn ℝ 2 φ V →
      HasC1HolderOn α φ (closure (boundaryHalfBall 1)) →
      HasFiniteHolderNormOn α (nondivClassicalOperator A b φ) (closure (boundaryHalfBall 1)) →
      (∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 → z x = φ x) →
      nondivC1HolderNorm α z (closure (boundaryHalfBall 1)) +
          nondivC1HolderNorm α φ (closure (boundaryHalfBall 1)) +
          holderNorm α f (closure (boundaryHalfBall 1)) +
          holderNorm α (nondivClassicalOperator A b φ) (closure (boundaryHalfBall 1)) ≤ N →
      ContDiffOn ℝ 2 (fun x => z x - φ x) boundaryNondivC2Slab ∧
      ∀ i j : Fin 3,
        (∀ x ∈ boundaryNondivC2Slab,
          |boundaryNeumannC2Entry (fun x => z x - φ x) x i j| ≤ C) ∧
        ∀ x ∈ boundaryNondivC2Slab, ∀ y ∈ boundaryNondivC2Slab,
          |boundaryNeumannC2Entry (fun x => z x - φ x) x i j -
            boundaryNeumannC2Entry (fun x => z x - φ x) y i j| ≤ C * dist x y ^ α := by
  obtain ⟨C, hC, hreg⟩ := boundary_nondiv_c2_holder hα hα1 hlam hlamcap hM hN
  refine ⟨C, hC, ?_⟩
  intro A b z f φ V hV hKV hA hb hz hf hAn hbn hcap hell he hzd hφ2 hφ hL htrace hNb
  have d := boundary_nondiv_closedData_sub_trace hα hV hKV hA hb hz hf hAn hbn hcap hell he
    hzd hφ2 hφ hL htrace
  have d' : BoundaryNondivClosedData α lam cap M N A b (fun x => z x - φ x)
      (fun x => f x - nondivClassicalOperator A b φ x) :=
    { d with norm_bound := d.norm_bound.trans hNb }
  obtain ⟨h2, hent⟩ := hreg A b _ _ d'
  exact ⟨h2, fun i j => ⟨(hent i j).1, (hent i j).2.1⟩⟩


/-- Second coordinate derivatives are additive at points where both summands are C². -/
lemma boundaryNeumannC2Entry_add {u φ : EuclideanSpace ℝ (Fin 3) → ℝ}
    {W : Set (EuclideanSpace ℝ (Fin 3))} (hW : IsOpen W)
    (hu : ContDiffOn ℝ 2 u W) (hφ : ContDiffOn ℝ 2 φ W)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ W) (i j : Fin 3) :
    boundaryNeumannC2Entry (fun y => u y + φ y) x i j =
      boundaryNeumannC2Entry u x i j + boundaryNeumannC2Entry φ x i j := by
  have hDu : ContDiffOn ℝ 1 (fun y => fderiv ℝ u y (EuclideanSpace.single j 1)) W :=
    (hu.fderiv_of_isOpen hW (by norm_num)).clm_apply contDiffOn_const
  have hDφ : ContDiffOn ℝ 1 (fun y => fderiv ℝ φ y (EuclideanSpace.single j 1)) W :=
    (hφ.fderiv_of_isOpen hW (by norm_num)).clm_apply contDiffOn_const
  have hev : (fun y => fderiv ℝ (fun y => u y + φ y) y (EuclideanSpace.single j 1)) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ u y (EuclideanSpace.single j 1) +
        fderiv ℝ φ y (EuclideanSpace.single j 1)) := by
    filter_upwards [hW.mem_nhds hx] with y hy
    have hdu := (hu.contDiffAt (hW.mem_nhds hy)).differentiableAt (by norm_num)
    have hdφ := (hφ.contDiffAt (hW.mem_nhds hy)).differentiableAt (by norm_num)
    change fderiv ℝ (u + φ) y _ = _
    rw [(hdu.hasFDerivAt.add hdφ.hasFDerivAt).fderiv, add_apply]
  unfold boundaryNeumannC2Entry
  rw [hev.fderiv_eq]
  have hd1 := (hDu.contDiffAt (hW.mem_nhds hx)).differentiableAt one_ne_zero
  have hd2 := (hDφ.contDiffAt (hW.mem_nhds hx)).differentiableAt one_ne_zero
  change fderiv ℝ ((fun y => fderiv ℝ u y (EuclideanSpace.single j 1)) +
    (fun y => fderiv ℝ φ y (EuclideanSpace.single j 1))) x _ = _
  rw [(hd1.hasFDerivAt.add hd2.hasFDerivAt).fderiv, add_apply]

/-- Blueprint `thm:boundary-nondiv` with a nonzero trace, on the fixed slab: if the
trace extension `φ` has bounded α-Hölder second derivatives on the slab (bound `P`),
then `z` itself is C² there with every `∂ᵢ∂ⱼz` bounded and α-Hölder with constant
`C + P`, where `C` is fixed by `α, lam, cap, M, N` before the data. -/
theorem boundary_nondiv_c2_holder_trace {α lam cap M N : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hlamcap : lam ≤ cap)
    (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3))
      (b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (z f φ : EuclideanSpace ℝ (Fin 3) → ℝ) (V : Set (EuclideanSpace ℝ (Fin 3))) (P : ℝ),
      IsOpen V → closure (boundaryHalfBall 1) ⊆ V →
      HasC1HolderOn α A (closure (boundaryHalfBall 1)) →
      HasFiniteHolderNormOn α b (closure (boundaryHalfBall 1)) →
      HasC1HolderOn α z (closure (boundaryHalfBall 1)) →
      HasFiniteHolderNormOn α f (closure (boundaryHalfBall 1)) →
      nondivC1HolderNorm α A (closure (boundaryHalfBall 1)) ≤ M →
      holderNorm α b (closure (boundaryHalfBall 1)) ≤ M →
      (∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap) →
      (∀ x ∈ closure (boundaryHalfBall 1), ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      IsWeakNondivergenceEquationOn A b z f (boundaryHalfBall 1) →
      (∀ x ∈ closure (boundaryHalfBall 1), DifferentiableAt ℝ z x) →
      ContDiffOn ℝ 2 φ V →
      HasC1HolderOn α φ (closure (boundaryHalfBall 1)) →
      HasFiniteHolderNormOn α (nondivClassicalOperator A b φ) (closure (boundaryHalfBall 1)) →
      (∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 → z x = φ x) →
      nondivC1HolderNorm α z (closure (boundaryHalfBall 1)) +
          nondivC1HolderNorm α φ (closure (boundaryHalfBall 1)) +
          holderNorm α f (closure (boundaryHalfBall 1)) +
          holderNorm α (nondivClassicalOperator A b φ) (closure (boundaryHalfBall 1)) ≤ N →
      (∀ i j : Fin 3, (∀ x ∈ boundaryNondivC2Slab, |boundaryNeumannC2Entry φ x i j| ≤ P) ∧
        ∀ x ∈ boundaryNondivC2Slab, ∀ y ∈ boundaryNondivC2Slab,
          |boundaryNeumannC2Entry φ x i j - boundaryNeumannC2Entry φ y i j| ≤
            P * dist x y ^ α) →
      ContDiffOn ℝ 2 z boundaryNondivC2Slab ∧
      ∀ i j : Fin 3,
        (∀ x ∈ boundaryNondivC2Slab, |boundaryNeumannC2Entry z x i j| ≤ C + P) ∧
        ∀ x ∈ boundaryNondivC2Slab, ∀ y ∈ boundaryNondivC2Slab,
          |boundaryNeumannC2Entry z x i j - boundaryNeumannC2Entry z y i j| ≤
            (C + P) * dist x y ^ α := by
  obtain ⟨C, hC, hreg⟩ := boundary_nondiv_c2_holder_sub_trace hα hα1 hlam hlamcap hM hN
  refine ⟨C, hC, ?_⟩
  intro A b z f φ V P hV hKV hA hb hz hf hAn hbn hcap hell he hzd hφ2 hφ hL htrace hNb hP
  obtain ⟨h2, hent⟩ := hreg A b z f φ V hV hKV hA hb hz hf hAn hbn hcap hell he hzd hφ2 hφ hL
    htrace hNb
  have hSV : boundaryNondivC2Slab ⊆ V :=
    boundaryNondivC2Slab_subset.trans (subset_closure.trans hKV)
  have hφS : ContDiffOn ℝ 2 φ boundaryNondivC2Slab := hφ2.mono hSV
  have hzeq : z = fun y => (z y - φ y) + φ y := funext fun y => (sub_add_cancel _ _).symm
  have hadd (x) (hx : x ∈ boundaryNondivC2Slab) (i j : Fin 3) :
      boundaryNeumannC2Entry z x i j =
        boundaryNeumannC2Entry (fun x => z x - φ x) x i j + boundaryNeumannC2Entry φ x i j := by
    conv_lhs => rw [hzeq]
    exact boundaryNeumannC2Entry_add isOpen_boundaryNondivC2Slab h2 hφS hx i j
  refine ⟨?_, fun i j => ⟨?_, ?_⟩⟩
  · rw [hzeq]
    exact h2.add hφS
  · intro x hx
    rw [hadd x hx]
    exact (abs_add_le _ _).trans (add_le_add ((hent i j).1 x hx) ((hP i j).1 x hx))
  · intro x hx y hy
    rw [hadd x hx, hadd y hy, add_sub_add_comm, add_mul]
    exact (abs_add_le _ _).trans (add_le_add ((hent i j).2 x hx y hy) ((hP i j).2 x hx y hy))

end LiquidDrop
