module

public import NoCompromise.Elliptic.SobolevChainLocal
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public section

/-!
# Explicit Sobolev derivative data and its L² norm

A witness consists of the function and its actual distributional derivative tree.
Its norm is the finite sum of the L² norms of these derivatives. No existence or
estimate is part of the norm definition.
-/

noncomputable section

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient

namespace LiquidDrop

/-- Actual weak derivative data through a specified finite order. -/
inductive SobolevDerivativeData {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) :
    ℕ → (EuclideanSpace ℝ (Fin n) → ℝ) → Type
  | zero {u} (hu : MemLp u 2 (volume.restrict U)) : SobolevDerivativeData U 0 u
  | succ {m u} (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (hG : HasH1GradientOn u G U)
      (d : ∀ i, SobolevDerivativeData U m (fun x => G x i)) :
      SobolevDerivativeData U (m + 1) u

/-- The sum norm of the finite derivative tree, including each vector gradient. -/
def SobolevDerivativeData.norm {n m : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (d : SobolevDerivativeData U m u) : ℝ :=
  match d with
  | .zero _ => lpNorm u 2 (volume.restrict U)
  | .succ G _ v => lpNorm u 2 (volume.restrict U) + lpNorm G 2 (volume.restrict U) +
      ∑ i, (v i).norm

lemma SobolevDerivativeData.norm_nonneg {n m : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (d : SobolevDerivativeData U m u) : 0 ≤ d.norm := by
  induction d with
  | zero hu => exact lpNorm_nonneg
  | succ G hG d ih =>
    exact add_nonneg (add_nonneg lpNorm_nonneg lpNorm_nonneg) (Finset.sum_nonneg fun i _ => ih i)

lemma SobolevDerivativeData.memLp {n m : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (d : SobolevDerivativeData U m u) : MemLp u 2 (volume.restrict U) := by
  cases d with
  | zero hu => exact hu
  | succ G hG d => exact hG.memLp_function

lemma SobolevDerivativeData.lpNorm_le {n m : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (d : SobolevDerivativeData U m u) : lpNorm u 2 (volume.restrict U) ≤ d.norm := by
  cases d with
  | zero hu => exact le_rfl
  | succ G hG d =>
    exact le_add_of_nonneg_right lpNorm_nonneg |>.trans
      (le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => (d i).norm_nonneg))

lemma SobolevDerivativeData.hasSobolevOrderOn {n m : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (d : SobolevDerivativeData U m u) : HasSobolevOrderOn m u U := by
  induction d with
  | zero hu => exact hu
  | succ G hG d ih => exact ⟨G, hG, ih⟩

/-- The derivative data exists exactly for the genuine weak Sobolev hierarchy. -/
theorem hasSobolevOrderOn_iff_nonempty_derivativeData {n m : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n) → ℝ} :
    HasSobolevOrderOn m u U ↔ Nonempty (SobolevDerivativeData U m u) := by
  constructor
  · intro h
    induction m generalizing u with
    | zero => exact ⟨.zero h⟩
    | succ m ih =>
      obtain ⟨G, hG, hd⟩ := h
      exact ⟨.succ G hG (fun i => Classical.choice (ih (hd i)))⟩
  · rintro ⟨d⟩
    exact d.hasSobolevOrderOn

/-- Restricting the domain restricts every genuine weak derivative in the tree. -/
def SobolevDerivativeData.mono {n m : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (d : SobolevDerivativeData U m u) (hVU : V ⊆ U) : SobolevDerivativeData V m u :=
  match d with
  | .zero hu => .zero (hu.mono_measure (Measure.restrict_mono hVU le_rfl))
  | .succ G hG v => .succ G (hG.mono hVU) (fun i => (v i).mono hVU)

lemma SobolevDerivativeData.norm_mono {n m : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (d : SobolevDerivativeData U m u) (hVU : V ⊆ U) : (d.mono hVU).norm ≤ d.norm := by
  induction d with
  | zero hu => exact poisson_lpNorm_mono_measure hu (Measure.restrict_mono hVU le_rfl)
  | succ G hG v ih =>
    exact add_le_add (add_le_add
      (poisson_lpNorm_mono_measure hG.memLp_function (Measure.restrict_mono hVU le_rfl))
      (poisson_lpNorm_mono_measure hG.memLp_gradient (Measure.restrict_mono hVU le_rfl)))
      (Finset.sum_le_sum fun i _ => ih i)

/-- The first genuine vector gradient stored in positive-order derivative data. -/
def SobolevDerivativeData.gradient {n m : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (d : SobolevDerivativeData U (m + 1) u) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  match d with
  | .succ G _ _ => G

lemma SobolevDerivativeData.hasH1GradientOn {n m : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (d : SobolevDerivativeData U (m + 1) u) : HasH1GradientOn u d.gradient U := by
  cases d with
  | succ G hG v => exact hG

/-- The derivative tree rooted at one coordinate of the first gradient. -/
def SobolevDerivativeData.tail {n m : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (d : SobolevDerivativeData U (m + 1) u) (i : Fin n) :
    SobolevDerivativeData U m (fun x => d.gradient x i) :=
  match d with
  | .succ _ _ v => v i

lemma SobolevDerivativeData.norm_eq {n m : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (d : SobolevDerivativeData U (m + 1) u) :
    d.norm = lpNorm u 2 (volume.restrict U) +
      lpNorm d.gradient 2 (volume.restrict U) + ∑ i, (d.tail i).norm := by
  cases d
  rfl

lemma SobolevDerivativeData.gradient_lpNorm_le {n m : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (d : SobolevDerivativeData U (m + 1) u) :
    lpNorm d.gradient 2 (volume.restrict U) ≤ d.norm := by
  rw [d.norm_eq]
  exact le_add_of_nonneg_left lpNorm_nonneg |>.trans
    (le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => (d.tail i).norm_nonneg))

lemma SobolevDerivativeData.sum_tail_norm_le {n m : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (d : SobolevDerivativeData U (m + 1) u) : ∑ i, (d.tail i).norm ≤ d.norm := by
  rw [d.norm_eq]
  exact le_add_of_nonneg_left (add_nonneg lpNorm_nonneg lpNorm_nonneg)

lemma SobolevDerivativeData.hasH2DerivativesOn {n m : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (d : SobolevDerivativeData U (m + 2) u) :
    HasH2DerivativesOn u d.gradient (fun i => (d.tail i).gradient) U :=
  ⟨d.hasH1GradientOn, fun i => (d.tail i).hasH1GradientOn⟩

/-- The L² size of the distributional Laplacian is controlled by the explicit derivative norm. -/
lemma SobolevDerivativeData.lpNorm_add_trace_le {n m : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (d : SobolevDerivativeData U (m + 2) u) :
    lpNorm u 2 (volume.restrict U) +
      lpNorm (fun x => ∑ i, (d.tail i).gradient x i) 2 (volume.restrict U) ≤ d.norm := by
  have hb := d.hasH2DerivativesOn.lpNorm_trace_le
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (d.tail i).gradient_lpNorm_le)
  rw [d.norm_eq]
  have hp : 0 ≤ lpNorm d.gradient 2 (volume.restrict U) := lpNorm_nonneg
  linarith

/-- Lowering the order discards derivative terms and does not increase the norm. -/
theorem SobolevDerivativeData.exists_lower {n m j : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (d : SobolevDerivativeData U m u) (hjm : j ≤ m) :
    ∃ e : SobolevDerivativeData U j u, e.norm ≤ d.norm := by
  induction j generalizing m u with
  | zero => exact ⟨.zero d.memLp, d.lpNorm_le⟩
  | succ j ih =>
    cases m with
    | zero => omega
    | succ m =>
      choose e he using fun i => ih (d.tail i) (Nat.le_of_succ_le_succ hjm)
      refine ⟨.succ d.gradient d.hasH1GradientOn e, ?_⟩
      rw [d.norm_eq]
      exact add_le_add le_rfl (Finset.sum_le_sum fun i _ => he i)

/-- On open domains the sum norm is independent of all choices of weak representatives. -/
theorem SobolevDerivativeData.norm_congr_ae {n m : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {u v : EuclideanSpace ℝ (Fin n) → ℝ}
    (d : SobolevDerivativeData U m u) (e : SobolevDerivativeData U m v)
    (heq : u =ᵐ[volume.restrict U] v) : d.norm = e.norm := by
  induction m generalizing u v with
  | zero =>
    cases d with
    | zero hd =>
      cases e with
      | zero he =>
        change lpNorm u 2 (volume.restrict U) = lpNorm v 2 (volume.restrict U)
        rw [← toReal_eLpNorm,
          ← toReal_eLpNorm, eLpNorm_congr_ae heq]
  | succ m ih =>
    have hg : d.gradient =ᵐ[volume.restrict U] e.gradient :=
      (d.hasH1GradientOn.toHasWeakGradientOn.congr_ae heq EventuallyEq.rfl).unique hU
        e.hasH1GradientOn.toHasWeakGradientOn
    rw [d.norm_eq, e.norm_eq]
    have huEq : lpNorm u 2 (volume.restrict U) = lpNorm v 2 (volume.restrict U) :=
      by rw [← toReal_eLpNorm,
        ← toReal_eLpNorm, eLpNorm_congr_ae heq]
    have hgEq : lpNorm d.gradient 2 (volume.restrict U) =
        lpNorm e.gradient 2 (volume.restrict U) :=
      by rw [← toReal_eLpNorm,
        ← toReal_eLpNorm,
        eLpNorm_congr_ae hg]
    rw [huEq, hgEq]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact ih (d.tail i) (e.tail i) (hg.mono fun x hx => congrArg (fun y => y i) hx)

end LiquidDrop
