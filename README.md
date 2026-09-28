# No compromise in the liquid drop model — Lean formalization

A Lean 4 / Mathlib formalization of the main results of

> Otis Chodosh and Matilde Gianocca, *No compromise in the liquid drop model*,
> [arXiv:2608.11517](https://arxiv.org/abs/2608.11517).

## Statement

[`Challenge.lean`](Challenge.lean) states the results using only Mathlib, in about 150 lines.
It is the file to read to see what is proved. For example:

```lean
theorem main (V : ℝ) (hV : 0 < V) :
    (V ≤ criticalVolume →
      ∀ Ω : Set AmbientSpace,
        IsFixedVolumeMinimizer V Ω ↔ IsBallUpToNull V Ω) ∧
    (criticalVolume < V →
      ¬ ∃ Ω : Set AmbientSpace, IsFixedVolumeMinimizer V Ω)
```

Here `criticalVolume` is `V_* = 5 (2 - 2^{2/3}) / (2^{2/3} - 1)`, and minimisers are taken for the
energy `𝓔(Ω) = P(Ω) + (1/2) ∫_Ω ∫_Ω |x - y|⁻¹ dx dy` among sets of volume `V` in `ℝ³`.

## Checking

```bash
lake exe cache get
lake build
```

`lake build` builds the library, the challenge and the solution. The proofs use only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

[`Solution.lean`](Solution.lean) proves the challenge theorems from the library, and
[`comparator.json`](comparator.json) configures
[comparator](https://github.com/leanprover/comparator) to check that the solution proves exactly
the challenge statements (comparator runs on Linux).

## Layout

- `Challenge.lean`, `Solution.lean`, `Solution/Defs.lean`, `comparator.json`: the statement and its check.
- `NoCompromise/`: the formalization (namespace `LiquidDrop`).
- `blueprint/`: the LaTeX blueprint the formalization follows, with a compiled PDF.
- `formalization.yaml`: metadata, including how the formalization was produced.

## License and citation

Apache 2.0 (see [`LICENSE`](LICENSE)). To cite this formalization, see
[`CITATION.cff`](CITATION.cff).
