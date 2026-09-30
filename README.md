# No compromise in the liquid drop model — Lean formalization

A Lean 4 / Mathlib (auto)formalization of the main results of

> Otis Chodosh and Matilde Gianocca, *No compromise in the liquid drop model*,
> [arXiv:2608.11517](https://arxiv.org/abs/2608.11517).

## Statement

[`Challenge.lean`](Challenge.lean) states the results using only Mathlib, in about 180 lines.
It is the file to read to see what is proved. It ends with sanity checks on the definitions: the
perimeter and Coulomb energy of a ball, `3.51 < V_* < 3.52`, and existence of minimisers for
`0 < V ≤ V_*`. The main theorem reads:

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

## Differences from the paper

- The theorems are stated for volume `V > 0`, and uniqueness means agreeing with a ball of
  volume `V` up to a null set.
- The main theorem is proved for Borel sets (`main`) and for Lebesgue-measurable sets
  (`main_lebesgue`).
- `main_binding` also proves that every optimiser of Corollary 1.2 is a ball of volume `5/2` up
  to a null set.
- The proof follows the blueprint in `blueprint/`, written by AI agents from the paper. Only the
  statements were checked against the paper; the formal proof may differ from the paper's
  argument.

See `fidelity` in [`formalization.yaml`](formalization.yaml) for the full list.

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
the challenge statements (comparator runs on Linux). The `Palomar preflight` workflow runs the
same check through Palomar's own verification job.

## Layout

- `Challenge.lean`, `Solution.lean`, `Solution/Defs.lean`, `comparator.json`: the statement and its check.
- `NoCompromise/`: the formalization, about 216,000 lines of Lean in 1,206 files
  (namespace `LiquidDrop`).
- `blueprint/`: the LaTeX blueprint the formalization follows, with a compiled PDF.
- `formalization.yaml`: metadata, including how the formalization was produced.

## License and citation

Apache 2.0 (see [`LICENSE`](LICENSE)). To cite this formalization, see
[`CITATION.cff`](CITATION.cff).
