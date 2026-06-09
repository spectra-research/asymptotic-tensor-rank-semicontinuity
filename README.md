# Asymptotic tensor rank semicontinuity

A Lean 4 formalization of the paper
*"Asymptotic tensor rank is characterized by polynomials"* (Christandl, Hoeberechts,
Nieuwboer, Vrana, Zuiddam), [arXiv:2411.15789](https://arxiv.org/abs/2411.15789).

The main results are stated in
[`AsymptoticTensorRankSemicontinuity/Main.lean`](AsymptoticTensorRankSemicontinuity/Main.lean).

Docstrings cite the paper by theorem number and by `tex:LINE` references into
arXiv v2.

## Build

```
lake exe cache get
lake build
```

Pinned to Mathlib `v4.27.0` (Lean `v4.27.0`).

## Acknowledgements

This formalization was developed with the assistance of [lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp).
