# SimisMonomial

This repository contains a result of the AI4M group at Peking University, obtained by
[Pharos](https://github.com/frenzymath/Pharos) with an internal model of Hy in two runs. In the first run the model was given the Méndez–Vaz
Pinto–Villarreal conjecture on Simis monomial ideals
([arXiv:2402.08833](https://arxiv.org/abs/2402.08833), Conjecture 5.7) and found a counterexample:
the ideals `I_{r,s} = (ac, bd, abz^r, cdz^s)` with `r ≠ s` satisfy the hypotheses of the conjecture
but are not a diagonal weighting of any squarefree ideal. In the second run we gave the model this
counterexample and let it explore further. It strengthened the hypotheses and proved a positive
result: the conclusion holds when, in addition, the supports of the generators of `I` and of its
radical coincide and contain no strong triangle; the conclusion also holds if, in addition, the
union of any two intersecting supports of the irreducible components of `I` contains at most one
other component support.

The `papers/` folder holds two versions of the work:

- [`papers/no-strong-triangle-original.pdf`](papers/no-strong-triangle-original.pdf), a research paper
  for the Méndez–Vaz Pinto–Villarreal conjecture, which mainly talks about a no-strong-triangle
  condition, is the original manuscript written by the internal model of Hy in the second run;
- [`papers/counterexamples-and-diagonal-representability.pdf`](papers/counterexamples-and-diagonal-representability.pdf),
  Counterexamples and some positive results under strengthened conditions for the MPV conjecture, is
  our reorganization of it, written to be easier for human readers. The Lean code in this repository
  formalizes this version.

## The formalization

The formalization was carried out autonomously by the same internal model of Hy, running in Claude
Code. Its only external knowledge base was [lean4-skills](https://github.com/cameronfreer/lean4-skills).
It worked from a single instruction in `/goal` mode: formalize this paper, following lean4 skills.

All results of the paper are proved without `sorry`, and every challenge theorem depends only on
the axioms `propext`, `Classical.choice` and `Quot.sound`. Lean `v4.33.1`, Mathlib `v4.33.1`.

## Where to look

The main results of [the reorganized paper](papers/counterexamples-and-diagonal-representability.pdf)
are the following; the theorem numbers refer to it. Their definitions are in
[`SimisFormal/Defs.lean`](SimisFormal/Defs.lean).

| Paper | Statement | Proof |
|---|---|---|
| Theorem 3.1, the counterexample (the most important result) | [`thm31_main`](Challenge.lean#L193), [`thm31_main_decomposition`](Challenge.lean#L197), [`thm31_main_root`](Challenge.lean#L201) | [`SimisFormal/Thm3_1.lean`](SimisFormal/Thm3_1.lean#L1578) |
| Theorem 4.1, the positive result (no strong triangle) | [`SimisFormal.thm41_full`](Challenge.lean#L333) | [`SimisFormal/Thm4_1.lean`](SimisFormal/Thm4_1.lean#L748) |
| Theorem 5.2, the criterion from component supports | [`thm52_of_paperHypotheses`](Challenge.lean#L415), [`thm52_arbitraryUnusedWeights`](Challenge.lean#L495) | [`SimisFormal/Thm5_2.lean`](SimisFormal/Thm5_2.lean#L1372) |

The statements of all the main theorems above have been checked by hand for semantic agreement with the paper.

The other results of the paper (Proposition 2.1, Remark 3.2, Corollary 3.3, Lemmas 4.2, 4.3,
5.1, Corollary 5.3, Section 6) are also in [`Challenge.lean`](Challenge.lean); the full list of 124
theorems is in [`comparator.json`](comparator.json).

## Checking the result with Lean comparator

Build the project and run the [Lean comparator](https://github.com/leanprover/comparator), which
needs `lean4export` and `landrun` (see its README):

```sh
lake build SimisFormal Challenge Solution
lake env <path-to-comparator> comparator.json
```

It checks that every theorem listed in `comparator.json` is proved in `Solution` with exactly the
statement in `Challenge.lean`, using only the axioms `propext`, `Classical.choice` and `Quot.sound`.
