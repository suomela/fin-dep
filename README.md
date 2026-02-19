# Finitely dependent distributions

## Results

This project proves the following tight thresholds for finitely dependent stationary processes on ℤ:

- **4-colorings:** there is a 1-dependent distribution, but no 0-dependent distribution.
- **3-colorings:** there is a 2-dependent distribution, but no 1-dependent distribution.
- **Weak 2-colorings:** there is a 3-dependent distribution, but no 2-dependent distribution.
- **Maximal independent sets:** there is a 6-dependent distribution, but no 5-dependent distribution.
- **Greedy 3-colorings:** there is a 6-dependent distribution, but no 5-dependent distribution.

The first two results are known from prior work (see [Holroyd and Liggett 2016](https://doi.org/10.1017/fmp.2016.7)), while the final three are, to the best of our knowledge, new.

## Observations

A simple local-factor reduction chain produces all tight upper bounds:

- k-dependent 3-coloring → (k+1)-dependent weak 2-coloring
- k-dependent weak 2-coloring → (k+3)-dependent greedy 3-coloring
- k-dependent greedy 3-coloring → k-dependent maximal independent set.

In particular, once you prove that **there is no 5-dependent maximal independent set**, the matching lower bounds for all of these follow.

One corollary is that **distributed quantum algorithms** that produce a maximal independent set on directed cycles require at least 3 full rounds; in particular, there is no 2-round quantum algorithm for this task.

## Human-readable proof

See [proof/main.pdf](proof/main.pdf) for a human-readable proof.

## Formalization in Lean 4

All listed threshold results have been formalized in Lean 4. These files serve as starting points for reading the formalized proofs:

- [FiniteDependence/API/Definitions.lean](FiniteDependence/API/Definitions.lean) — definitions.
- [FiniteDependence/API/MainTheorems.lean](FiniteDependence/API/MainTheorems.lean) — theorem statements.

To build everything, run:

```sh
lake exe cache get
lake build
```

## Notes

This project is close to 100% work produced by AI tools. The new lower-bound proof was discovered by LLMs, and the formalization work was also done by LLMs, with minimal human guidance. We used primarily [Codex](https://openai.com/codex/) with [GPT-5.2](https://openai.com/index/introducing-gpt-5-2/) and [GPT-5.3-Codex](https://openai.com/index/introducing-gpt-5-3-codex/) in [this Docker sandbox](https://github.com/suomela/cursor-sandbox), where the agent could interact with Lean, Python, solver libraries, and other computational tools.

As a byproduct of this project, there is now also a Lean 4 formalization of the finitely dependent distributions by Holroyd and Liggett.

## Contact information

Primary contact: [Jukka Suomela](https://jukkasuomela.fi)
