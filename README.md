# Formal verification of *Partitioning 3-homogeneous latin bitrades*

This Lean 4 project formalizes claims from `arXiv-0710.0938v3/3hom.tex`, the arXiv source of the paper.

Lean now checks the paper's main result.  The formal statement is
`LatinBitrade.theorem_1_1` in
`Partitioning3Homogeneous/MatePermutations.lean`:

```lean
theorem theorem_1_1
    (positive negative : Finset (Entry Row Column Symbol))
    (hbit : IsBitrade positive negative)
    (hhom : IsKHomogeneous 3 positive) :
    ∃ T₀ T₁ T₂,
      IsThreeTransversalPartition positive T₀ T₁ T₂
```

Checked components include:

- the definitions of partial Latin square, bitrade, homogeneity, transversal,
  and a three-transversal partition;
- the two arrays in Equation (2) form a bitrade;
- its positive part is 3-homogeneous;
- the three transversals displayed below Figure 4 form the claimed partition.
- the three permutations printed after Equation (2) satisfy (T1)--(T4),
  are derived from the three `beta` maps in Equation (1), and include an
  explicit transitivity certificate.
- the abstract orbit-map argument behind Lemma 4.1, with its necessary
  stabilizer hypothesis and a proved free-action corollary;
- a concrete algebraic model of the Euclidean triangle group and the
  representation induced by any permutation triple satisfying (T1)--(T3);
- the componentwise three-colouring argument (so primarity/transitivity is
  not silently assumed);
- construction of the canonical `beta` mate bijections and `tau`
  permutations from an arbitrary bitrade;
- preservation, fixed-point-freeness, order three, and the product identity
  for those permutations; and
- transfer of the resulting colour classes back to three transversals of
  the original positive partial Latin square.

Run all checks with:

```sh
lake build
```

The project contains no `sorry`, `admit`, `native_decide`, or project-defined
axioms. `#print axioms LatinBitrade.theorem_1_1` reports only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`. It formalizes the main theorem
and the proof machinery needed for it, plus the paper's worked example. It does
not attempt to encode every expository or topological claim elsewhere in the
article.
