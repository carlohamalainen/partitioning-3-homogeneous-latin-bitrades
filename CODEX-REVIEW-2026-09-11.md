# Codex review of *Partitioning 3-homogeneous latin bitrades*

Date: 11 September 2026

This review compares the proof in [`3hom.tex`](3hom.tex) with its Lean 4
formalization in this repository. It records both the initial proof audit and
the assessment after the main theorem had been checked end to end.

## Initial analysis: gaps exposed during formalization

The worked example was a natural first target. Lean could check directly that
the two arrays in Equation (2) form a bitrade, that the positive array is
3-homogeneous, and that the three displayed sets form the claimed transversal
partition. Those computations did not reveal an error in the example.

Extending the verification from that finite example to the universal theorem
exposed four proof obligations that were not adequately justified in the
paper.

### 1. Connectedness and transitivity are used without being assumed

Lemma 3.1 starts with an arbitrary 3-homogeneous bitrade, but its proof invokes
both (T1) and (T4), including transitivity
([`3hom.tex`, lines 585–608](3hom.tex#L585-L608)). Later, the proof says, “By
assumption,” that the cartographic group acts transitively on the positive
trade ([`3hom.tex`, lines 1066–1075](3hom.tex#L1066-L1075)). No such assumption
appears in Theorem 1.1.

This is a genuine scope gap. A disjoint union of two 3-homogeneous bitrades is
again 3-homogeneous, while its generated permutation action has at least two
orbits. Thus the geometric proof as written directly handles only a
transitive, or primary, component.

The required repair is to work componentwise. Each orbit of the generated
triangle-group action can be coloured independently, after which equally
coloured classes can be united across components. Lean implements precisely
this orbitwise construction in
[`ThreeColoring.lean`](Partitioning3Homogeneous/ThreeColoring.lean#L115-L204).

### 2. The orbit map `psi` is not shown to be well-defined

The paper fixes base points `t₀` and `x₀` and defines

```text
t psi = x₀ (δ theta), where t₀ δ = t.
```

To prove independence of the chosen `δ`, one needs

```text
theta(StabΓ(t₀)) ⊆ StabG(x₀).
```

Instead, after observing that `δ₁ δ₂⁻¹` fixes `t₀`, the paper simply
asserts that its image fixes `x₀`
([`3hom.tex`, lines 741–758](3hom.tex#L741-L758)). That assertion is the missing
stabilizer condition itself, so the argument is circular at this point. A
homomorphism between acting groups does not supply such an equivariant orbit
map automatically.

Lean isolates the exact condition as `MapsStabilizer` in
[`OrbitMap.lean`](Partitioning3Homogeneous/OrbitMap.lean#L24-L27) and proves the
corresponding descent theorem in
[`OrbitMap.lean`](Partitioning3Homogeneous/OrbitMap.lean#L84-L92). For the
bitrade application, fixed-point-freeness forces every dart stabilizer into
the translation subgroup, which supplies the required condition
([`ThreeColoring.lean`](Partitioning3Homogeneous/ThreeColoring.lean#L25-L94)).

### 3. Most of the geometric case analysis is only sketched

Case 1 contains distance calculations and several local configurations. Cases
2, 3, and 4 are described as “very similar”; the paper lists words in the
generators for their `a` and `b` subcases, but gives neither the corresponding
distance inequalities nor the finite contradictions required for their `c`
subcases ([`3hom.tex`, lines 1002–1040](3hom.tex#L1002-L1040)). Consequently,
the printed case analysis is not a complete proof of the disjointness lemma.

The Lean development avoids fragile Euclidean case splitting. It models the
orientation-preserving `(3,3,3)` triangle group as an integral triangular
lattice extended by a cyclic rotation. A single conjugacy theorem, proved by
integer arithmetic modulo three, shows that every affine rotation of the
relevant type is translation-conjugate to one of the three vertex rotations
([`TriangleGroup.lean`](Partitioning3Homogeneous/TriangleGroup.lean#L142-L165)).
This supplies all cases uniformly.

### 4. The last conversion from labels to transversals is informal

The closing argument explains geometrically why inconsistent labels should
produce a contradiction, but it does not explicitly prove that each colour
class contains exactly one entry in every row and column and has no repeated
symbol ([`3hom.tex`, lines 1078–1102](3hom.tex#L1078-L1102)). These conclusions
are plausible once the colouring is established, but the required existence,
uniqueness, disjointness, and coverage arguments are compressed into a few
sentences.

Lean makes these cardinality obligations explicit. It proves that a colour
class meets every coordinate fibre exactly once, constructs three pairwise
disjoint classes covering all darts, and transfers them back to finsets of
Latin-square entries in
[`TransversalPartition.lean`](Partitioning3Homogeneous/TransversalPartition.lean#L98-L446).

### Other formalization observations

- The paper uses right actions, whereas Lean composes functions from right to
  left. The reversed product order in Lean is therefore a convention change,
  not a mathematical error.
- The claim that the generator assignment extends to a triangle-group
  homomorphism is standard when the displayed presentation is accepted, but
  formalizing it still requires an explicit universal-property argument. The
  Lean proof supplies a concrete semidirect-product model and proves the
  necessary translation relations in
  [`TriangleRepresentation.lean`](Partitioning3Homogeneous/TriangleRepresentation.lean).
- The initial audit therefore suggested that the main result was likely
  correct, but that the published geometric proof required repairs before it
  could certify the theorem for arbitrary, possibly disconnected bitrades.

## Final assessment after Lean verification

The result fares well; the published proof has some real gaps. Lean confirms
the main theorem is true, but not quite by accepting every step as written.

The significant issues are:

- **Unjustified transitivity.** The paper starts with an arbitrary
  3-homogeneous bitrade but invokes (T4), transitivity, in Lemma 3.1
  ([`3hom.tex`](3hom.tex#L598)) and later says transitivity holds “by
  assumption” ([`3hom.tex`](3hom.tex#L1069)). It was never assumed; a disjoint
  union of bitrades is an immediate nontransitive example. Thus the printed
  proof directly covers only the primary/connected case. Lean repairs this by
  colouring each group-action orbit independently in
  [`ThreeColoring.lean`](Partitioning3Homogeneous/ThreeColoring.lean#L115).

- **The map `psi` is not proved well-defined.** At
  [`3hom.tex`](3hom.tex#L744), the proof assumes that if a group element fixes
  `t₀`, its image under `theta` fixes `x₀`. That is precisely the missing
  condition:

  ```text
  theta(Stab(t₀)) ⊆ Stab(x₀).
  ```

  The assertion at lines 748–750 is therefore circular. Lean isolates the
  correct hypothesis in
  [`OrbitMap.lean`](Partitioning3Homogeneous/OrbitMap.lean#L24) and proves the
  required stabilizer result from fixed-point-freeness in
  [`ThreeColoring.lean`](Partitioning3Homogeneous/ThreeColoring.lean#L52).

- **Cases 2–4 are only announced, not proved.** After treating Case 1, the
  paper merely lists the transformations for the remaining cases
  ([`3hom.tex`](3hom.tex#L1002)); the distance inequalities and finite `c`
  configurations are absent. Lean replaces the whole geometric case split
  with an integer-lattice theorem showing every relevant rotation is
  conjugate to one of the three vertex rotations
  ([`TriangleGroup.lean`](Partitioning3Homogeneous/TriangleGroup.lean#L142)).

- **The final transversal argument is compressed.** The discussion at
  [`3hom.tex`](3hom.tex#L1083) argues informally about consistent labels but
  does not explicitly establish the required exactly-one cardinalities for
  every row, column, and symbol. Lean proves these fibre cardinalities and the
  disjoint covering directly.

What survived unchanged:

- The worked bitrade, its homogeneity, permutations, and displayed
  transversals are all correct.
- The triangle-group idea is sound.
- The main theorem is true and is checked universally as
  [`LatinBitrade.theorem_1_1`](Partitioning3Homogeneous/MatePermutations.lean#L457-L479).
- The reversed product order in Lean is only the expected difference between
  the paper's right actions and Lean's function-composition convention.

Overall verdict: **correct theorem and strong underlying idea, but the proof
as printed is incomplete for arbitrary bitrades and contains one genuinely
invalid well-definedness argument.** The gaps are repairable—and Lean now
supplies those repairs—but they are more than cosmetic.

## Verification status

At the time of this review:

- `lake build` completed successfully for all 3,044 build jobs, without
  warnings;
- the project contained no `sorry`, `admit`, `native_decide`, or
  project-defined axioms; and
- `#print axioms LatinBitrade.theorem_1_1` reported only Lean's standard
  `propext`, `Classical.choice`, and `Quot.sound` axioms.

The formalization verifies the main theorem, the machinery needed for it, and
the paper's worked example. It is not a line-by-line encoding of every
topological or expository claim in the article; in particular, it replaces
the incomplete geometric case analysis with an algebraic proof of the needed
statement.
