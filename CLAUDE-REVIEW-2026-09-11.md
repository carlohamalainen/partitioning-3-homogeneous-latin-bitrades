# Review of the Lean formalisation of *Partitioning 3-homogeneous latin bitrades*

| | |
|---|---|
| **Date** | 2026-09-11 |
| **Reviewer** | Claude (Fable 5.1), run through Claude Code at the request of the paper's author |
| **Revision reviewed** | commit `32775a9` ("codex attempt"), working tree clean |
| **Paper** | `3hom.tex`, C. Hämäläinen, *Partitioning 3-homogeneous latin bitrades* (arXiv:0710.0938) |
| **Toolchain** | Lean `v4.34.0-rc2`, Mathlib `v4.34.0-rc2` (rev `85e3a25e`) |
| **Formalisation author** | another LLM; this review is independent of it |

## 1. Verdict

The formalisation is **correct, complete for Theorem 1.1, and faithful to the
paper's definitions**.

- `lake build` succeeds and every module recompiles standalone with zero
  warnings.
- There is no `sorry`, `admit`, `native_decide`, `unsafe`, `implemented_by`,
  or project-declared `axiom`.
- `#print axioms LatinBitrade.theorem_1_1` reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- I read every proof, re-derived the group-theoretic identities by hand, checked
  the transcription of Example 2.6 against the TeX, and ran additional
  positive and negative tests (Appendix A).

The proof is the paper's argument in algebraic form. The geometric objects of
Sections 3 and 4 (hypermaps, the torus, the tessellation, the map ψ, the
Euclidean distance descent) are not formalised; an integer-lattice model of the
(3,3,3) triangle group plays their role. The README states this honestly.

The formalisation also surfaces three points about the paper itself
(Section 6): an unjustified step in the proof of Lemma 4.1, an unstated use of
transitivity (T4) in Lemma 3.5 and Corollary 4.5, and the fact that condition
(T2) is never needed.

## 2. The formal statement

```lean
theorem theorem_1_1
    {Row Column Symbol : Type*}
    [Fintype Row] [Fintype Column] [Fintype Symbol]
    [DecidableEq Row] [DecidableEq Column] [DecidableEq Symbol]
    (positive negative : Finset (Entry Row Column Symbol))
    (hbit : IsBitrade positive negative)
    (hhom : IsKHomogeneous 3 positive) :
    ∃ T₀ T₁ T₂, IsThreeTransversalPartition positive T₀ T₁ T₂
```

The conclusion unfolds to: each `Tᵢ` is a subset of `positive`, meets every row
exactly once, meets every column exactly once, and has pairwise distinct
symbols; the three sets are pairwise disjoint; their union is `positive`. This
is the full content of "T◇ can be partitioned into three transversals". No
hypothesis beyond Definition 2.1 and 3-homogeneity is present, and there is no
implicit assumption of primarity.

## 3. File-by-file

### `Basic.lean` (definitions, Section 2 of the paper)

- `Entry` is a row/column/symbol triple; `entryEquiv` identifies it with a
  product so that `Fintype` and `DecidableEq` are available.
- `IsPartialLatin T`: every entry of `T` is the unique entry of `T` agreeing
  with it in each of the three coordinate pairs. This is exactly "at most one
  symbol per cell, each symbol at most once per row and per column".
- `HasUniqueMates source target`: for every entry of `source` and each of the
  three coordinate pairs, exactly one entry of `target` agrees in that pair.
  This is (R2) when applied as `positive negative` and (R3) as
  `negative positive`.
- `IsBitrade`: both arrays partial Latin, disjoint (R1), and unique mates in
  both directions. Matches Definition 2.1.
- `IsKHomogeneous k T`: every row, every column, and every symbol of the
  ambient finite types occurs exactly `k` times in `T`. See Section 7 for the
  "no empty rows" convention this implies.
- `IsTransversal T X`: `X ⊆ T`, each row and each column met exactly once,
  and the image under `symbol` has the same cardinality as `X`. This matches
  the paper's definition verbatim, including the symbol-count form.
- `IsThreeTransversalPartition`: three transversals, pairwise disjoint,
  covering `T`.

### `MatePermutations.lean` (β maps and τ permutations, Equation (1))

- `chooseOfCardOne`, `mateBy`, `mateEquivBy`: from a relation with a unique
  mate in both directions, build an `Equiv` between the two dart subtypes.
  The `hsymmetric` argument is needed to run the uniqueness clause backwards;
  it is supplied for all three coordinate relations.
- `beta₁ beta₂ beta₃ : Darts negative ≃ Darts positive` are the paper's
  β₁, β₂, β₃ (change row / column / symbol, fix the other two). The direction
  T⊗ → T◇ matches the paper.
- `tauRow = beta₂.symm.trans beta₃`, i.e. apply β₂⁻¹ then β₃. With the
  paper's right-action convention this is τ₁ = β₂⁻¹β₃. Likewise
  `tauColumn` = τ₂ and `tauSymbol` = τ₃.
- `tau_product : tauSymbol * tauColumn * tauRow = 1`. Lean composes
  permutations right to left, so this is τ₃(τ₂(τ₁ x)) = x, which is the
  paper's x τ₁ τ₂ τ₃ = x. Correct and documented in the source.
- `tauRow_fixedPointFree` and siblings: a fixed point would force an entry of
  `negative` to equal an entry of `positive`, contradicting (R1). This is the
  standard proof of (T3).
- `perm_pow_three_of_fiber_card_three`: a fixed-point-free permutation that
  preserves a coordinate whose fibres have size three has order three. The
  proof first rules out a 2-cycle inside a 3-fibre, then shows the 3-cycle
  exhausts the fibre. Correct.
- `theorem_1_1` assembles the certificate and hands it to
  `exists_three_transversal_partition_from_permutations`.

### `TriangleGroup.lean` (integral model of the (3,3,3) group, Section 4)

The model is `Translation ⋊[rotationAction] Rotation` with
`Translation = Multiplicative (ℤ × ℤ)` and `Rotation = Multiplicative (ZMod 3)`.
I checked that it is the Euclidean (3,3,3) triangle group:

- `rotate (m, n) = (-n, m - n)` is multiplication by the primitive cube root
  of unity ω on ℤ[ω] in the basis (1, ω), since
  ω(m + nω) = mω + n(-1 - ω) = -n + (m - n)ω. It has order three
  (`rotate_three`).
- With Mathlib's semidirect product convention, the element (t, k) is the
  affine map z ↦ ωᵏz + t and the group law is composition.
- `rho₁ = (0, 1)` is z ↦ ωz, the rotation about 0.
  `rho₂ = affineRotation 1 0` is z ↦ ωz + 1, centre 1/(1-ω) = (2+ω)/3.
  `rho₃ = affineRotation 1 1` is z ↦ ωz + 1 + ω, centre (1+2ω)/3.
  The three centres form an equilateral triangle, and the translation lattice
  ℤ[ω] has index three in the vertex lattice, as it must for the (3,3,3)
  tessellation. All three are anticlockwise rotations by 2π/3.
- `rho_relations` (checked by `decide`): ρᵢ³ = 1 and ρ₁ρ₂ρ₃ = 1. These are the
  relations of Equation (3).
- `conjugate_rotation_one`: conjugating `affineRotation m n` by
  `translation p q` gives `affineRotation (m+p+q) (n+2q-p)`. I verified the
  formula from the semidirect product law. The quantity m + n mod 3 is
  invariant, and ρ₁, ρ₂, ρ₃ have m + n = 0, 1, 2.
- `rotation_one_conjugate_generator`: every element with rotational
  component one is translation-conjugate to ρ₁, ρ₂, or ρ₃. The proof splits
  on (m + n) mod 3 and closes with `omega`. This lemma is the algebraic
  replacement for Cases 1 to 4 in the proof of Lemma 4.3.

### `TriangleRepresentation.lean` (any (T1)-plus-order-three triple is a representation)

Given `a b c` in a group with a³ = b³ = c³ = 1 and abc = 1, the file builds a
homomorphism from the concrete model sending ρ₁, ρ₂, ρ₃ to a, b, c. This is the
non-trivial direction: it shows the concrete model is a quotient of the
abstract von Dyck group ⟨ρ₁,ρ₂,ρ₃ | ρᵢ³, ρ₁ρ₂ρ₃⟩, and together with
`rho_relations` that the two groups coincide. I re-derived the identities:

- Put u = ba⁻¹ and v = aua⁻¹. Then b = ua and
  b³ = (ua)³ = u · (aua⁻¹) · (a²ua⁻²) · a³ = u v (ava⁻¹) a³, so b³ = a³ = 1
  gives ava⁻¹ = (uv)⁻¹ (`conjugate_secondTranslation`). This says conjugation
  by a sends the lattice vector (0,1) to (-1,-1), which is `rotate (0,1)`.
- Using a⁻¹ = a² and b⁻¹ = b², c = (ab)⁻¹ = b²a² = uva. Then c³ = 1 and a³ = 1
  yield the commutator [u, v] = 1
  (`generator_relations_force_translations_commute`).
- `translationHom_rotate_one` checks
  u^(-n) v^(m-n) = a (uᵐ vⁿ) a⁻¹, which is the compatibility hypothesis of
  `SemidirectProduct.lift`.
- `triangleRepresentation_rho₁/₂/₃` confirm ρ₁ ↦ a, ρ₂ ↦ ua = b,
  ρ₃ ↦ uva = c.

### `OrbitMap.lean` (the abstract orbit-map lemma)

`exists_equivariant`: given θ : Γ →* G, a transitive Γ-set with base point
x₀, and a G-set with base point y₀, the map γ·x₀ ↦ θ(γ)·y₀ is well defined and
equivariant **provided the stabiliser of x₀ maps into the stabiliser of y₀**
(`MapsStabilizer`). The proof is correct. `exists_equivariant_of_free`
derives the hypothesis when Γ acts freely at x₀. This is the hypothesis the
paper's Lemma 4.1 needs and does not state; see Section 6. Note that only
`exists_equivariant` is used by the main proof, and it is used in the
opposite direction to the paper's ψ: from the dart set to `ZMod 3`, not from
triangles to darts.

### `ThreeColoring.lean` (the geometric step, algebraically)

This is the heart of the formalisation.

- `rotation_one_not_in_stabilizer`: if g has rotational component one and
  fixes x, conjugate g by a translation to some ρᵢ; then ρᵢ fixes the
  translated point, contradicting fixed-point-freeness.
- `stabilizer_has_trivial_rotation`: the case of rotational component two is
  reduced to the previous lemma via g⁻¹. Hence every point stabiliser lies in
  the translation subgroup.
- `exists_three_coloring_of_transitive`: on one orbit, apply
  `exists_equivariant` with θ = the projection to `Rotation` and target base
  point 1. The resulting `psi` satisfies `psi (g • x) = g.right * psi x`, so
  `color := toAdd ∘ psi` is advanced by one under each ρᵢ (all three have
  rotational component one).
- `exists_three_coloring`: the same on every orbit of
  `MulAction.orbitRel.Quotient`, glued with a dependent `if`. This is why
  primarity (T4) is not needed anywhere.
- `permutations_admit_three_coloring`: the permutation-level statement. Its
  hypotheses are cubes equal to one, product equal to one, and
  fixed-point-freeness. Condition (T2) does not appear.

### `TransversalPartition.lean` (colour classes are transversals)

- `cyclesFibers_of_card_three`: for a fixed-point-free order-three
  permutation preserving a coordinate with size-three fibres, the fibre of x
  is exactly {x, τx, τ²x}.
- `color_class_fiber_card`: because the colouring advances by one along the
  cycle, each colour class meets each fibre in exactly one point.
- `three_homogeneous_permutation_partition`: the three colour classes are
  coordinate transversals, pairwise disjoint, and cover the dart type. The
  argument to `permutations_admit_three_coloring` is
  `(tauSymbol, tauColumn, tauRow)` so that the product hypothesis has the
  right order.
- `forgetDarts_*` and `coordinatePartition_isThreeTransversalPartition`
  transfer from the dart subtype back to `Finset (Entry …)`, including the
  symbol-count form of the transversal condition via injectivity of `symbol`
  on each class.
- `homogeneous_three_dart_cards` converts `IsKHomogeneous 3` to fibre
  cardinalities on the dart subtype.

### `PaperExample.lean` and `TauExample.lean` (Example 2.6)

I checked the transcription against `3hom.tex` entry by entry.

- Equation (2), T◇ (rows 1 to 4): {111, 123, 142}, {213, 222, 234},
  {324, 333, 341}, {412, 431, 444}. T⊗: {113, 122, 141}, {212, 224, 233},
  {323, 331, 344}, {411, 434, 442}. Both match the TeX.
- The three transversals displayed after Lemma 3.5 match.
- `equation2_is_bitrade`, `equation2_is_three_homogeneous`, and
  `displayed_partition_is_valid` are decided by the kernel (`decide`, not
  `native_decide`).
- `TauExample.lean` indexes the twelve darts as
  0:111 1:123 2:142 3:213 4:222 5:234 6:324 7:333 8:341 9:412 10:431 11:444.
  I traced the tables `tau₁`, `tau₂`, `tau₃` against the printed cycles
  (111,142,123)(213,234,222)(324,341,333)(412,444,431),
  (111,213,412)(123,222,324)(234,333,431)(142,341,444), and
  (111,431,341)(123,333,213)(142,412,222)(234,444,324). All twelve images of
  each table agree.
- `beta_coordinate_conditions` verifies the β tables satisfy the defining
  coordinate conditions, and `tau_equation_from_betas` verifies Equation (1)
  holds for them. Since the β's are uniquely determined by those conditions,
  this is a complete check that the printed τ's are the ones Equation (1)
  produces.
- (T1), order three, (T3), (T2) (via `cycleSupport`, valid because the order
  is three), and (T4) (via an explicit word for every ordered pair of darts)
  are all decided by the kernel.

## 4. Correspondence with the paper

| Paper | Lean | Status |
|---|---|---|
| Definition 2.1 (bitrade) | `IsBitrade` | formalised |
| k-homogeneous, transversal | `IsKHomogeneous`, `IsTransversal` | formalised |
| Equation (1), β maps | `Canonical.beta₁/₂/₃`, `tauRow/Column/Symbol` | formalised for any bitrade |
| Definition 2.2 (T1) | `tau_product` | proved for any bitrade |
| Definition 2.2 (T3) | `tau*_fixedPointFree` | proved for any bitrade |
| Definition 2.2 (T2), (T4) | `TauExample` only | checked for Example 2.6 only; not needed for Theorem 1.1 |
| Theorem 2.4 (Drápal), Construction 2.5 | none | not formalised |
| Constructions 3.1, 3.3, Lemma 3.5 (torus) | none | not formalised |
| Example 2.6 and its transversals | `PaperExample`, `TauExample` | fully checked |
| τᵢ³ = 1 from 3-homogeneity | `perm_pow_three_of_fiber_card_three` | proved |
| Γ and Equation (3) | `TriangleGroup`, `rho_relations` | concrete model, relations checked |
| θ : Γ → G, Equation (4) | `triangleRepresentation` | proved for any (T1)+order-three triple |
| Lemma 4.1 (ψ well defined, equivariant) | `EquivariantOrbitMap.exists_equivariant` | proved, with the missing hypothesis made explicit |
| Definition 4.2 (T₁, T₂, T₃ by position) | colour classes of `color` | algebraic substitute |
| Lemma 4.3, Cases 1 to 4 | `rotation_one_conjugate_generator`, `rotation_one_not_in_stabilizer` | algebraic substitute |
| Corollary 4.4, 4.5 (disjoint, partition) | `three_homogeneous_permutation_partition` | proved, per orbit |
| Lemma 4.6 (each Tᵢ is a transversal) | `color_class_fiber_card`, `forgetDarts_isTransversal` | proved |
| Theorem 1.1 | `theorem_1_1` | proved |

The two "algebraic substitute" rows are the same mathematics as the paper.
The paper's T₁, T₂, T₃ are indexed by the position of a shaded triangle
relative to its black vertex, which is the rotational component of the group
element carrying the base triangle there. Disjointness of the Tᵢ is
therefore the statement that the stabiliser of a dart contains no
non-translation, and the paper's descent argument moves an inconsistent pair
toward a vertex until some τᵢ has a fixed point. The Lean does the same by
conjugating to a generator in one step.

## 5. Checks performed

| Check | Command | Result |
|---|---|---|
| Full build | `lake build` | success, 3044 jobs |
| Escape hatches | `grep -nE 'sorry\|admit\|native_decide\|axiom\|unsafe\|implemented_by\|extern\|opaque\|partial def' Partitioning3Homogeneous/*.lean` | no hits |
| Axioms | `#print axioms` on `theorem_1_1`, `permutations_admit_three_coloring`, `exists_three_coloring`, `rotation_one_conjugate_generator`, `exists_equivariant` | only `propext`, `Classical.choice`, `Quot.sound` |
| Warnings | `lake env lean Partitioning3Homogeneous/<Module>.lean` for all nine modules | no output at all |
| Dead code | `grep -rn exists_equivariant_of_free` | defined, never used |
| Unused hypotheses | grep for uses of `IsPartialLatin` outside `Basic`/`PaperExample` | none; the conjuncts are never consumed |
| Second positive example | Appendix A | Z/3 Cayley table against its symbol shift is a 3-homogeneous bitrade; `theorem_1_1` applies |
| Negative controls | Appendix A | deleting one entry breaks `IsBitrade`; an unused ambient row breaks `IsKHomogeneous 3` |

## 6. What the formalisation says about the paper

1. **Lemma 4.1, well-definedness of ψ.** The proof writes: "t₀δ₁δ₂⁻¹ = t₀ so
   (δ₁δ₂⁻¹)θ = g ∈ G where x₀g = x₀ (we can't assume that g is the identity
   in G, only that it fixes x₀)." The conclusion x₀g = x₀ is asserted, not
   derived; in general a homomorphism between acting groups does not make an
   orbit map well defined. The step is nevertheless valid here because Γ acts
   freely on the shaded triangles of the tessellation, so δ₁ = δ₂ and g is
   the identity in G after all. The parenthetical remark is therefore
   misleading rather than wrong. `OrbitMap.lean` isolates the precise
   hypothesis (`MapsStabilizer`) and proves freeness is sufficient.
2. **Unstated use of (T4).** Lemma 3.5 invokes (T4) to obtain a combinatorial
   hypermap, and Corollary 4.5 says "By assumption, the group G acts
   transitively on T◇". Theorem 1.1 does not assume the bitrade is primary.
   The reduction to primary components is standard but is not stated. The
   Lean proof colours each orbit separately and needs no such reduction.
3. **(T2) is not needed.** `permutations_admit_three_coloring` uses only
   (T1), the order-three relations, and (T3). Condition (T2) holds for the τ's
   of any bitrade by Drápal's theorem, but it plays no role in Theorem 1.1.

None of these affect the truth of any statement in the paper.

## 7. Modelling conventions a reader should know

- **No empty rows, columns, or unused symbols.** `Row`, `Column`, `Symbol`
  are finite types and `IsKHomogeneous 3` ranges over all of their elements.
  A 3-homogeneous bitrade sitting inside a larger n × n array must be
  re-indexed to its occupied rows, columns, and symbols before `theorem_1_1`
  applies. This is without loss of generality, and `IsTransversal` uses the
  same convention, so the statement is internally consistent. The negative
  control in Appendix A demonstrates the behaviour.
- **Row, column, and symbol types may differ.** The paper takes three sets
  of equal size n; the Lean does not require this. 3-homogeneity forces the
  three cardinalities to agree anyway.
- **Composition order.** Lean's `Equiv.Perm` multiplies right to left. The
  paper's τ₁τ₂τ₃ = 1 under right actions is `tauSymbol * tauColumn * tauRow = 1`
  in Lean. Every place this matters is handled and commented.
- **`IsPartialLatin` is redundant.** Both conjuncts of `IsBitrade` follow
  from (R2) and (R3): if two entries of T◇ shared a cell, (R2) would give a
  common mate in T⊗ and (R3) for that mate would force the two entries to
  coincide. Keeping them is faithful to Definition 2.1 and harmless.
- **Choice.** The β maps are built with `Classical.choose` from cardinality
  one, so they are noncomputable. This is fine; they are unique.

## 8. Nits and suggested edits

Documentation only; nothing here affects correctness.

1. `README.md`: "the representation induced by any permutation triple
   satisfying (T1)–(T3)". The representation `triangleRepresentation` needs
   (T1) and the order-three relations only. (T3) enters in `ThreeColoring`,
   and (T2) is never used.
2. `MatePermutations.lean`, docstring of `perm_pow_three_of_fiber_card_three`:
   "This is the finite combinatorial input behind (T2)" should read "behind
   the order-three relations τᵢ³ = 1 of Equation (4)".
3. `OrbitMap.lean`: `exists_equivariant_of_free` is unused. Either mark it
   as a remark in the docstring or delete it.
4. `lakefile.toml` pins Mathlib to a release candidate (`v4.34.0-rc2`).
   Consider moving to the corresponding stable tag once available.
5. Optional strengthening: state explicitly that the concrete
   `TriangleGroup` is generated by `rho₁`, `rho₂`, `rho₃`. Together with
   `rho_relations` and `triangleRepresentation` this would make the
   isomorphism with the presented group of Equation (3) a stated theorem
   rather than an implicit consequence.
6. Optional completeness: prove (T2) for `Canonical.tauRow/Column/Symbol` of
   an arbitrary bitrade, so that all of Definition 2.2 is covered in general
   and not only for Example 2.6.

## 9. Not formalised

Listed for completeness; the README already says the project does not
attempt these.

- Theorem 2.4 (Drápal's equivalence between bitrades and τ-representations)
  and Construction 2.5 (from τ's back to a bitrade), including the claim in
  Example 2.6 about the cell at row (111,142,123), column (111,213,412).
- Constructions 3.1 and 3.3 (hypermap, canonical triangulation), Example
  3.2, and Lemma 3.5 (genus formula, torus, Euclidean covering).
- The map ψ from triangles to darts and the geometric Definition 4.2.
- The Euclidean-distance case analysis in the proof of Lemma 4.3.

## Appendix A: scratch tests

This file was compiled against the project with
`lake env lean <path>` and produced no output, i.e. every statement was
accepted by the kernel.

```lean
import Partitioning3Homogeneous

open LatinBitrade

namespace Cyclic3Test

abbrev L := Fin 3
abbrev E := Entry L L L

/-- Cayley table of Z/3: (i, j, i+j). -/
def positive : Finset E :=
  (Finset.univ : Finset (L × L)).image fun p => ⟨p.1, p.2, p.1 + p.2⟩

/-- The same cells with every symbol shifted by one: (i, j, i+j+1). -/
def negative : Finset E :=
  (Finset.univ : Finset (L × L)).image fun p => ⟨p.1, p.2, p.1 + p.2 + 1⟩

theorem cyclic_is_bitrade : IsBitrade positive negative := by
  unfold IsBitrade IsPartialLatin HasUniqueMates positive negative
  decide

theorem cyclic_is_three_homogeneous : IsKHomogeneous 3 positive := by
  unfold IsKHomogeneous positive
  decide

/-- Theorem 1.1 applies to it. -/
example : ∃ T₀ T₁ T₂, IsThreeTransversalPartition positive T₀ T₁ T₂ :=
  theorem_1_1 positive negative cyclic_is_bitrade cyclic_is_three_homogeneous

/-- Negative control: an ambient row type with an unused row makes
`IsKHomogeneous 3` fail, documenting the "no empty rows" convention. -/
def positive4 : Finset (Entry (Fin 4) L L) :=
  positive.image fun e => ⟨Fin.castSucc e.row, e.column, e.symbol⟩

theorem unused_row_breaks_homogeneity : ¬ IsKHomogeneous 3 positive4 := by
  unfold IsKHomogeneous positive4 positive
  decide

/-- Negative control: the paper's example with one entry deleted is not a
bitrade. -/
theorem deleted_entry_not_bitrade :
    ¬ IsBitrade (PaperExample.positive.erase (PaperExample.entry 0 0 0))
        PaperExample.negative := by
  unfold IsBitrade IsPartialLatin HasUniqueMates PaperExample.positive
    PaperExample.negative PaperExample.entry
  decide

end Cyclic3Test
```

## Appendix B: axiom audit

```lean
import Partitioning3Homogeneous

#print axioms LatinBitrade.theorem_1_1
-- 'LatinBitrade.theorem_1_1' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms EuclideanTriangleGroup.permutations_admit_three_coloring
-- [propext, Classical.choice, Quot.sound]
#print axioms EuclideanTriangleGroup.exists_three_coloring
-- [propext, Classical.choice, Quot.sound]
#print axioms EuclideanTriangleGroup.rotation_one_conjugate_generator
-- [propext, Classical.choice, Quot.sound]
#print axioms EquivariantOrbitMap.exists_equivariant
-- [propext, Classical.choice]
```
