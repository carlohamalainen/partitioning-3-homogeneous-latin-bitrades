import Partitioning3Homogeneous.Basic

/-!
# The 12-entry example in the paper

Machine-checked certificates for Example 2.6 and its three displayed
transversals (the numbering in `3hom.tex` is `1` through `4`).
-/

namespace LatinBitrade.PaperExample

/-- Paper labels `1` through `4`, represented internally by `Fin 4`. -/
abbrev Label := Fin 4

abbrev one : Label := 0
abbrev two : Label := 1
abbrev three : Label := 2
abbrev four : Label := 3

abbrev PaperEntry := Entry Label Label Label

def entry (r c s : Label) : PaperEntry := ⟨r, c, s⟩

/-- The partial Latin square `T^diamond` displayed in Equation (2). -/
def positive : Finset PaperEntry :=
  [ entry one   one   one,
    entry one   two   three,
    entry one   four  two,
    entry two   one   three,
    entry two   two   two,
    entry two   three four,
    entry three two   four,
    entry three three three,
    entry three four  one,
    entry four  one   two,
    entry four  three one,
    entry four  four  four ].toFinset

/-- The mate `T^otimes` displayed in Equation (2). -/
def negative : Finset PaperEntry :=
  [ entry one   one   three,
    entry one   two   two,
    entry one   four  one,
    entry two   one   two,
    entry two   two   four,
    entry two   three three,
    entry three two   three,
    entry three three one,
    entry three four  four,
    entry four  one   one,
    entry four  three four,
    entry four  four  two ].toFinset

/-- The diagonal transversal displayed below Figure 4. -/
def transversal₁ : Finset PaperEntry :=
  [ entry one one one,
    entry two two two,
    entry three three three,
    entry four four four ].toFinset

/-- The lower-left transversal displayed below Figure 4. -/
def transversal₂ : Finset PaperEntry :=
  [ entry one four two,
    entry two one three,
    entry three two four,
    entry four three one ].toFinset

/-- The lower-right transversal displayed below Figure 4. -/
def transversal₃ : Finset PaperEntry :=
  [ entry one two three,
    entry two three four,
    entry three four one,
    entry four one two ].toFinset

/-- Lean checks all three clauses of the partial Latin property for both
arrays, disjointness, and all unique-mate obligations in (R2)/(R3). -/
theorem equation2_is_bitrade : IsBitrade positive negative := by
  unfold IsBitrade IsPartialLatin HasUniqueMates
  decide

/-- Lean checks that each row and column has three entries and that every
symbol occurs three times. -/
theorem equation2_is_three_homogeneous : IsKHomogeneous 3 positive := by
  unfold IsKHomogeneous
  decide

/-- Lean checks that the three displayed sets are pairwise disjoint, cover
`T^diamond`, and individually satisfy the paper's transversal definition. -/
theorem displayed_partition_is_valid :
    IsThreeTransversalPartition positive transversal₁ transversal₂ transversal₃ := by
  unfold IsThreeTransversalPartition IsTransversal
  decide

end LatinBitrade.PaperExample
