import Mathlib.Data.Fin.VecNotation
import Partitioning3Homogeneous.PaperExample
import Partitioning3Homogeneous.ThreeColoring

/-!
# The permutation representation of the paper's 12-entry example

The order of `Dart = Fin 12` below is documented by `dartEntry`. The tables
for `tau₁`, `tau₂`, and `tau₃` are exactly the oriented cycles printed after
Equation (2). This module checks conditions (T1)--(T4) for those tables.
-/

namespace LatinBitrade.PaperExample

/-- Indices for the twelve entries of `positive`. -/
abbrev Dart := Fin 12

/-- The concrete correspondence between our indices and the triples printed
in the paper. -/
def dartEntry : Dart → PaperEntry :=
  ![ entry one   one   one,    -- 0: 111
     entry one   two   three,  -- 1: 123
     entry one   four  two,    -- 2: 142
     entry two   one   three,  -- 3: 213
     entry two   two   two,    -- 4: 222
     entry two   three four,   -- 5: 234
     entry three two   four,   -- 6: 324
     entry three three three,  -- 7: 333
     entry three four  one,    -- 8: 341
     entry four  one   two,    -- 9: 412
     entry four  three one,    -- 10: 431
     entry four  four  four ]  -- 11: 444

/-- `dartEntry` contains every positive entry exactly once. -/
theorem dartEntry_enumerates_positive :
    Finset.univ.image dartEntry = positive := by
  decide

/-- An indexing of the twelve entries of `negative`, in the same cell order
as `dartEntry`. -/
def negativeDartEntry : Dart → PaperEntry :=
  ![ entry one   one   three,
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
     entry four  four  two ]

theorem negativeDartEntry_enumerates_negative :
    Finset.univ.image negativeDartEntry = negative := by
  decide

/-- `beta₁` changes the row and preserves column and symbol. Its input index
refers to `negativeDartEntry` and its output index to `dartEntry`. -/
def beta₁ : Dart ≃ Dart where
  toFun := ![3, 4, 8, 9, 6, 7, 1, 10, 11, 0, 5, 2]
  invFun := ![9, 6, 11, 0, 1, 10, 4, 5, 2, 3, 7, 8]
  left_inv := by decide
  right_inv := by decide

/-- `beta₂` changes the column and preserves row and symbol. -/
def beta₂ : Dart ≃ Dart where
  toFun := ![1, 2, 0, 4, 5, 3, 7, 8, 6, 10, 11, 9]
  invFun := ![2, 0, 1, 5, 3, 4, 8, 6, 7, 11, 9, 10]
  left_inv := by decide
  right_inv := by decide

/-- `beta₃` changes the symbol and preserves row and column. -/
def beta₃ : Dart ≃ Dart := Equiv.refl Dart

/-- The three tables above satisfy the defining coordinate conditions for
the maps `beta_r` in Section 2. -/
theorem beta_coordinate_conditions :
    (∀ x,
      let a := negativeDartEntry x
      let b := dartEntry (beta₁ x)
      a.row ≠ b.row ∧ a.column = b.column ∧ a.symbol = b.symbol) ∧
    (∀ x,
      let a := negativeDartEntry x
      let b := dartEntry (beta₂ x)
      a.row = b.row ∧ a.column ≠ b.column ∧ a.symbol = b.symbol) ∧
    (∀ x,
      let a := negativeDartEntry x
      let b := dartEntry (beta₃ x)
      a.row = b.row ∧ a.column = b.column ∧ a.symbol ≠ b.symbol) := by
  decide

/-- `(111,142,123) (213,234,222) (324,341,333) (412,444,431)`. -/
def tau₁ : Equiv.Perm Dart where
  toFun := ![2, 0, 1, 5, 3, 4, 8, 6, 7, 11, 9, 10]
  invFun := ![1, 2, 0, 4, 5, 3, 7, 8, 6, 10, 11, 9]
  left_inv := by decide
  right_inv := by decide

/-- `(111,213,412) (123,222,324) (234,333,431) (142,341,444)`. -/
def tau₂ : Equiv.Perm Dart where
  toFun := ![3, 4, 8, 9, 6, 7, 1, 10, 11, 0, 5, 2]
  invFun := ![9, 6, 11, 0, 1, 10, 4, 5, 2, 3, 7, 8]
  left_inv := by decide
  right_inv := by decide

/-- `(111,431,341) (123,333,213) (142,412,222) (234,444,324)`. -/
def tau₃ : Equiv.Perm Dart where
  toFun := ![10, 7, 9, 1, 2, 11, 5, 3, 0, 4, 8, 6]
  invFun := ![8, 3, 4, 7, 9, 6, 11, 1, 10, 2, 0, 5]
  left_inv := by decide
  right_inv := by decide

/-- The displayed permutations are exactly those obtained from Equation (1):
`tau₁ = beta₂⁻¹ beta₃`, `tau₂ = beta₃⁻¹ beta₁`, and
`tau₃ = beta₁⁻¹ beta₂`, with maps applied from left to right. -/
theorem tau_equation_from_betas :
    (∀ x, tau₁ x = beta₃ (beta₂.symm x)) ∧
    (∀ x, tau₂ x = beta₁ (beta₃.symm x)) ∧
    (∀ x, tau₃ x = beta₂ (beta₁.symm x)) := by
  decide

/-- (T1), written in the paper's right-action order. -/
theorem tau_product_identity (x : Dart) : tau₃ (tau₂ (tau₁ x)) = x := by
  decide +revert

/-- Every displayed permutation has order three. -/
theorem tau_order_three :
    (∀ x, tau₁ (tau₁ (tau₁ x)) = x) ∧
    (∀ x, tau₂ (tau₂ (tau₂ x)) = x) ∧
    (∀ x, tau₃ (tau₃ (tau₃ x)) = x) := by
  decide

/-- (T3): all three displayed permutations are fixed-point-free. -/
theorem tau_fixedPointFree :
    (∀ x, tau₁ x ≠ x) ∧
    (∀ x, tau₂ x ≠ x) ∧
    (∀ x, tau₃ x ≠ x) := by
  decide

/-- The support of the length-three cycle of `tau` containing `x`. -/
def cycleSupport (tau : Equiv.Perm Dart) (x : Dart) : Finset Dart :=
  [x, tau x, tau (tau x)].toFinset

/-- (T2): a cycle from one permutation and a cycle from another intersect
in at most one dart. -/
theorem tau_cycles_pairwise_disjoint :
    (∀ x y, ((cycleSupport tau₁ x) ∩ (cycleSupport tau₂ y)).card ≤ 1) ∧
    (∀ x y, ((cycleSupport tau₁ x) ∩ (cycleSupport tau₃ y)).card ≤ 1) ∧
    (∀ x y, ((cycleSupport tau₂ x) ∩ (cycleSupport tau₃ y)).card ≤ 1) := by
  decide

inductive Generator where
  | first | second | third
  deriving DecidableEq, Repr

def applyGenerator : Generator → Dart → Dart
  | .first => tau₁
  | .second => tau₂
  | .third => tau₃

/-- Apply a word from left to right, following the paper's right-action
convention. -/
def applyWord (start : Dart) : List Generator → Dart :=
  List.foldl (fun x generator => applyGenerator generator x) start

private def pathFromZero : Dart → List Generator :=
  ![ [],
     [.first, .first],
     [.first],
     [.second],
     [.first, .first, .second],
     [.second, .first],
     [.first, .first, .second, .second],
     [.first, .first, .third],
     [.first, .second],
     [.first, .third],
     [.third],
     [.first, .second, .second] ]

private def inverseWord (word : List Generator) : List Generator :=
  word.reverse.flatMap fun generator => [generator, generator]

private def pathBetween (x y : Dart) : List Generator :=
  inverseWord (pathFromZero x) ++ pathFromZero y

/-- (T4): an explicit word in the generators sends any dart to any other
dart. Thus the generated permutation group is transitive. -/
theorem tau_action_transitive (x y : Dart) :
    applyWord x (pathBetween x y) = y := by
  decide +revert

/-- The pointwise checks above, bundled as relations in Lean's permutation
group. Lean composes functions from right to left, hence the reversed order
relative to the paper's right-action notation. -/
theorem tau_group_relations :
    tau₃ ^ 3 = 1 ∧ tau₂ ^ 3 = 1 ∧ tau₁ ^ 3 = 1 ∧
      tau₃ * tau₂ * tau₁ = 1 := by
  decide

/-- The general triangle-group theorem applies to the example's three
permutations, independently of the explicitly displayed partition. -/
theorem tau_structural_coloring :
    ∃ color : Dart → ZMod 3,
      (∀ x, color (tau₁ x) = color x + 1) ∧
      (∀ x, color (tau₂ x) = color x + 1) ∧
      (∀ x, color (tau₃ x) = color x + 1) := by
  obtain ⟨color, h₃, h₂, h₁⟩ :=
    EuclideanTriangleGroup.permutations_admit_three_coloring
      tau₃ tau₂ tau₁
      tau_group_relations.1 tau_group_relations.2.1 tau_group_relations.2.2.1
      tau_group_relations.2.2.2
      tau_fixedPointFree.2.2 tau_fixedPointFree.2.1 tau_fixedPointFree.1
  exact ⟨color, h₁, h₂, h₃⟩

end LatinBitrade.PaperExample
