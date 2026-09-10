import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.DeriveFintype

/-!
# Latin bitrades

Definitions corresponding to Section 2 of `3hom.tex`.

An entry has a row, column, and symbol. A partial Latin square is expressed
in the symmetric form used in the paper: two entries which agree in any two
coordinates agree in the third. The bitrade mate conditions below are the
three concrete instances of (R2) and (R3).
-/

namespace LatinBitrade

/-- An entry `(row, column, symbol)` of a partial Latin square. -/
structure Entry (Row Column Symbol : Type*) where
  row : Row
  column : Column
  symbol : Symbol
  deriving DecidableEq, Repr

/-- Entries are equivalent to ordinary triples. -/
def entryEquiv (Row Column Symbol : Type*) :
    Entry Row Column Symbol ≃ Row × Column × Symbol where
  toFun e := (e.row, e.column, e.symbol)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv e := by cases e; rfl
  right_inv p := by rcases p with ⟨r, c, s⟩; rfl

instance [Fintype Row] [Fintype Column] [Fintype Symbol] :
    Fintype (Entry Row Column Symbol) :=
  Fintype.ofEquiv (Row × Column × Symbol) (entryEquiv Row Column Symbol).symm

variable {Row Column Symbol : Type*}

/-- The partial-Latin-square condition: fixing any two coordinates uniquely
determines the third. -/
def IsPartialLatin
    [DecidableEq Row] [DecidableEq Column] [DecidableEq Symbol]
    (T : Finset (Entry Row Column Symbol)) : Prop :=
  (T.filter fun e =>
      (T.filter fun f => f.row = e.row ∧ f.column = e.column).card ≠ 1) = ∅ ∧
  (T.filter fun e =>
      (T.filter fun f => f.row = e.row ∧ f.symbol = e.symbol).card ≠ 1) = ∅ ∧
  (T.filter fun e =>
      (T.filter fun f => f.column = e.column ∧ f.symbol = e.symbol).card ≠ 1) = ∅

/-- Every entry of `source` has a unique entry of `target` agreeing with it
in each chosen pair of coordinates. -/
def HasUniqueMates
    [DecidableEq Row] [DecidableEq Column] [DecidableEq Symbol]
    (source target : Finset (Entry Row Column Symbol)) : Prop :=
  (source.filter fun e =>
      (target.filter fun f => f.row = e.row ∧ f.column = e.column).card ≠ 1) = ∅ ∧
  (source.filter fun e =>
      (target.filter fun f => f.row = e.row ∧ f.symbol = e.symbol).card ≠ 1) = ∅ ∧
  (source.filter fun e =>
      (target.filter fun f => f.column = e.column ∧ f.symbol = e.symbol).card ≠ 1) = ∅

/-- Definition 2.1: two partial Latin squares satisfying (R1)--(R3). -/
def IsBitrade
    [DecidableEq Row] [DecidableEq Column] [DecidableEq Symbol]
    (positive negative : Finset (Entry Row Column Symbol)) : Prop :=
  IsPartialLatin positive ∧
  IsPartialLatin negative ∧
  positive ∩ negative = ∅ ∧
  HasUniqueMates positive negative ∧
  HasUniqueMates negative positive

/-- Every row and column contains `k` entries and every symbol occurs `k`
times. This is the paper's definition of `k`-homogeneity. -/
def IsKHomogeneous
    [Fintype Row] [Fintype Column] [Fintype Symbol]
    [DecidableEq Row] [DecidableEq Column] [DecidableEq Symbol]
    (k : Nat) (T : Finset (Entry Row Column Symbol)) : Prop :=
  ((Finset.univ : Finset Row).filter fun r =>
      (T.filter fun e => e.row = r).card ≠ k) = ∅ ∧
  ((Finset.univ : Finset Column).filter fun c =>
      (T.filter fun e => e.column = c).card ≠ k) = ∅ ∧
  ((Finset.univ : Finset Symbol).filter fun s =>
      (T.filter fun e => e.symbol = s).card ≠ k) = ∅

/-- A subset which meets every row and column once and has no repeated
symbol, matching the definition immediately after Definition 2.1. -/
def IsTransversal
    [Fintype Row] [Fintype Column]
    [DecidableEq Row] [DecidableEq Column] [DecidableEq Symbol]
    (T X : Finset (Entry Row Column Symbol)) : Prop :=
  X ⊆ T ∧
  ((Finset.univ : Finset Row).filter fun r =>
      (X.filter fun e => e.row = r).card ≠ 1) = ∅ ∧
  ((Finset.univ : Finset Column).filter fun c =>
      (X.filter fun e => e.column = c).card ≠ 1) = ∅ ∧
  (X.image fun e => e.symbol).card = X.card

/-- A certificate for the conclusion of Theorem 1.1. -/
def IsThreeTransversalPartition
    [Fintype Row] [Fintype Column]
    [DecidableEq Row] [DecidableEq Column] [DecidableEq Symbol]
    (T T₁ T₂ T₃ : Finset (Entry Row Column Symbol)) : Prop :=
  IsTransversal T T₁ ∧
  IsTransversal T T₂ ∧
  IsTransversal T T₃ ∧
  T₁ ∩ T₂ = ∅ ∧
  T₁ ∩ T₃ = ∅ ∧
  T₂ ∩ T₃ = ∅ ∧
  T₁ ∪ T₂ ∪ T₃ = T

end LatinBitrade
