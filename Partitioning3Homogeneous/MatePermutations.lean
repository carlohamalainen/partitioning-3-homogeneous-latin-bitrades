import Partitioning3Homogeneous.TransversalPartition

/-!
# Canonical mate maps and bitrade permutations

This module constructs the three bijections `beta₁`, `beta₂`, `beta₃`
from the unique-mate clauses of a Latin bitrade.  It then defines the three
permutations from Equation (1) of the paper.
-/

namespace LatinBitrade

section UniqueChoice

variable {E : Type*} [DecidableEq E]

noncomputable def chooseOfCardOne (s : Finset E) (h : s.card = 1) : E :=
  Classical.choose (Finset.card_eq_one.mp h)

omit [DecidableEq E] in
theorem chooseOfCardOne_spec (s : Finset E) (h : s.card = 1) :
    s = {chooseOfCardOne s h} :=
  Classical.choose_spec (Finset.card_eq_one.mp h)

omit [DecidableEq E] in
theorem chooseOfCardOne_mem (s : Finset E) (h : s.card = 1) :
    chooseOfCardOne s h ∈ s := by
  have hmembership := congrArg
    (fun t : Finset E => chooseOfCardOne s h ∈ t)
    (chooseOfCardOne_spec s h)
  exact hmembership.mpr (by simp)

omit [DecidableEq E] in
theorem eq_chooseOfCardOne_of_mem (s : Finset E) (h : s.card = 1)
    {x : E} (hx : x ∈ s) : x = chooseOfCardOne s h := by
  rw [chooseOfCardOne_spec s h] at hx
  simpa using hx

variable (source target : Finset E)
variable (R : E → E → Prop) [DecidableRel R]

/-- Choose the unique target related to a source element. -/
noncomputable def mateBy
    (hcard : ∀ x : {e // e ∈ source},
      (target.filter fun y => R x.val y).card = 1)
    (x : {e // e ∈ source}) : {e // e ∈ target} :=
  let fiber := target.filter fun y => R x.val y
  let h := hcard x
  ⟨chooseOfCardOne fiber h,
    (Finset.mem_filter.mp (chooseOfCardOne_mem fiber h)).1⟩

omit [DecidableEq E] in
theorem mateBy_relation
    (hcard : ∀ x : {e // e ∈ source},
      (target.filter fun y => R x.val y).card = 1)
    (x : {e // e ∈ source}) : R x.val (mateBy source target R hcard x).val := by
  change R x.val (chooseOfCardOne (target.filter fun y => R x.val y) (hcard x))
  exact (Finset.mem_filter.mp
    (chooseOfCardOne_mem (target.filter fun y => R x.val y) (hcard x))).2

omit [DecidableEq E] in
theorem mateBy_unique
    (hcard : ∀ x : {e // e ∈ source},
      (target.filter fun y => R x.val y).card = 1)
    (x : {e // e ∈ source}) (y : {e // e ∈ target})
    (hxy : R x.val y.val) : y = mateBy source target R hcard x := by
  apply Subtype.ext
  change y.val = chooseOfCardOne (target.filter fun z => R x.val z) (hcard x)
  exact eq_chooseOfCardOne_of_mem _ (hcard x)
    (Finset.mem_filter.mpr ⟨y.property, hxy⟩)

/-- Symmetric unique-mate relations in both directions give an equivalence. -/
noncomputable def mateEquivBy
    (hforward : ∀ x : {e // e ∈ source},
      (target.filter fun y => R x.val y).card = 1)
    (hreverse : ∀ y : {e // e ∈ target},
      (source.filter fun x => R y.val x).card = 1)
    (hsymmetric : ∀ x y, R x y ↔ R y x) :
    {e // e ∈ source} ≃ {e // e ∈ target} where
  toFun := mateBy source target R hforward
  invFun := mateBy target source R hreverse
  left_inv x := by
    have hrel : R (mateBy source target R hforward x).val x.val :=
      (hsymmetric _ _).mp (mateBy_relation source target R hforward x)
    exact (mateBy_unique target source R hreverse
      (mateBy source target R hforward x) x hrel).symm
  right_inv y := by
    have hrel : R (mateBy target source R hreverse y).val y.val :=
      (hsymmetric _ _).mp (mateBy_relation target source R hreverse y)
    exact (mateBy_unique source target R hforward
      (mateBy target source R hreverse y) y hrel).symm

end UniqueChoice

section Coordinates

variable {Row Column Symbol : Type*}
variable [DecidableEq Row] [DecidableEq Column] [DecidableEq Symbol]

def SameRowColumn (x y : Entry Row Column Symbol) : Prop :=
  x.row = y.row ∧ x.column = y.column

def SameRowSymbol (x y : Entry Row Column Symbol) : Prop :=
  x.row = y.row ∧ x.symbol = y.symbol

def SameColumnSymbol (x y : Entry Row Column Symbol) : Prop :=
  x.column = y.column ∧ x.symbol = y.symbol

instance instDecidableSameRowColumn : DecidableRel
    (SameRowColumn (Row := Row) (Column := Column) (Symbol := Symbol)) :=
  fun _ _ => by unfold SameRowColumn; infer_instance

instance instDecidableSameRowSymbol : DecidableRel
    (SameRowSymbol (Row := Row) (Column := Column) (Symbol := Symbol)) :=
  fun _ _ => by unfold SameRowSymbol; infer_instance

instance instDecidableSameColumnSymbol : DecidableRel
    (SameColumnSymbol (Row := Row) (Column := Column) (Symbol := Symbol)) :=
  fun _ _ => by unfold SameColumnSymbol; infer_instance

omit [DecidableEq Row] [DecidableEq Column] [DecidableEq Symbol] in
theorem sameRowColumn_symmetric (x y : Entry Row Column Symbol) :
    SameRowColumn x y ↔ SameRowColumn y x := by
  constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₁.symm, h₂.symm⟩

omit [DecidableEq Row] [DecidableEq Column] [DecidableEq Symbol] in
theorem sameRowSymbol_symmetric (x y : Entry Row Column Symbol) :
    SameRowSymbol x y ↔ SameRowSymbol y x := by
  constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₁.symm, h₂.symm⟩

omit [DecidableEq Row] [DecidableEq Column] [DecidableEq Symbol] in
theorem sameColumnSymbol_symmetric (x y : Entry Row Column Symbol) :
    SameColumnSymbol x y ↔ SameColumnSymbol y x := by
  constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₁.symm, h₂.symm⟩

theorem uniqueMates_rowColumn
    {source target : Finset (Entry Row Column Symbol)} (h : HasUniqueMates source target)
    (x : {e // e ∈ source}) :
    (target.filter fun y => SameRowColumn x.val y).card = 1 := by
  simpa [SameRowColumn, eq_comm] using
    (not_ne_iff.mp ((Finset.filter_eq_empty_iff.mp h.1) x.property))

theorem uniqueMates_rowSymbol
    {source target : Finset (Entry Row Column Symbol)} (h : HasUniqueMates source target)
    (x : {e // e ∈ source}) :
    (target.filter fun y => SameRowSymbol x.val y).card = 1 := by
  simpa [SameRowSymbol, eq_comm] using
    (not_ne_iff.mp ((Finset.filter_eq_empty_iff.mp h.2.1) x.property))

theorem uniqueMates_columnSymbol
    {source target : Finset (Entry Row Column Symbol)} (h : HasUniqueMates source target)
    (x : {e // e ∈ source}) :
    (target.filter fun y => SameColumnSymbol x.val y).card = 1 := by
  simpa [SameColumnSymbol, eq_comm] using
    (not_ne_iff.mp ((Finset.filter_eq_empty_iff.mp h.2.2) x.property))

end Coordinates

section ThreeElementFibers

variable {D A : Type*}
variable [Fintype D] [DecidableEq D] [DecidableEq A]

/-- A fixed-point-free permutation preserving fibres of size three has
order three.  This is the finite combinatorial input behind (T2). -/
theorem perm_pow_three_of_fiber_card_three
    (coordinate : D → A) (tau : Equiv.Perm D)
    (hpreserves : ∀ x, coordinate (tau x) = coordinate x)
    (hcard : ∀ a, (Finset.univ.filter fun x => coordinate x = a).card = 3)
    (hfree : ∀ x, tau x ≠ x) : tau ^ 3 = 1 := by
  ext x
  let fiber := Finset.univ.filter fun y => coordinate y = coordinate x
  have hxFiber : x ∈ fiber := by simp [fiber]
  have htauFiber : tau x ∈ fiber := by simp [fiber, hpreserves x]
  have hfiberCard : fiber.card = 3 := hcard (coordinate x)
  have htwice : tau (tau x) ≠ x := by
    intro htwo
    let pair : Finset D := {x, tau x}
    have hpairCard : pair.card = 2 := by simp [pair, (hfree x).symm]
    have hpairSubset : pair ⊆ fiber := by
      intro z hz
      simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hxFiber
      · exact htauFiber
    obtain ⟨y, hyFiber, hyPair⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card
        (s := pair) (t := fiber) (by rw [hpairCard, hfiberCard]; norm_num)
    have hyNe : y ≠ x ∧ y ≠ tau x := by simpa [pair] using hyPair
    let triple : Finset D := {x, tau x, y}
    have htripleSubset : triple ⊆ fiber := by
      intro z hz
      simp only [triple, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact hxFiber
      · exact htauFiber
      · exact hyFiber
    have htripleCard : triple.card = 3 := by
      simp [triple, (hfree x).symm, hyNe.1.symm, hyNe.2.symm]
    have htripleEq : triple = fiber :=
      Finset.eq_of_subset_of_card_le htripleSubset (by rw [htripleCard, hfiberCard])
    have htauYFiber : tau y ∈ fiber := by
      have hyCoordinate : coordinate y = coordinate x := by simpa [fiber] using hyFiber
      simp [fiber, (hpreserves y).trans hyCoordinate]
    have htauYTriple : tau y ∈ triple := by simpa [htripleEq] using htauYFiber
    simp only [triple, Finset.mem_insert, Finset.mem_singleton] at htauYTriple
    rcases htauYTriple with hyx | hytaux | hyy
    · apply hyNe.2
      apply tau.injective
      exact hyx.trans htwo.symm
    · exact hyNe.1 (tau.injective hytaux)
    · exact hfree y hyy
  have htwiceFiber : tau (tau x) ∈ fiber := by
    simp [fiber, (hpreserves (tau x)).trans (hpreserves x)]
  let cycle : Finset D := {x, tau x, tau (tau x)}
  have hcycleSubset : cycle ⊆ fiber := by
    intro z hz
    simp only [cycle, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact hxFiber
    · exact htauFiber
    · exact htwiceFiber
  have hcycleCard : cycle.card = 3 := by
    have hfirstTwice : tau x ≠ tau (tau x) := (hfree (tau x)).symm
    simp [cycle, (hfree x).symm, htwice.symm, hfirstTwice]
  have hcycleEq : cycle = fiber :=
    Finset.eq_of_subset_of_card_le hcycleSubset (by rw [hcycleCard, hfiberCard])
  have hthirdFiber : tau (tau (tau x)) ∈ fiber := by
    simp [fiber, (hpreserves (tau (tau x))).trans
      ((hpreserves (tau x)).trans (hpreserves x))]
  have hthirdCycle : tau (tau (tau x)) ∈ cycle := by
    simpa [hcycleEq] using hthirdFiber
  have hthird : tau (tau (tau x)) = x := by
    simp only [cycle, Finset.mem_insert, Finset.mem_singleton] at hthirdCycle
    rcases hthirdCycle with h | h | h
    · exact h
    · exfalso
      exact htwice (tau.injective h)
    · exfalso
      exact hfree x (tau.injective (tau.injective h))
  simpa [pow_succ, Equiv.Perm.mul_apply] using hthird

end ThreeElementFibers

namespace Canonical

variable {Row Column Symbol : Type*}
variable [DecidableEq Row] [DecidableEq Column] [DecidableEq Symbol]
variable (positive negative : Finset (Entry Row Column Symbol))
variable (hbit : IsBitrade positive negative)

private theorem mates_positive_negative
    (hbit : IsBitrade positive negative) : HasUniqueMates positive negative :=
  hbit.2.2.2.1

private theorem mates_negative_positive
    (hbit : IsBitrade positive negative) : HasUniqueMates negative positive :=
  hbit.2.2.2.2

/-- `beta₁` changes the row and preserves column and symbol. -/
noncomputable def beta₁ (hbit : IsBitrade positive negative) :
    Darts negative ≃ Darts positive :=
  mateEquivBy negative positive SameColumnSymbol
    (uniqueMates_columnSymbol (mates_negative_positive positive negative hbit))
    (uniqueMates_columnSymbol (mates_positive_negative positive negative hbit))
    sameColumnSymbol_symmetric

/-- `beta₂` changes the column and preserves row and symbol. -/
noncomputable def beta₂ (hbit : IsBitrade positive negative) :
    Darts negative ≃ Darts positive :=
  mateEquivBy negative positive SameRowSymbol
    (uniqueMates_rowSymbol (mates_negative_positive positive negative hbit))
    (uniqueMates_rowSymbol (mates_positive_negative positive negative hbit))
    sameRowSymbol_symmetric

/-- `beta₃` changes the symbol and preserves row and column. -/
noncomputable def beta₃ (hbit : IsBitrade positive negative) :
    Darts negative ≃ Darts positive :=
  mateEquivBy negative positive SameRowColumn
    (uniqueMates_rowColumn (mates_negative_positive positive negative hbit))
    (uniqueMates_rowColumn (mates_positive_negative positive negative hbit))
    sameRowColumn_symmetric

theorem beta₁_relation (x : Darts negative) :
    SameColumnSymbol x.val (beta₁ positive negative hbit x).val :=
  mateBy_relation negative positive SameColumnSymbol _ x

theorem beta₂_relation (x : Darts negative) :
    SameRowSymbol x.val (beta₂ positive negative hbit x).val :=
  mateBy_relation negative positive SameRowSymbol _ x

theorem beta₃_relation (x : Darts negative) :
    SameRowColumn x.val (beta₃ positive negative hbit x).val :=
  mateBy_relation negative positive SameRowColumn _ x

theorem beta₁_symm_relation (x : Darts positive) :
    SameColumnSymbol x.val ((beta₁ positive negative hbit).symm x).val :=
  mateBy_relation positive negative SameColumnSymbol _ x

theorem beta₂_symm_relation (x : Darts positive) :
    SameRowSymbol x.val ((beta₂ positive negative hbit).symm x).val :=
  mateBy_relation positive negative SameRowSymbol _ x

theorem beta₃_symm_relation (x : Darts positive) :
    SameRowColumn x.val ((beta₃ positive negative hbit).symm x).val :=
  mateBy_relation positive negative SameRowColumn _ x

/-- The row cycles (`tau₁` in the paper). -/
noncomputable def tauRow (hbit : IsBitrade positive negative) :
    Equiv.Perm (Darts positive) :=
  (beta₂ positive negative hbit).symm.trans (beta₃ positive negative hbit)

/-- The column cycles (`tau₂` in the paper). -/
noncomputable def tauColumn (hbit : IsBitrade positive negative) :
    Equiv.Perm (Darts positive) :=
  (beta₃ positive negative hbit).symm.trans (beta₁ positive negative hbit)

/-- The symbol cycles (`tau₃` in the paper). -/
noncomputable def tauSymbol (hbit : IsBitrade positive negative) :
    Equiv.Perm (Darts positive) :=
  (beta₁ positive negative hbit).symm.trans (beta₂ positive negative hbit)

theorem tauRow_preserves_row (x : Darts positive) :
    (tauRow positive negative hbit x).val.row = x.val.row := by
  let y := (beta₂ positive negative hbit).symm x
  have h₂ := beta₂_symm_relation positive negative hbit x
  have h₃ := beta₃_relation positive negative hbit y
  change (beta₃ positive negative hbit y).val.row = x.val.row
  exact h₃.1.symm.trans h₂.1.symm

theorem tauColumn_preserves_column (x : Darts positive) :
    (tauColumn positive negative hbit x).val.column = x.val.column := by
  let y := (beta₃ positive negative hbit).symm x
  have h₃ := beta₃_symm_relation positive negative hbit x
  have h₁ := beta₁_relation positive negative hbit y
  change (beta₁ positive negative hbit y).val.column = x.val.column
  exact h₁.1.symm.trans h₃.2.symm

theorem tauSymbol_preserves_symbol (x : Darts positive) :
    (tauSymbol positive negative hbit x).val.symbol = x.val.symbol := by
  let y := (beta₁ positive negative hbit).symm x
  have h₁ := beta₁_symm_relation positive negative hbit x
  have h₂ := beta₂_relation positive negative hbit y
  change (beta₂ positive negative hbit y).val.symbol = x.val.symbol
  exact h₂.2.symm.trans h₁.2.symm

/-- Equation (1): with Lean's left-action convention, the product is
`tauSymbol * tauColumn * tauRow`. -/
theorem tau_product :
    tauSymbol positive negative hbit * tauColumn positive negative hbit *
        tauRow positive negative hbit = 1 := by
  ext x
  simp [tauSymbol, tauColumn, tauRow, Equiv.Perm.mul_apply]

private theorem positive_negative_values_ne
    (hbit : IsBitrade positive negative)
    (x : Darts positive) (y : Darts negative) : x.val ≠ y.val := by
  intro hxy
  have hyPositive : y.val ∈ positive := by simpa [hxy] using x.property
  have hyIntersection : y.val ∈ positive ∩ negative :=
    Finset.mem_inter.mpr ⟨hyPositive, y.property⟩
  rw [hbit.2.2.1] at hyIntersection
  simp at hyIntersection

theorem tauRow_fixedPointFree (x : Darts positive) :
    tauRow positive negative hbit x ≠ x := by
  intro hfixed
  let y := (beta₂ positive negative hbit).symm x
  have h₂image : beta₂ positive negative hbit y = x := by simp [y]
  have h₃image : beta₃ positive negative hbit y = x := by
    simpa [tauRow, y] using hfixed
  have h₂ := beta₂_relation positive negative hbit y
  have h₃ := beta₃_relation positive negative hbit y
  rw [h₂image] at h₂
  rw [h₃image] at h₃
  have hyx : y.val = x.val := by
    apply (entryEquiv Row Column Symbol).injective
    exact Prod.ext h₂.1 (Prod.ext h₃.2 h₂.2)
  exact positive_negative_values_ne positive negative hbit x y hyx.symm

theorem tauColumn_fixedPointFree (x : Darts positive) :
    tauColumn positive negative hbit x ≠ x := by
  intro hfixed
  let y := (beta₃ positive negative hbit).symm x
  have h₃image : beta₃ positive negative hbit y = x := by simp [y]
  have h₁image : beta₁ positive negative hbit y = x := by
    simpa [tauColumn, y] using hfixed
  have h₃ := beta₃_relation positive negative hbit y
  have h₁ := beta₁_relation positive negative hbit y
  rw [h₃image] at h₃
  rw [h₁image] at h₁
  have hyx : y.val = x.val := by
    apply (entryEquiv Row Column Symbol).injective
    exact Prod.ext h₃.1 (Prod.ext h₃.2 h₁.2)
  exact positive_negative_values_ne positive negative hbit x y hyx.symm

theorem tauSymbol_fixedPointFree (x : Darts positive) :
    tauSymbol positive negative hbit x ≠ x := by
  intro hfixed
  let y := (beta₁ positive negative hbit).symm x
  have h₁image : beta₁ positive negative hbit y = x := by simp [y]
  have h₂image : beta₂ positive negative hbit y = x := by
    simpa [tauSymbol, y] using hfixed
  have h₁ := beta₁_relation positive negative hbit y
  have h₂ := beta₂_relation positive negative hbit y
  rw [h₁image] at h₁
  rw [h₂image] at h₂
  have hyx : y.val = x.val := by
    apply (entryEquiv Row Column Symbol).injective
    exact Prod.ext h₂.1 (Prod.ext h₁.1 h₁.2)
  exact positive_negative_values_ne positive negative hbit x y hyx.symm

section Homogeneous

variable [Fintype Row] [Fintype Column] [Fintype Symbol]

theorem tauRow_pow_three
    (hbit : IsBitrade positive negative) (hhom : IsKHomogeneous 3 positive) :
    tauRow positive negative hbit ^ 3 = 1 := by
  obtain ⟨hrowCard, -, -⟩ := homogeneous_three_dart_cards hhom
  exact perm_pow_three_of_fiber_card_three
    (fun x : Darts positive => x.val.row)
    (tauRow positive negative hbit)
    (tauRow_preserves_row positive negative hbit) hrowCard
    (tauRow_fixedPointFree positive negative hbit)

theorem tauColumn_pow_three
    (hbit : IsBitrade positive negative) (hhom : IsKHomogeneous 3 positive) :
    tauColumn positive negative hbit ^ 3 = 1 := by
  obtain ⟨-, hcolumnCard, -⟩ := homogeneous_three_dart_cards hhom
  exact perm_pow_three_of_fiber_card_three
    (fun x : Darts positive => x.val.column)
    (tauColumn positive negative hbit)
    (tauColumn_preserves_column positive negative hbit) hcolumnCard
    (tauColumn_fixedPointFree positive negative hbit)

theorem tauSymbol_pow_three
    (hbit : IsBitrade positive negative) (hhom : IsKHomogeneous 3 positive) :
    tauSymbol positive negative hbit ^ 3 = 1 := by
  obtain ⟨-, -, hsymbolCard⟩ := homogeneous_three_dart_cards hhom
  exact perm_pow_three_of_fiber_card_three
    (fun x : Darts positive => x.val.symbol)
    (tauSymbol positive negative hbit)
    (tauSymbol_preserves_symbol positive negative hbit) hsymbolCard
    (tauSymbol_fixedPointFree positive negative hbit)

end Homogeneous

end Canonical

section MainTheorem

variable {Row Column Symbol : Type*}
variable [Fintype Row] [Fintype Column] [Fintype Symbol]
variable [DecidableEq Row] [DecidableEq Column] [DecidableEq Symbol]

/-- Theorem 1.1 (Cavenagh): the positive partial Latin square of every
3-homogeneous Latin bitrade partitions into three transversals. -/
theorem theorem_1_1
    (positive negative : Finset (Entry Row Column Symbol))
    (hbit : IsBitrade positive negative)
    (hhom : IsKHomogeneous 3 positive) :
    ∃ T₀ T₁ T₂, IsThreeTransversalPartition positive T₀ T₁ T₂ := by
  exact exists_three_transversal_partition_from_permutations
    positive
    (Canonical.tauRow positive negative hbit)
    (Canonical.tauColumn positive negative hbit)
    (Canonical.tauSymbol positive negative hbit)
    hhom
    (Canonical.tauRow_preserves_row positive negative hbit)
    (Canonical.tauColumn_preserves_column positive negative hbit)
    (Canonical.tauSymbol_preserves_symbol positive negative hbit)
    (Canonical.tauRow_pow_three positive negative hbit hhom)
    (Canonical.tauColumn_pow_three positive negative hbit hhom)
    (Canonical.tauSymbol_pow_three positive negative hbit hhom)
    (Canonical.tau_product positive negative hbit)
    (Canonical.tauRow_fixedPointFree positive negative hbit)
    (Canonical.tauColumn_fixedPointFree positive negative hbit)
    (Canonical.tauSymbol_fixedPointFree positive negative hbit)

end MainTheorem

end LatinBitrade
