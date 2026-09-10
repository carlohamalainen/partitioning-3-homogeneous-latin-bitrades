import Partitioning3Homogeneous.Basic
import Partitioning3Homogeneous.ThreeColoring

/-!
# From the triangle-group colouring to transversals

This file formalizes the final combinatorial step: when the cycles of a
permutation are exactly the fibres of a coordinate, a colouring advanced by
that permutation meets every coordinate fibre exactly once.
-/

namespace LatinBitrade

variable {D A : Type*}

/-- The fibres of `coordinate` are precisely the (at most) three displayed
points in the cycle of `tau`. -/
def CyclesFibers (coordinate : D → A) (tau : Equiv.Perm D) : Prop :=
  ∀ x y, coordinate y = coordinate x ↔
    y = x ∨ y = tau x ∨ y = tau (tau x)

/-- Three elements in every fibre makes the coordinate map surjective. -/
theorem coordinate_surjective_of_card_three
    [Fintype D] [DecidableEq D] [DecidableEq A]
    (coordinate : D → A)
    (hcard : ∀ a, (Finset.univ.filter fun x => coordinate x = a).card = 3) :
    Function.Surjective coordinate := by
  intro a
  have hpositive : 0 < (Finset.univ.filter fun x => coordinate x = a).card := by
    rw [hcard]
    norm_num
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpositive
  exact ⟨x, by simpa using hx⟩

/-- A fixed-point-free order-three permutation preserving a coordinate whose
fibres have size three has exactly those fibres as its cycles. -/
theorem cyclesFibers_of_card_three
    [Fintype D] [DecidableEq D] [DecidableEq A]
    (coordinate : D → A) (tau : Equiv.Perm D)
    (hpreserves : ∀ x, coordinate (tau x) = coordinate x)
    (hcard : ∀ a, (Finset.univ.filter fun x => coordinate x = a).card = 3)
    (hthree : ∀ x, tau (tau (tau x)) = x)
    (hfree : ∀ x, tau x ≠ x) : CyclesFibers coordinate tau := by
  intro x y
  let cycle : Finset D := {x, tau x, tau (tau x)}
  have htwice : tau (tau x) ≠ x := by
    intro h
    have happly := congrArg tau h
    rw [hthree x] at happly
    exact hfree x happly.symm
  have hxFirst : x ≠ tau x := (hfree x).symm
  have hxTwice : x ≠ tau (tau x) := htwice.symm
  have hfirstTwice : tau x ≠ tau (tau x) := (hfree (tau x)).symm
  have hcycleCard : cycle.card = 3 := by
    simp [cycle, hxFirst, hxTwice, hfirstTwice]
  have hcycleSubset :
      cycle ⊆ Finset.univ.filter (fun z => coordinate z = coordinate x) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [cycle, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · rfl
    · exact hpreserves x
    · exact (hpreserves (tau x)).trans (hpreserves x)
  have hcycleEq :
      cycle = Finset.univ.filter (fun z => coordinate z = coordinate x) :=
    Finset.eq_of_subset_of_card_le hcycleSubset (by rw [hcard, hcycleCard])
  constructor
  · intro hy
    have hyMem : y ∈ Finset.univ.filter (fun z => coordinate z = coordinate x) := by
      simp [hy]
    rw [← hcycleEq] at hyMem
    simpa [cycle] using hyMem
  · rintro (rfl | rfl | rfl)
    · rfl
    · exact hpreserves x
    · exact (hpreserves (tau x)).trans (hpreserves x)

private theorem zmod_three_cases (x i : ZMod 3) :
    i = x ∨ i = x + 1 ∨ i = x + 2 := by
  revert x i
  decide

private theorem zmod_three_add_one_ne (x : ZMod 3) : x + 1 ≠ x := by
  revert x
  decide

private theorem zmod_three_add_two_ne (x : ZMod 3) : x + 2 ≠ x := by
  revert x
  decide

theorem color_twice
    (tau : Equiv.Perm D) (color : D → ZMod 3)
    (hcolor : ∀ x, color (tau x) = color x + 1) (x : D) :
    color (tau (tau x)) = color x + 2 := by
  rw [hcolor, hcolor]
  ring

/-- Within a coordinate fibre, the structural colouring is injective. -/
theorem color_injective_on_fiber
    (coordinate : D → A) (tau : Equiv.Perm D) (color : D → ZMod 3)
    (hcycles : CyclesFibers coordinate tau)
    (hcolor : ∀ x, color (tau x) = color x + 1)
    {x y : D} (hcoordinate : coordinate x = coordinate y)
    (hcolors : color x = color y) : x = y := by
  rcases (hcycles x y).mp hcoordinate.symm with rfl | hy | hy
  · rfl
  · subst y
    exfalso
    apply zmod_three_add_one_ne (color x)
    calc
      color x + 1 = color (tau x) := (hcolor x).symm
      _ = color x := hcolors.symm
  · subst y
    exfalso
    apply zmod_three_add_two_ne (color x)
    calc
      color x + 2 = color (tau (tau x)) := (color_twice tau color hcolor x).symm
      _ = color x := hcolors.symm

/-- Every requested colour occurs in every coordinate fibre. -/
theorem exists_color_in_fiber
    (coordinate : D → A) (tau : Equiv.Perm D) (color : D → ZMod 3)
    (hcycles : CyclesFibers coordinate tau)
    (hcolor : ∀ x, color (tau x) = color x + 1)
    (hsurjective : Function.Surjective coordinate) (a : A) (i : ZMod 3) :
    ∃ x, coordinate x = a ∧ color x = i := by
  obtain ⟨x, hx⟩ := hsurjective a
  rcases zmod_three_cases (color x) i with hi | hi | hi
  · exact ⟨x, hx, hi.symm⟩
  · refine ⟨tau x, ?_, ?_⟩
    · exact ((hcycles x (tau x)).mpr (Or.inr (Or.inl rfl))).trans hx
    · exact (hcolor x).trans hi.symm
  · refine ⟨tau (tau x), ?_, ?_⟩
    · exact ((hcycles x (tau (tau x))).mpr (Or.inr (Or.inr rfl))).trans hx
    · exact (color_twice tau color hcolor x).trans hi.symm

/-- A colour class meets each coordinate fibre in a singleton. -/
theorem color_class_fiber_card
    [Fintype D] [DecidableEq D] [DecidableEq A]
    (coordinate : D → A) (tau : Equiv.Perm D) (color : D → ZMod 3)
    (hcycles : CyclesFibers coordinate tau)
    (hcolor : ∀ x, color (tau x) = color x + 1)
    (hsurjective : Function.Surjective coordinate) (a : A) (i : ZMod 3) :
    ((Finset.univ.filter fun x => color x = i).filter fun x => coordinate x = a).card = 1 := by
  obtain ⟨x, hxCoordinate, hxColor⟩ :=
    exists_color_in_fiber coordinate tau color hcycles hcolor hsurjective a i
  have heq :
      (Finset.univ.filter fun y => color y = i).filter (fun y => coordinate y = a) = {x} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hyColor, hyCoordinate⟩
      exact (color_injective_on_fiber coordinate tau color hcycles hcolor
        (hxCoordinate.trans hyCoordinate.symm) (hxColor.trans hyColor.symm)).symm
    · rintro rfl
      exact ⟨hxColor, hxCoordinate⟩
  rw [heq, Finset.card_singleton]

/-- Symmetric transversal condition on an abstract dart set: each row,
column, and symbol fibre is met exactly once. -/
def IsCoordinateTransversal
    [Fintype D] [DecidableEq A]
    {B C : Type*} [DecidableEq B] [DecidableEq C]
    (row : D → A) (column : D → B) (symbol : D → C) (X : Finset D) : Prop :=
  (∀ r, (X.filter fun x => row x = r).card = 1) ∧
  (∀ c, (X.filter fun x => column x = c).card = 1) ∧
  (∀ s, (X.filter fun x => symbol x = s).card = 1)

/-- A partition of all darts into three symmetric coordinate transversals. -/
def IsThreeCoordinatePartition
    [Fintype D] [DecidableEq D] [DecidableEq A]
    {B C : Type*} [DecidableEq B] [DecidableEq C]
    (row : D → A) (column : D → B) (symbol : D → C)
    (X₀ X₁ X₂ : Finset D) : Prop :=
  IsCoordinateTransversal row column symbol X₀ ∧
  IsCoordinateTransversal row column symbol X₁ ∧
  IsCoordinateTransversal row column symbol X₂ ∧
  X₀ ∩ X₁ = ∅ ∧ X₀ ∩ X₂ = ∅ ∧ X₁ ∩ X₂ = ∅ ∧
  X₀ ∪ X₁ ∪ X₂ = Finset.univ

/-- Universal permutation form of Theorem 1.1.  These are precisely the
properties supplied by the three permutations associated to a
3-homogeneous bitrade. -/
theorem three_homogeneous_permutation_partition
    [Fintype D] [DecidableEq D]
    {B C : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (row : D → A) (column : D → B) (symbol : D → C)
    (tauRow tauColumn tauSymbol : Equiv.Perm D)
    (hrowPreserves : ∀ x, row (tauRow x) = row x)
    (hcolumnPreserves : ∀ x, column (tauColumn x) = column x)
    (hsymbolPreserves : ∀ x, symbol (tauSymbol x) = symbol x)
    (hrowCard : ∀ r, (Finset.univ.filter fun x => row x = r).card = 3)
    (hcolumnCard : ∀ c, (Finset.univ.filter fun x => column x = c).card = 3)
    (hsymbolCard : ∀ s, (Finset.univ.filter fun x => symbol x = s).card = 3)
    (hrowThree : tauRow ^ 3 = 1)
    (hcolumnThree : tauColumn ^ 3 = 1)
    (hsymbolThree : tauSymbol ^ 3 = 1)
    (hproduct : tauSymbol * tauColumn * tauRow = 1)
    (hrowFree : ∀ x, tauRow x ≠ x)
    (hcolumnFree : ∀ x, tauColumn x ≠ x)
    (hsymbolFree : ∀ x, tauSymbol x ≠ x) :
    ∃ X₀ X₁ X₂,
      IsThreeCoordinatePartition row column symbol X₀ X₁ X₂ := by
  obtain ⟨color, hcolorSymbol, hcolorColumn, hcolorRow⟩ :=
    EuclideanTriangleGroup.permutations_admit_three_coloring
      tauSymbol tauColumn tauRow hsymbolThree hcolumnThree hrowThree hproduct
      hsymbolFree hcolumnFree hrowFree
  let X₀ := Finset.univ.filter fun x => color x = 0
  let X₁ := Finset.univ.filter fun x => color x = 1
  let X₂ := Finset.univ.filter fun x => color x = 2
  have hrowCycles : CyclesFibers row tauRow :=
    cyclesFibers_of_card_three row tauRow hrowPreserves hrowCard
      (fun x => by
        have h := congrArg (fun p : Equiv.Perm D => p x) hrowThree
        simpa [pow_succ, Equiv.Perm.mul_apply] using h)
      hrowFree
  have hcolumnCycles : CyclesFibers column tauColumn :=
    cyclesFibers_of_card_three column tauColumn hcolumnPreserves hcolumnCard
      (fun x => by
        have h := congrArg (fun p : Equiv.Perm D => p x) hcolumnThree
        simpa [pow_succ, Equiv.Perm.mul_apply] using h)
      hcolumnFree
  have hsymbolCycles : CyclesFibers symbol tauSymbol :=
    cyclesFibers_of_card_three symbol tauSymbol hsymbolPreserves hsymbolCard
      (fun x => by
        have h := congrArg (fun p : Equiv.Perm D => p x) hsymbolThree
        simpa [pow_succ, Equiv.Perm.mul_apply] using h)
      hsymbolFree
  have hrowSurjective := coordinate_surjective_of_card_three row hrowCard
  have hcolumnSurjective := coordinate_surjective_of_card_three column hcolumnCard
  have hsymbolSurjective := coordinate_surjective_of_card_three symbol hsymbolCard
  have htransversal (i : ZMod 3) :
      IsCoordinateTransversal row column symbol
        (Finset.univ.filter fun x => color x = i) := by
    refine ⟨?_, ?_, ?_⟩
    · intro r
      exact color_class_fiber_card row tauRow color hrowCycles hcolorRow
        hrowSurjective r i
    · intro c
      exact color_class_fiber_card column tauColumn color hcolumnCycles hcolorColumn
        hcolumnSurjective c i
    · intro s
      exact color_class_fiber_card symbol tauSymbol color hsymbolCycles hcolorSymbol
        hsymbolSurjective s i
  refine ⟨X₀, X₁, X₂, htransversal 0, htransversal 1, htransversal 2, ?_, ?_, ?_, ?_⟩
  · ext x
    simp [X₀, X₁]
    intro hzero hone
    exact (by decide : (0 : ZMod 3) ≠ 1) (hzero.symm.trans hone)
  · ext x
    simp [X₀, X₂]
    intro hzero htwo
    exact (by decide : (0 : ZMod 3) ≠ 2) (hzero.symm.trans htwo)
  · ext x
    simp [X₁, X₂]
    intro hone htwo
    exact (by decide : (1 : ZMod 3) ≠ 2) (hone.symm.trans htwo)
  · ext x
    simp only [X₀, X₁, X₂, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rcases zmod_three_cases 0 (color x) with h | h | h
    · simp [h]
    · simp at h
      simp [h]
    · simp at h
      simp [h]

section Entries

variable {Row Column Symbol : Type*}
variable [Fintype Row] [Fintype Column] [Fintype Symbol]
variable [DecidableEq Row] [DecidableEq Column] [DecidableEq Symbol]

/-- The positive entries of a partial Latin square, used as the dart type. -/
abbrev Darts (T : Finset (Entry Row Column Symbol)) :=
  {e : Entry Row Column Symbol // e ∈ T}

/-- Forget membership evidence and regard a set of darts as a set of entries. -/
def forgetDarts {T : Finset (Entry Row Column Symbol)} (X : Finset (Darts T)) :
    Finset (Entry Row Column Symbol) :=
  X.map (Function.Embedding.subtype _)

omit [Fintype Row] [Fintype Column] [Fintype Symbol]
    [DecidableEq Row] [DecidableEq Column] [DecidableEq Symbol] in
@[simp] theorem forgetDarts_univ {T : Finset (Entry Row Column Symbol)} :
    forgetDarts (Finset.univ : Finset (Darts T)) = T := by
  have huniv : (Finset.univ : Finset (Darts T)) = T.attach := by ext; simp
  rw [forgetDarts, huniv, Finset.attach_map_val]

omit [Fintype Row] [Fintype Column] [Fintype Symbol]
    [DecidableEq Row] [DecidableEq Column] [DecidableEq Symbol] in
theorem forgetDarts_subset
    {T : Finset (Entry Row Column Symbol)} (X : Finset (Darts T)) :
    forgetDarts X ⊆ T := by
  intro e he
  rw [forgetDarts, Finset.mem_map] at he
  obtain ⟨x, -, rfl⟩ := he
  exact x.property

omit [Fintype Row] [Fintype Column] [Fintype Symbol]
    [DecidableEq Row] [DecidableEq Column] [DecidableEq Symbol] in
theorem forgetDarts_filter_card
    {T : Finset (Entry Row Column Symbol)} (X : Finset (Darts T))
    {K : Type*} [DecidableEq K]
    (coordinate : Entry Row Column Symbol → K) (k : K) :
    ((forgetDarts X).filter fun e => coordinate e = k).card =
      (X.filter fun x : Darts T => coordinate x.val = k).card := by
  rw [forgetDarts, Finset.filter_map, Finset.card_map]
  rfl

private theorem coordinate_injective_of_fiber_card_one
    {K : Type*} [DecidableEq K] {E : Type*} [DecidableEq E]
    (coordinate : E → K) (X : Finset E)
    (hcard : ∀ k, (X.filter fun x => coordinate x = k).card = 1) :
    Set.InjOn coordinate X := by
  intro x hx y hy hxy
  have hxFin : x ∈ X := hx
  have hyFin : y ∈ X := hy
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp (hcard (coordinate x))
  have hxz : x = z := by
    have : x ∈ X.filter (fun w => coordinate w = coordinate x) := by simp [hxFin]
    rw [hz] at this
    simpa using this
  have hyz : y = z := by
    have : y ∈ X.filter (fun w => coordinate w = coordinate x) := by
      simp [hyFin, hxy]
    rw [hz] at this
    simpa using this
  exact hxz.trans hyz.symm

omit [Fintype Symbol] in
/-- A symmetric transversal of the dart subtype becomes a transversal in
the paper's original finset-of-entries formulation. -/
theorem forgetDarts_isTransversal
    {T : Finset (Entry Row Column Symbol)} {X : Finset (Darts T)}
    (hX : IsCoordinateTransversal
      (fun x : Darts T => x.val.row)
      (fun x : Darts T => x.val.column)
      (fun x : Darts T => x.val.symbol) X) :
    IsTransversal T (forgetDarts X) := by
  rcases hX with ⟨hrows, hcolumns, hsymbols⟩
  refine ⟨forgetDarts_subset X, ?_, ?_, ?_⟩
  · apply Finset.filter_eq_empty_iff.mpr
    intro r _ hne
    apply hne
    rw [forgetDarts_filter_card]
    exact hrows r
  · apply Finset.filter_eq_empty_iff.mpr
    intro c _ hne
    apply hne
    rw [forgetDarts_filter_card]
    exact hcolumns c
  · apply Finset.card_image_iff.mpr
    have hinjDart : Set.InjOn (fun x : Darts T => x.val.symbol) X :=
      coordinate_injective_of_fiber_card_one _ X hsymbols
    intro e he f hf hef
    have heFin : e ∈ forgetDarts X := he
    have hfFin : f ∈ forgetDarts X := hf
    rw [forgetDarts, Finset.mem_map] at heFin hfFin
    obtain ⟨x, hx, rfl⟩ := heFin
    obtain ⟨y, hy, rfl⟩ := hfFin
    exact congrArg Subtype.val (hinjDart hx hy hef)

omit [Fintype Symbol] in
/-- Transfer an abstract dart partition back to the exact conclusion type
used for Theorem 1.1. -/
theorem coordinatePartition_isThreeTransversalPartition
    {T : Finset (Entry Row Column Symbol)} {X₀ X₁ X₂ : Finset (Darts T)}
    (hpartition : IsThreeCoordinatePartition
      (fun x : Darts T => x.val.row)
      (fun x : Darts T => x.val.column)
      (fun x : Darts T => x.val.symbol) X₀ X₁ X₂) :
    IsThreeTransversalPartition T (forgetDarts X₀) (forgetDarts X₁) (forgetDarts X₂) := by
  rcases hpartition with ⟨h₀, h₁, h₂, h₀₁, h₀₂, h₁₂, hcover⟩
  refine ⟨forgetDarts_isTransversal h₀, forgetDarts_isTransversal h₁,
    forgetDarts_isTransversal h₂, ?_, ?_, ?_, ?_⟩
  · simp only [forgetDarts]
    rw [← Finset.map_inter, h₀₁]
    rfl
  · simp only [forgetDarts]
    rw [← Finset.map_inter, h₀₂]
    rfl
  · simp only [forgetDarts]
    rw [← Finset.map_inter, h₁₂]
    rfl
  · simp only [forgetDarts]
    rw [← Finset.map_union, ← Finset.map_union, hcover]
    rw [show (Finset.univ : Finset (Darts T)) = T.attach by ext; simp,
      Finset.attach_map_val]

/-- The finset definition of 3-homogeneity gives the corresponding cardinal
statements on the dart subtype. -/
theorem homogeneous_three_dart_cards
    {T : Finset (Entry Row Column Symbol)} (hhom : IsKHomogeneous 3 T) :
    (∀ r, (Finset.univ.filter fun x : Darts T => x.val.row = r).card = 3) ∧
    (∀ c, (Finset.univ.filter fun x : Darts T => x.val.column = c).card = 3) ∧
    (∀ s, (Finset.univ.filter fun x : Darts T => x.val.symbol = s).card = 3) := by
  rcases hhom with ⟨hrows, hcolumns, hsymbols⟩
  refine ⟨?_, ?_, ?_⟩
  · intro r
    have hr : (T.filter fun e => e.row = r).card = 3 := by
      exact not_ne_iff.mp ((Finset.filter_eq_empty_iff.mp hrows) (Finset.mem_univ r))
    rw [← forgetDarts_filter_card (X := (Finset.univ : Finset (Darts T)))
      (fun e => e.row) r, forgetDarts_univ]
    exact hr
  · intro c
    have hc : (T.filter fun e => e.column = c).card = 3 := by
      exact not_ne_iff.mp ((Finset.filter_eq_empty_iff.mp hcolumns) (Finset.mem_univ c))
    rw [← forgetDarts_filter_card (X := (Finset.univ : Finset (Darts T)))
      (fun e => e.column) c, forgetDarts_univ]
    exact hc
  · intro s
    have hs : (T.filter fun e => e.symbol = s).card = 3 := by
      exact not_ne_iff.mp ((Finset.filter_eq_empty_iff.mp hsymbols) (Finset.mem_univ s))
    rw [← forgetDarts_filter_card (X := (Finset.univ : Finset (Darts T)))
      (fun e => e.symbol) s, forgetDarts_univ]
    exact hs

/-- End-to-end conclusion from the canonical permutation certificate of a
3-homogeneous bitrade.  The remaining interface theorem is that the mate
maps of `IsBitrade` supply exactly this certificate. -/
theorem exists_three_transversal_partition_from_permutations
    (T : Finset (Entry Row Column Symbol))
    (tauRow tauColumn tauSymbol : Equiv.Perm (Darts T))
    (hhom : IsKHomogeneous 3 T)
    (hrowPreserves : ∀ x, (tauRow x).val.row = x.val.row)
    (hcolumnPreserves : ∀ x, (tauColumn x).val.column = x.val.column)
    (hsymbolPreserves : ∀ x, (tauSymbol x).val.symbol = x.val.symbol)
    (hrowThree : tauRow ^ 3 = 1)
    (hcolumnThree : tauColumn ^ 3 = 1)
    (hsymbolThree : tauSymbol ^ 3 = 1)
    (hproduct : tauSymbol * tauColumn * tauRow = 1)
    (hrowFree : ∀ x, tauRow x ≠ x)
    (hcolumnFree : ∀ x, tauColumn x ≠ x)
    (hsymbolFree : ∀ x, tauSymbol x ≠ x) :
    ∃ T₀ T₁ T₂, IsThreeTransversalPartition T T₀ T₁ T₂ := by
  obtain ⟨hrowCard, hcolumnCard, hsymbolCard⟩ := homogeneous_three_dart_cards hhom
  obtain ⟨X₀, X₁, X₂, hpartition⟩ :=
    three_homogeneous_permutation_partition
      (fun x : Darts T => x.val.row)
      (fun x : Darts T => x.val.column)
      (fun x : Darts T => x.val.symbol)
      tauRow tauColumn tauSymbol
      hrowPreserves hcolumnPreserves hsymbolPreserves
      hrowCard hcolumnCard hsymbolCard
      hrowThree hcolumnThree hsymbolThree hproduct
      hrowFree hcolumnFree hsymbolFree
  exact ⟨forgetDarts X₀, forgetDarts X₁, forgetDarts X₂,
    coordinatePartition_isThreeTransversalPartition hpartition⟩

end Entries

end LatinBitrade
