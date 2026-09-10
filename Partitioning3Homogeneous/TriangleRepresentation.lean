import Partitioning3Homogeneous.TriangleGroup

/-!
# Representations of the Euclidean triangle group

The three permutations attached to a 3-homogeneous bitrade have order three
and product one.  This file proves algebraically that every such triple is a
representation of `EuclideanTriangleGroup.TriangleGroup`.
-/

namespace EuclideanTriangleGroup

section Relations

variable {G : Type*} [Group G]
variable (a b c : G)

/-- Translation corresponding to the first lattice basis vector. -/
def firstTranslation : G := b * a⁻¹

/-- Translation corresponding to the second lattice basis vector. -/
def secondTranslation : G := a * firstTranslation a b * a⁻¹

theorem generator_relations_force_translations_commute
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hc : c ^ 3 = 1)
    (habc : a * b * c = 1) :
    Commute (firstTranslation a b) (secondTranslation a b) := by
  let u := firstTranslation a b
  let v := secondTranslation a b
  have hv : v = a * u * a⁻¹ := by
    rfl
  have haInv : a⁻¹ = a ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    simpa [pow_succ, pow_two, mul_assoc] using ha
  have hbInv : b⁻¹ = b ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    simpa [pow_succ, pow_two, mul_assoc] using hb
  have haFive : a ^ 5 = a ^ 2 := by
    rw [show (5 : ℕ) = 2 + 3 by norm_num, pow_add, ha, mul_one]
  have hbForm : b = u * a := by
    dsimp [u, firstTranslation]
    group
  have hcForm : c = u * v * a := by
    have hcInv : c = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right habc
    rw [hcInv]
    dsimp [u, v, firstTranslation, secondTranslation]
    rw [mul_inv_rev, haInv, hbInv]
    group
    simp only [zpow_ofNat]
    rw [ha, haFive]
    simp only [pow_two]
    simp
  have huvCycle : u * v * (a * v * a⁻¹) = 1 := by
    calc
      u * v * (a * v * a⁻¹) = (u * a) ^ 3 * (a ^ 3)⁻¹ := by
        rw [hv]
        simp only [pow_succ]
        group
      _ = 1 := by rw [← hbForm, hb, ha]; simp
  have hrotateV : a * v * a⁻¹ = v⁻¹ * u⁻¹ := by
    calc
      a * v * a⁻¹ = (u * v)⁻¹ := eq_inv_of_mul_eq_one_right huvCycle
      _ = v⁻¹ * u⁻¹ := mul_inv_rev u v
  have hrotateUV : a * (u * v) * a⁻¹ = u⁻¹ := by
    calc
      a * (u * v) * a⁻¹ = (a * u * a⁻¹) * (a * v * a⁻¹) := by group
      _ = v * (v⁻¹ * u⁻¹) := by rw [← hv, hrotateV]
      _ = u⁻¹ := by group
  have hrotateTwiceUV : a ^ 2 * (u * v) * (a ^ 2)⁻¹ = v⁻¹ := by
    calc
      a ^ 2 * (u * v) * (a ^ 2)⁻¹ = a * (a * (u * v) * a⁻¹) * a⁻¹ := by
        simp only [pow_two]
        group
      _ = a * u⁻¹ * a⁻¹ := by rw [hrotateUV]
      _ = v⁻¹ := by
        rw [hv]
        group
  have hcommutator : u * v * u⁻¹ * v⁻¹ = 1 := by
    calc
      u * v * u⁻¹ * v⁻¹ = (u * v * a) ^ 3 * (a ^ 3)⁻¹ := by
        rw [show u⁻¹ = a * (u * v) * a⁻¹ from hrotateUV.symm]
        rw [show v⁻¹ = a ^ 2 * (u * v) * (a ^ 2)⁻¹ from hrotateTwiceUV.symm]
        simp only [pow_succ]
        group
      _ = 1 := by rw [← hcForm, hc, ha]; simp
  rw [commute_iff_eq]
  calc
    u * v = (u * v * u⁻¹ * v⁻¹) * (v * u) := by group
    _ = v * u := by rw [hcommutator, one_mul]

end Relations

section Extension

variable {G : Type*} [Group G]

/-- A commuting pair determines a homomorphism from the translation lattice. -/
def translationHom (u v : G) (huv : Commute u v) : Translation →* G where
  toFun x := u ^ x.toAdd.1 * v ^ x.toAdd.2
  map_one' := by simp
  map_mul' x y := by
    change u ^ (x.toAdd.1 + y.toAdd.1) * v ^ (x.toAdd.2 + y.toAdd.2) =
      (u ^ x.toAdd.1 * v ^ x.toAdd.2) * (u ^ y.toAdd.1 * v ^ y.toAdd.2)
    rw [zpow_add, zpow_add]
    calc
      (u ^ x.toAdd.1 * u ^ y.toAdd.1) * (v ^ x.toAdd.2 * v ^ y.toAdd.2) =
          u ^ x.toAdd.1 * (u ^ y.toAdd.1 * v ^ x.toAdd.2) * v ^ y.toAdd.2 := by
            group
      _ = u ^ x.toAdd.1 * (v ^ x.toAdd.2 * u ^ y.toAdd.1) * v ^ y.toAdd.2 := by
        rw [(huv.zpow_zpow y.toAdd.1 x.toAdd.2).eq]
      _ = (u ^ x.toAdd.1 * v ^ x.toAdd.2) *
          (u ^ y.toAdd.1 * v ^ y.toAdd.2) := by group

@[simp] theorem translationHom_apply (u v : G) (huv : Commute u v) (m n : ℤ) :
    translationHom u v huv (Multiplicative.ofAdd (m, n)) = u ^ m * v ^ n := rfl

/-- An element of order dividing three determines a homomorphism from the
cyclic rotation factor. -/
def rotationHom (a : G) (ha : a ^ 3 = 1) : Rotation →* G where
  toFun k := a ^ k.toAdd.val
  map_one' := by simp
  map_mul' x y := by
    change a ^ (x.toAdd + y.toAdd).val = a ^ x.toAdd.val * a ^ y.toAdd.val
    rw [ZMod.val_add]
    rw [← pow_eq_pow_mod (x.toAdd.val + y.toAdd.val) ha]
    rw [pow_add]

@[simp] theorem rotationHom_one (a : G) (ha : a ^ 3 = 1) :
    rotationHom a ha (Multiplicative.ofAdd (1 : ZMod 3)) = a := by
  change a ^ (1 : ZMod 3).val = a
  rw [ZMod.val_one, pow_one]

/-- The order-three relation for the second generator determines how the
rotation acts on the second translation. -/
theorem conjugate_secondTranslation
    (a b : G) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    a * secondTranslation a b * a⁻¹ =
      (firstTranslation a b * secondTranslation a b)⁻¹ := by
  let u := firstTranslation a b
  let v := secondTranslation a b
  have hv : v = a * u * a⁻¹ := rfl
  have hbForm : b = u * a := by
    dsimp [u, firstTranslation]
    group
  have huvCycle : u * v * (a * v * a⁻¹) = 1 := by
    calc
      u * v * (a * v * a⁻¹) = (u * a) ^ 3 * (a ^ 3)⁻¹ := by
        rw [hv]
        simp only [pow_succ]
        group
      _ = 1 := by rw [← hbForm, hb, ha]; simp
  exact eq_inv_of_mul_eq_one_right huvCycle

/-- Compatibility of the lattice map with one 120-degree rotation. -/
theorem translationHom_rotate_one
    (a b c : G)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hc : c ^ 3 = 1)
    (habc : a * b * c = 1) (x : Translation) :
    let u := firstTranslation a b
    let v := secondTranslation a b
    let huv := generator_relations_force_translations_commute a b c ha hb hc habc
    translationHom u v huv
        (rotationAction (Multiplicative.ofAdd (1 : ZMod 3)) x) =
      a * translationHom u v huv x * a⁻¹ := by
  dsimp only
  let u := firstTranslation a b
  let v := secondTranslation a b
  let huv := generator_relations_force_translations_commute a b c ha hb hc habc
  have huvLocal : Commute u v := huv
  change translationHom u v huv (rotationAction (Multiplicative.ofAdd (1 : ZMod 3)) x) =
    a * translationHom u v huv x * a⁻¹
  rw [rotationAction_one_apply]
  rcases x with ⟨m, n⟩
  change u ^ (-n) * v ^ (m - n) = a * (u ^ m * v ^ n) * a⁻¹
  have hv : v = a * u * a⁻¹ := rfl
  have hrotateV : a * v * a⁻¹ = u⁻¹ * v⁻¹ := by
    rw [conjugate_secondTranslation a b ha hb]
    exact huvLocal.mul_inv
  calc
    u ^ (-n) * v ^ (m - n) = v ^ m * (u⁻¹ * v⁻¹) ^ n := by
      rw [huvLocal.inv_inv.mul_zpow, inv_zpow', inv_zpow']
      calc
        u ^ (-n) * v ^ (m - n) = u ^ (-n) * (v ^ m * v ^ (-n)) := by
          rw [← zpow_add]
          congr 2
        _ = (u ^ (-n) * v ^ m) * v ^ (-n) := by group
        _ = (v ^ m * u ^ (-n)) * v ^ (-n) := by
          rw [(huvLocal.zpow_zpow (-n) m).eq]
        _ = v ^ m * (u ^ (-n) * v ^ (-n)) := by group
    _ = (a * u * a⁻¹) ^ m * (a * v * a⁻¹) ^ n := by
      rw [← hv, hrotateV]
    _ = a * (u ^ m * v ^ n) * a⁻¹ := by
      have hconjU : (a * u * a⁻¹) ^ m = a * u ^ m * a⁻¹ := by
        simpa only [MulAut.conj_apply] using (map_zpow (MulAut.conj a) u m).symm
      have hconjV : (a * v * a⁻¹) ^ n = a * v ^ n * a⁻¹ := by
        simpa only [MulAut.conj_apply] using (map_zpow (MulAut.conj a) v n).symm
      rw [hconjU, hconjV]
      group

/-- Compatibility with every element of the cyclic rotation factor follows
by iterating compatibility with its generator. -/
theorem translationHom_rotation_compatible
    (a b c : G)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hc : c ^ 3 = 1)
    (habc : a * b * c = 1) (k : Rotation) (x : Translation) :
    let u := firstTranslation a b
    let v := secondTranslation a b
    let huv := generator_relations_force_translations_commute a b c ha hb hc habc
    translationHom u v huv (rotationAction k x) =
      rotationHom a ha k * translationHom u v huv x * (rotationHom a ha k)⁻¹ := by
  dsimp only
  let u := firstTranslation a b
  let v := secondTranslation a b
  let huv := generator_relations_force_translations_commute a b c ha hb hc habc
  let fn := translationHom u v huv
  have hone (y : Translation) : fn (rotateMul y) = a * fn y * a⁻¹ := by
    simpa only [fn, rotationAction_one_apply] using
      translationHom_rotate_one a b c ha hb hc habc y
  have hiterate : ∀ r : ℕ, ∀ y : Translation,
      fn ((rotateMul ^ r) y) = a ^ r * fn y * (a ^ r)⁻¹ := by
    intro r
    induction r with
    | zero => intro y; simp
    | succ r ih =>
        intro y
        calc
          fn ((rotateMul ^ (r + 1)) y) = fn (rotateMul ((rotateMul ^ r) y)) := by
            rw [pow_succ']
            rfl
          _ = a * fn ((rotateMul ^ r) y) * a⁻¹ := hone _
          _ = a * (a ^ r * fn y * (a ^ r)⁻¹) * a⁻¹ := by rw [ih]
          _ = a ^ (r + 1) * fn y * (a ^ (r + 1))⁻¹ := by
            rw [pow_succ']
            group
  exact hiterate k.toAdd.val x

/-- The representation of the concrete Euclidean triangle group determined
by any triple satisfying the four triangle-group relations. -/
def triangleRepresentation
    (a b c : G)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hc : c ^ 3 = 1)
    (habc : a * b * c = 1) : TriangleGroup →* G :=
  let u := firstTranslation a b
  let v := secondTranslation a b
  let huv := generator_relations_force_translations_commute a b c ha hb hc habc
  SemidirectProduct.lift (translationHom u v huv) (rotationHom a ha) (by
    intro k
    ext x
    change translationHom u v huv (rotationAction k x) =
      rotationHom a ha k * translationHom u v huv x * (rotationHom a ha k)⁻¹
    exact translationHom_rotation_compatible a b c ha hb hc habc k x)

@[simp] theorem triangleRepresentation_rho₁
    (a b c : G)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hc : c ^ 3 = 1)
    (habc : a * b * c = 1) :
    triangleRepresentation a b c ha hb hc habc rho₁ = a := by
  simp [triangleRepresentation, rho₁, rotation]

@[simp] theorem triangleRepresentation_rho₂
    (a b c : G)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hc : c ^ 3 = 1)
    (habc : a * b * c = 1) :
    triangleRepresentation a b c ha hb hc habc rho₂ = b := by
  simp [triangleRepresentation, rho₂, rho₁, rotation, translation,
    firstTranslation]

@[simp] theorem triangleRepresentation_rho₃
    (a b c : G)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hc : c ^ 3 = 1)
    (habc : a * b * c = 1) :
    triangleRepresentation a b c ha hb hc habc rho₃ = c := by
  let theta := triangleRepresentation a b c ha hb hc habc
  have htriangle : rho₁ * rho₂ * rho₃ = 1 := rho_relations.2.2.2
  have hmap := congrArg theta htriangle
  simp only [map_mul, map_one] at hmap
  rw [triangleRepresentation_rho₁, triangleRepresentation_rho₂] at hmap
  calc
    theta rho₃ = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right hmap
    _ = c := (eq_inv_of_mul_eq_one_right habc).symm

end Extension

end EuclideanTriangleGroup
