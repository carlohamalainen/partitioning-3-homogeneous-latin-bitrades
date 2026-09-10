import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic

/-!
# The Euclidean triangle group `(3,3,3)`

An algebraic model of the orientation-preserving symmetry group used in
Section 4: translations of the triangular lattice, extended by a rotation of
order three. Keeping this model integral avoids formalizing Euclidean square
roots and metric geometry.
-/

namespace EuclideanTriangleGroup

/-- Integer coordinates for the triangular lattice. -/
abbrev Lattice := ℤ × ℤ

/-- Rotation through 120 degrees in triangular-lattice coordinates. -/
def rotate : Lattice ≃+ Lattice where
  toFun p := (-p.2, p.1 - p.2)
  invFun p := (p.2 - p.1, -p.1)
  left_inv p := by rcases p with ⟨m, n⟩; simp
  right_inv p := by rcases p with ⟨m, n⟩; simp
  map_add' p q := by
    rcases p with ⟨m, n⟩
    rcases q with ⟨m', n'⟩
    simp
    constructor <;> ring

abbrev Translation := Multiplicative Lattice

/-- The same rotation, as an automorphism of the multiplicative type synonym
used by `SemidirectProduct`. -/
def rotateMul : MulAut Translation :=
  AddEquiv.toMultiplicative rotate

theorem rotate_three (p : Lattice) : rotate (rotate (rotate p)) = p := by
  rcases p with ⟨m, n⟩
  apply Prod.ext
  · simp [rotate]
  · simp [rotate]
    ring

theorem rotateMul_three : rotateMul ^ 3 = 1 := by
  apply MulEquiv.ext
  intro p
  change Multiplicative.ofAdd (rotate (rotate (rotate p.toAdd))) = p
  simpa using congrArg Multiplicative.ofAdd (rotate_three p.toAdd)

/-- The cyclic group of rotations. -/
abbrev Rotation := Multiplicative (ZMod 3)

/-- Exhaustion of the three elements of the rotation factor. -/
theorem rotation_cases (k : Rotation) :
    k = 1 ∨
    k = Multiplicative.ofAdd (1 : ZMod 3) ∨
    k = Multiplicative.ofAdd (2 : ZMod 3) := by
  revert k
  decide

/-- A rotation class acts on translations by the corresponding power of
`rotateMul`. -/
def rotationAction : Rotation →* MulAut Translation where
  toFun k := rotateMul ^ k.toAdd.val
  map_one' := by simp
  map_mul' a b := by
    change rotateMul ^ (a.toAdd + b.toAdd).val =
      rotateMul ^ a.toAdd.val * rotateMul ^ b.toAdd.val
    rw [ZMod.val_add]
    rw [← pow_eq_pow_mod (a.toAdd.val + b.toAdd.val) rotateMul_three]
    rw [pow_add]

@[simp]
theorem rotationAction_one_apply (p : Translation) :
    rotationAction (Multiplicative.ofAdd (1 : ZMod 3)) p = rotateMul p := by
  change (rotateMul ^ (1 : ZMod 3).val) p = rotateMul p
  rw [ZMod.val_one]
  rfl

/-- Concrete algebraic model of the `(3,3,3)` triangle group. -/
abbrev TriangleGroup := Translation ⋊[rotationAction] Rotation

/-- A pure translation. -/
def translation (m n : ℤ) : TriangleGroup :=
  SemidirectProduct.inl (Multiplicative.ofAdd (m, n))

@[simp]
theorem translation_inv (m n : ℤ) :
    (translation m n)⁻¹ = translation (-m) (-n) := by
  ext <;> simp [translation]

/-- A pure rotation class. -/
def rotation (k : ZMod 3) : TriangleGroup :=
  SemidirectProduct.inr (Multiplicative.ofAdd k)

/-- An affine rotation whose rotational component is one. -/
def affineRotation (m n : ℤ) : TriangleGroup :=
  ⟨Multiplicative.ofAdd (m, n), Multiplicative.ofAdd (1 : ZMod 3)⟩

/-- Rotation about a vertex of the first type. -/
def rho₁ : TriangleGroup := rotation 1

/-- Rotation about a vertex of the second type. -/
def rho₂ : TriangleGroup := translation 1 0 * rho₁

/-- Rotation about a vertex of the third type. -/
def rho₃ : TriangleGroup := translation 1 1 * rho₁

@[simp] theorem rho₁_coordinates : rho₁ = affineRotation 0 0 := by
  decide

@[simp] theorem rho₂_coordinates : rho₂ = affineRotation 1 0 := by
  decide

@[simp] theorem rho₃_coordinates : rho₃ = affineRotation 1 1 := by
  decide

/-- The defining `(3,3,3)` relations, checked in the integral affine model. -/
theorem rho_relations :
    rho₁ ^ 3 = 1 ∧ rho₂ ^ 3 = 1 ∧ rho₃ ^ 3 = 1 ∧ rho₁ * rho₂ * rho₃ = 1 := by
  decide

set_option maxRecDepth 10000 in
/-- Conjugating a rotation by a translation changes its centre by an
index-three sublattice. This formula replaces the distance calculations in
the paper by integer arithmetic. -/
theorem conjugate_rotation_one (m n p q : ℤ) :
    translation p q * affineRotation m n *
        (translation p q)⁻¹ =
      affineRotation (m + p + q) (n + 2 * q - p) := by
  rw [translation_inv]
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      translation, affineRotation, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      map_one, MulAut.one_apply, one_mul, rotationAction_one_apply]
    change ((p, q) : Lattice) + (m, n) + rotate (-p, -q) =
      (m + p + q, n + 2 * q - p)
    simp only [rotate, AddEquiv.coe_mk, Equiv.coe_fn_mk, neg_neg]
    apply Prod.ext <;> simp <;> ring
  · simp [translation, affineRotation]

/-- Every element whose rotational component is one is conjugate, by a
translation, to one of the three vertex rotations. This is the
integer-lattice substitute for Cases 1--4 in the proof of Theorem 1.1. -/
theorem rotation_one_conjugate_generator (m n : ℤ) :
    ∃ p q : ℤ,
      translation p q * affineRotation m n * (translation p q)⁻¹ = rho₁ ∨
      translation p q * affineRotation m n * (translation p q)⁻¹ = rho₂ ∨
      translation p q * affineRotation m n * (translation p q)⁻¹ = rho₃ := by
  let z := m + n
  let q := -(z / 3)
  have hdiv : z / 3 * 3 + z % 3 = z := Int.ediv_mul_add_emod z 3
  have hnonneg : 0 ≤ z % 3 := Int.emod_nonneg z (by norm_num)
  have hlt : z % 3 < 3 := Int.emod_lt_of_pos z (by norm_num)
  have hcases : z % 3 = 0 ∨ z % 3 = 1 ∨ z % 3 = 2 := by omega
  rcases hcases with hzero | hone | htwo
  · refine ⟨-m - q, q, Or.inl ?_⟩
    rw [conjugate_rotation_one, rho₁_coordinates]
    congr 1 <;> dsimp [q, z] at * <;> omega
  · refine ⟨1 - m - q, q, Or.inr (Or.inl ?_)⟩
    rw [conjugate_rotation_one, rho₂_coordinates]
    congr 1 <;> dsimp [q, z] at * <;> omega
  · refine ⟨1 - m - q, q, Or.inr (Or.inr ?_)⟩
    rw [conjugate_rotation_one, rho₃_coordinates]
    congr 1 <;> dsimp [q, z] at * <;> omega

end EuclideanTriangleGroup
