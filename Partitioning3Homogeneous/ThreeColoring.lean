import Partitioning3Homogeneous.OrbitMap
import Partitioning3Homogeneous.TriangleRepresentation
import Mathlib.Algebra.Group.Action.Hom
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Three-colouring triangle-group actions

The main geometric step of the paper is equivalent to the statement that a
fixed-point-free action of the three vertex rotations admits a colouring by
`ZMod 3`, and that every generator advances the colour by one.
-/

namespace EuclideanTriangleGroup

variable {D : Type*} [MulAction TriangleGroup D]

private theorem conjugate_fixes
    {g h r : TriangleGroup} {x : D}
    (hfix : g • x = x) (hconj : h * g * h⁻¹ = r) :
    r • (h • x) = h • x := by
  rw [← hconj]
  simp only [mul_smul, inv_smul_smul, hfix]

/-- An element with rotational component one cannot stabilize a point when
the three distinguished rotations are fixed-point-free. -/
theorem rotation_one_not_in_stabilizer
    (hfree₁ : ∀ x : D, rho₁ • x ≠ x)
    (hfree₂ : ∀ x : D, rho₂ • x ≠ x)
    (hfree₃ : ∀ x : D, rho₃ • x ≠ x)
    {g : TriangleGroup} {x : D}
    (hrotation : g.right = Multiplicative.ofAdd (1 : ZMod 3))
    (hfix : g • x = x) : False := by
  let m := g.left.toAdd.1
  let n := g.left.toAdd.2
  have hg : g = affineRotation m n := by
    apply SemidirectProduct.ext
    · change g.left.toAdd = (m, n)
      exact (Prod.eta g.left.toAdd).symm
    · exact hrotation
  obtain ⟨p, q, h₁ | h₂ | h₃⟩ := rotation_one_conjugate_generator m n
  · apply hfree₁ (translation p q • x)
    apply conjugate_fixes hfix
    simpa only [← hg] using h₁
  · apply hfree₂ (translation p q • x)
    apply conjugate_fixes hfix
    simpa only [← hg] using h₂
  · apply hfree₃ (translation p q • x)
    apply conjugate_fixes hfix
    simpa only [← hg] using h₃

/-- Fixed-point-freeness forces every point stabilizer into the translation
subgroup, i.e. into the kernel of the rotation-coordinate map. -/
theorem stabilizer_has_trivial_rotation
    (hfree₁ : ∀ x : D, rho₁ • x ≠ x)
    (hfree₂ : ∀ x : D, rho₂ • x ≠ x)
    (hfree₃ : ∀ x : D, rho₃ • x ≠ x)
    {g : TriangleGroup} {x : D} (hfix : g • x = x) :
    g.right = 1 := by
  rcases rotation_cases g.right with hzero | hone | htwo
  · exact hzero
  · exact False.elim
      (rotation_one_not_in_stabilizer hfree₁ hfree₂ hfree₃ hone hfix)
  · have hinverseRotation : g⁻¹.right = Multiplicative.ofAdd (1 : ZMod 3) := by
      rw [SemidirectProduct.inv_right, htwo]
      decide
    have hinverseFix : g⁻¹ • x = x := by
      calc
        g⁻¹ • x = g⁻¹ • (g • x) := congrArg (g⁻¹ • ·) hfix.symm
        _ = x := inv_smul_smul g x
    exact False.elim
      (rotation_one_not_in_stabilizer hfree₁ hfree₂ hfree₃
        hinverseRotation hinverseFix)

/-- On a transitive component, the rotation coordinate descends to a
three-colouring.  Each distinguished rotation advances the colour by one. -/
theorem exists_three_coloring_of_transitive
    (hfree₁ : ∀ x : D, rho₁ • x ≠ x)
    (hfree₂ : ∀ x : D, rho₂ • x ≠ x)
    (hfree₃ : ∀ x : D, rho₃ • x ≠ x)
    (x₀ : D) (htrans : EquivariantOrbitMap.IsTransitiveAt TriangleGroup x₀) :
    ∃ color : D → ZMod 3,
      (∀ x, color (rho₁ • x) = color x + 1) ∧
      (∀ x, color (rho₂ • x) = color x + 1) ∧
      (∀ x, color (rho₃ • x) = color x + 1) := by
  let projection : TriangleGroup →* Rotation := SemidirectProduct.rightHom
  have hstab : EquivariantOrbitMap.MapsStabilizer projection x₀ (1 : Rotation) := by
    intro g hfix
    have hright := stabilizer_has_trivial_rotation hfree₁ hfree₂ hfree₃ hfix
    change g.right • (1 : Rotation) = 1
    rw [hright]
    simp
  obtain ⟨psi, -, hpsi⟩ :=
    EquivariantOrbitMap.exists_equivariant projection x₀ (1 : Rotation) htrans hstab
  refine ⟨fun x => (psi x).toAdd, ?_, ?_, ?_⟩
  · intro x
    have h := hpsi rho₁ x
    change (psi (rho₁ • x)).toAdd = (psi x).toAdd + 1
    rw [h]
    change (rho₁.right * psi x).toAdd = (psi x).toAdd + 1
    simp [rho₁, rotation, add_comm]
  · intro x
    have h := hpsi rho₂ x
    change (psi (rho₂ • x)).toAdd = (psi x).toAdd + 1
    rw [h]
    change (rho₂.right * psi x).toAdd = (psi x).toAdd + 1
    simp [rho₂, rho₁, translation, rotation, add_comm]
  · intro x
    have h := hpsi rho₃ x
    change (psi (rho₃ • x)).toAdd = (psi x).toAdd + 1
    rw [h]
    change (rho₃.right * psi x).toAdd = (psi x).toAdd + 1
    simp [rho₃, rho₁, translation, rotation, add_comm]

/-- The componentwise form used for arbitrary (not necessarily primary)
bitrades.  Each orbit is coloured independently. -/
theorem exists_three_coloring
    (hfree₁ : ∀ x : D, rho₁ • x ≠ x)
    (hfree₂ : ∀ x : D, rho₂ • x ≠ x)
    (hfree₃ : ∀ x : D, rho₃ • x ≠ x) :
    ∃ color : D → ZMod 3,
      (∀ x, color (rho₁ • x) = color x + 1) ∧
      (∀ x, color (rho₂ • x) = color x + 1) ∧
      (∀ x, color (rho₃ • x) = color x + 1) := by
  classical
  have hcomponent (omega : MulAction.orbitRel.Quotient TriangleGroup D) :
      ∃ color : omega.orbit → ZMod 3,
        (∀ x, color (rho₁ • x) = color x + 1) ∧
        (∀ x, color (rho₂ • x) = color x + 1) ∧
        (∀ x, color (rho₃ • x) = color x + 1) := by
    let x₀ : omega.orbit := ⟨omega.nonempty_orbit.choose,
      omega.nonempty_orbit.choose_spec⟩
    refine exists_three_coloring_of_transitive ?_ ?_ ?_ x₀ ?_
    · intro x hx
      apply hfree₁ x.1
      simpa using congrArg Subtype.val hx
    · intro x hx
      apply hfree₂ x.1
      simpa using congrArg Subtype.val hx
    · intro x hx
      apply hfree₃ x.1
      simpa using congrArg Subtype.val hx
    · intro x
      exact MulAction.exists_smul_eq TriangleGroup x₀ x
  choose componentColor hcomponent_spec using hcomponent
  let extendedColor :
      (omega : MulAction.orbitRel.Quotient TriangleGroup D) → D → ZMod 3 :=
    fun omega x => if hx : x ∈ omega.orbit then componentColor omega ⟨x, hx⟩ else 0
  let color : D → ZMod 3 := fun x => extendedColor (Quotient.mk'' x) x
  refine ⟨color, ?_, ?_, ?_⟩
  · intro x
    let omega : MulAction.orbitRel.Quotient TriangleGroup D := Quotient.mk'' x
    have hxmem : x ∈ omega.orbit := MulAction.orbitRel.Quotient.mem_orbit.mpr rfl
    have hrmem : rho₁ • x ∈ omega.orbit := omega.mapsTo_smul_orbit rho₁ hxmem
    have h := (hcomponent_spec omega).1 (⟨x, hxmem⟩ : omega.orbit)
    have hsub : rho₁ • (⟨x, hxmem⟩ : omega.orbit) = ⟨rho₁ • x, hrmem⟩ := by
      apply Subtype.ext
      rfl
    change extendedColor (Quotient.mk'' (rho₁ • x)) (rho₁ • x) =
      extendedColor omega x + 1
    have hquot :
        (Quotient.mk'' (rho₁ • x) : MulAction.orbitRel.Quotient TriangleGroup D) =
          omega := MulAction.orbitRel.Quotient.quotient_smul_eq
    rw [hquot]
    dsimp only [extendedColor]
    rw [dite_eq_left hrmem, dite_eq_left hxmem]
    rw [hsub] at h
    exact h
  · intro x
    let omega : MulAction.orbitRel.Quotient TriangleGroup D := Quotient.mk'' x
    have hxmem : x ∈ omega.orbit := MulAction.orbitRel.Quotient.mem_orbit.mpr rfl
    have hrmem : rho₂ • x ∈ omega.orbit := omega.mapsTo_smul_orbit rho₂ hxmem
    have h := (hcomponent_spec omega).2.1 (⟨x, hxmem⟩ : omega.orbit)
    have hsub : rho₂ • (⟨x, hxmem⟩ : omega.orbit) = ⟨rho₂ • x, hrmem⟩ := by
      apply Subtype.ext
      rfl
    change extendedColor (Quotient.mk'' (rho₂ • x)) (rho₂ • x) =
      extendedColor omega x + 1
    have hquot :
        (Quotient.mk'' (rho₂ • x) : MulAction.orbitRel.Quotient TriangleGroup D) =
          omega := MulAction.orbitRel.Quotient.quotient_smul_eq
    rw [hquot]
    dsimp only [extendedColor]
    rw [dite_eq_left hrmem, dite_eq_left hxmem]
    rw [hsub] at h
    exact h
  · intro x
    let omega : MulAction.orbitRel.Quotient TriangleGroup D := Quotient.mk'' x
    have hxmem : x ∈ omega.orbit := MulAction.orbitRel.Quotient.mem_orbit.mpr rfl
    have hrmem : rho₃ • x ∈ omega.orbit := omega.mapsTo_smul_orbit rho₃ hxmem
    have h := (hcomponent_spec omega).2.2 (⟨x, hxmem⟩ : omega.orbit)
    have hsub : rho₃ • (⟨x, hxmem⟩ : omega.orbit) = ⟨rho₃ • x, hrmem⟩ := by
      apply Subtype.ext
      rfl
    change extendedColor (Quotient.mk'' (rho₃ • x)) (rho₃ • x) =
      extendedColor omega x + 1
    have hquot :
        (Quotient.mk'' (rho₃ • x) : MulAction.orbitRel.Quotient TriangleGroup D) =
          omega := MulAction.orbitRel.Quotient.quotient_smul_eq
    rw [hquot]
    dsimp only [extendedColor]
    rw [dite_eq_left hrmem, dite_eq_left hxmem]
    rw [hsub] at h
    exact h

omit [MulAction TriangleGroup D] in
/-- Permutation form of the colouring theorem.  Any three fixed-point-free
permutations satisfying the triangle-group relations share a `ZMod 3`
colouring advanced by all three permutations. -/
theorem permutations_admit_three_coloring
    (a b c : Equiv.Perm D)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hc : c ^ 3 = 1)
    (habc : a * b * c = 1)
    (hfreeA : ∀ x, a x ≠ x)
    (hfreeB : ∀ x, b x ≠ x)
    (hfreeC : ∀ x, c x ≠ x) :
    ∃ color : D → ZMod 3,
      (∀ x, color (a x) = color x + 1) ∧
      (∀ x, color (b x) = color x + 1) ∧
      (∀ x, color (c x) = color x + 1) := by
  let theta := triangleRepresentation a b c ha hb hc habc
  let _ : MulAction TriangleGroup D := MulAction.compHom D theta
  have htheta₁ : theta rho₁ = a := triangleRepresentation_rho₁ a b c ha hb hc habc
  have htheta₂ : theta rho₂ = b := triangleRepresentation_rho₂ a b c ha hb hc habc
  have htheta₃ : theta rho₃ = c := triangleRepresentation_rho₃ a b c ha hb hc habc
  have hfree₁ : ∀ x : D, rho₁ • x ≠ x := by
    intro x
    change (theta rho₁) x ≠ x
    rw [htheta₁]
    exact hfreeA x
  have hfree₂ : ∀ x : D, rho₂ • x ≠ x := by
    intro x
    change (theta rho₂) x ≠ x
    rw [htheta₂]
    exact hfreeB x
  have hfree₃ : ∀ x : D, rho₃ • x ≠ x := by
    intro x
    change (theta rho₃) x ≠ x
    rw [htheta₃]
    exact hfreeC x
  obtain ⟨color, h₁, h₂, h₃⟩ := exists_three_coloring hfree₁ hfree₂ hfree₃
  refine ⟨color, ?_, ?_, ?_⟩
  · intro x
    have h := h₁ x
    change color ((theta rho₁) x) = color x + 1 at h
    simpa only [htheta₁] using h
  · intro x
    have h := h₂ x
    change color ((theta rho₂) x) = color x + 1 at h
    simpa only [htheta₂] using h
  · intro x
    have h := h₃ x
    change color ((theta rho₃) x) = color x + 1 at h
    simpa only [htheta₃] using h

end EuclideanTriangleGroup
