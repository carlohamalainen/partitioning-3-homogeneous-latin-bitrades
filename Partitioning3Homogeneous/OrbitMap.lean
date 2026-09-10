import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Tactic.Group

/-!
# Equivariant maps between transitive group actions

This isolates the abstract argument used for the map `psi` in Lemma 4.1 of
the paper. A homomorphism between the acting groups does not, by itself,
make the orbit map well-defined. The stabilizer of the source base point must
map into the stabilizer of the target base point. A free source action is a
sufficient special case.
-/

namespace EquivariantOrbitMap

variable {Gamma G X Y : Type*}
variable [Group Gamma] [Group G]
variable [MulAction Gamma X] [MulAction G Y]

/-- Every point of `X` can be reached from the chosen base point. -/
def IsTransitiveAt (Gamma : Type*) [Group Gamma] [MulAction Gamma X] (x₀ : X) : Prop :=
  ∀ x, ∃ gamma : Gamma, gamma • x₀ = x

/-- The condition required for a base-point orbit map to be independent of
the group element chosen to reach a point. -/
def MapsStabilizer (theta : Gamma →* G) (x₀ : X) (y₀ : Y) : Prop :=
  ∀ gamma : Gamma, gamma • x₀ = x₀ → theta gamma • y₀ = y₀

section Construction

variable (theta : Gamma →* G) (x₀ : X) (y₀ : Y)
variable (htrans : IsTransitiveAt Gamma x₀)

/-- A choice of group element carrying `x₀` to `x`. -/
noncomputable def representative (x : X) : Gamma :=
  Classical.choose (htrans x)

theorem representative_spec (x : X) :
    representative x₀ htrans x • x₀ = x :=
  Classical.choose_spec (htrans x)

/-- The candidate orbit map, defined using an arbitrary representative. -/
noncomputable def descend (x : X) : Y :=
  theta (representative x₀ htrans x) • y₀

variable (hstab : MapsStabilizer theta x₀ y₀)

include hstab

theorem descend_base : descend theta x₀ y₀ htrans x₀ = y₀ := by
  apply hstab
  exact representative_spec x₀ htrans x₀

theorem descend_equivariant (gamma : Gamma) (x : X) :
    descend theta x₀ y₀ htrans (gamma • x) =
      theta gamma • descend theta x₀ y₀ htrans x := by
  let r := representative x₀ htrans x
  let s := representative x₀ htrans (gamma • x)
  let stabilizerElement := (gamma * r)⁻¹ * s
  have hr : r • x₀ = x := representative_spec x₀ htrans x
  have hs : s • x₀ = gamma • x := representative_spec x₀ htrans (gamma • x)
  have hfix : stabilizerElement • x₀ = x₀ := by
    calc
      stabilizerElement • x₀ = (gamma * r)⁻¹ • (s • x₀) := by
        simp only [stabilizerElement, mul_smul]
      _ = (gamma * r)⁻¹ • (gamma • x) := by rw [hs]
      _ = (gamma * r)⁻¹ • (gamma • (r • x₀)) := by rw [hr]
      _ = (gamma * r)⁻¹ • ((gamma * r) • x₀) := by rw [mul_smul]
      _ = x₀ := inv_smul_smul (gamma * r) x₀
  have hfixImage : theta stabilizerElement • y₀ = y₀ := hstab stabilizerElement hfix
  have hsGroup : (gamma * r) * stabilizerElement = s := by
    dsimp [stabilizerElement]
    group
  change theta s • y₀ = theta gamma • (theta r • y₀)
  calc
    theta s • y₀ = theta ((gamma * r) * stabilizerElement) • y₀ := by
      rw [hsGroup]
    _ = theta (gamma * r) • (theta stabilizerElement • y₀) := by
      simp only [map_mul, mul_smul]
    _ = theta (gamma * r) • y₀ := by rw [hfixImage]
    _ = theta gamma • (theta r • y₀) := by
      simp only [map_mul, mul_smul]

include htrans
/-- A transitive action and the stabilizer condition produce the desired
base-point-preserving equivariant map. -/
theorem exists_equivariant :
    ∃ psi : X → Y,
      psi x₀ = y₀ ∧
      ∀ gamma x, psi (gamma • x) = theta gamma • psi x := by
  refine ⟨descend theta x₀ y₀ htrans, descend_base theta x₀ y₀ htrans hstab, ?_⟩
  exact descend_equivariant theta x₀ y₀ htrans hstab

end Construction

/-- Freeness at the source base point supplies the stabilizer condition used
above. This is the repair appropriate for the simply transitive chamber action
intended in the paper. -/
theorem exists_equivariant_of_free
    (theta : Gamma →* G) (x₀ : X) (y₀ : Y)
    (htrans : IsTransitiveAt Gamma x₀)
    (hfree : ∀ gamma : Gamma, gamma • x₀ = x₀ → gamma = 1) :
    ∃ psi : X → Y,
      psi x₀ = y₀ ∧
      ∀ gamma x, psi (gamma • x) = theta gamma • psi x := by
  have hstab : MapsStabilizer theta x₀ y₀ := by
    intro gamma hgamma
    rw [hfree gamma hgamma]
    simp
  exact exists_equivariant theta x₀ y₀ htrans hstab

end EquivariantOrbitMap
