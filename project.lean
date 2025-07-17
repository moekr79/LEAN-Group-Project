import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Defs

/-!
# Injectivity of Group Homomorphisms and Trivial Kernel

A group homomorphism is injective if and only if its kernel is trivial.
-/

variable {G H : Type*} [Group G] [Group H]
-- variable {g : G}
variable (f : G →* H)

-- lemma neutral_element_maps_to_neutral_element : f 1 = 1 := by
--   rw [map_one f]


-- lemma inverse_maps_to_inverse (g : G) : f g⁻¹ = (f g)⁻¹ := by
--   rw [map_inv f]

theorem f_injective_iff_ker_trivial :
  Function.Injective f ↔ ∀ g, f g = 1 → g = 1 := by
  constructor
  · intro hf g hg
    rw [←map_one f] at hg
    exact hf hg
  · intro hKer g k hgk
    have h1 : (f g) * (f k)⁻¹ = (f k) * (f k)⁻¹ := by rw [← hgk]
    have h2 : (f g) * (f k)⁻¹ = 1 := by rw [h1, mul_inv_cancel]
    have h3 : (f g) * (f (k⁻¹)) = 1 := by rw [map_inv, h2]
    have h4 : f (g * k⁻¹) = 1 := by rw [map_mul, h3]
    have h5 : g * k⁻¹ = 1 := by apply hKer; exact h4
    have h6 : g * k⁻¹ * k = 1 * k := by rw [← h5]
    have h7 : g * k⁻¹ * k = k := by rw [h6, one_mul]
    have h8 : g = k := by rw [inv_mul_cancel_right g k] at h7; exact h7
    exact h8
