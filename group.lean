import Mathlib


structure our_Group where
  uni : Type
  mul : uni → uni → uni
  one : uni
  inv : uni → uni
  mul_assoc : ∀ a b c : uni, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : uni, mul one a = a
  mul_one : ∀ a : uni, mul a one = a
  mul_inv : ∀ a : uni, mul a (inv a) = one
  inv_mul : ∀ a : uni, mul (inv a) a = one


lemma our_unique_inv {G : our_Group} (a b : G.uni) : G.mul a b = G.one → b = G.inv a := by
  intro h
  have h1 : G.mul a (G.inv a) = G.one := G.mul_inv a
  rw [←h] at h1
  have h2 : G.mul (G.inv a) (G.mul a b) = G.mul (G.inv a) G.one := by rw [h]
  have h3 : G.mul (G.mul (G.inv a) a) b = G.mul (G.inv a) G.one := by rw [G.mul_assoc, h2]
  have h4 : G.mul (G.one) b = G.mul (G.inv a) G.one := by
    rw [G.inv_mul a] at h3
    exact h3
  have h5 : b = G.mul (G.inv a) G.one := by
    rw [G.one_mul b] at h4
    exact h4
  have h6 : b = G.inv a := by
    rw [G.mul_one (G.inv a)] at h5
    exact h5
  exact h6


lemma our_unique_inv_inv {G : our_Group} (a : G.uni) : a = G.inv (G.inv a) := by
  have h1 : G.mul (G.inv a) a = G.one := G.inv_mul a
  apply our_unique_inv (G.inv a) a at h1
  exact h1


structure our_Group_Hom (G H : our_Group) where
  map : G.uni → H.uni
  hom_mul : ∀ a b : G.uni, map (G.mul a b) = H.mul (map a) (map b)
  mul_hom : ∀ a b : G.uni, H.mul (map a) (map b) = map (G.mul a b)
  hom_one : map G.one = H.one
  ker : Set G.uni
  ker_def : ∀ a : G.uni, map a = H.one ↔ g ∈ ker


lemma our_map_inv {G H : our_Group} (f : our_Group_Hom G H) (a : G.uni) :
  f.map (G.inv a) = H.inv (f.map a) := by
  apply our_unique_inv
  -- Use the property that f is a homomorphism and the uniqueness of inverses
  have h1 : H.mul (f.map a) (f.map (G.inv a)) = f.map (G.mul (a) (G.inv a)) := by rw[f.hom_mul a (G.inv a)]
  have h2 : H.mul (f.map a) (f.map (G.inv a)) = f.map G.one := by
    rw [G.mul_inv a] at h1
    exact h1
  have h3 : H.mul (f.map a) (f.map (G.inv a)) = H.one := by
    rw [f.hom_one] at h2
    exact h2
  exact h3


theorem our_hom_injective_iff_ker_trivial {G H : our_Group} (f : our_Group_Hom G H) :
  Function.Injective f.map ↔ f.ker = {G.one} := by
  constructor
  · intro hf
    ext a
    constructor
    · intro ha
      rw [← f.ker_def a] at ha
      have hOne : f.map G.one = H.one := f.hom_one
      have h1 : f.map a = f.map (G.one) := by
        rw [hOne]
        exact ha
      apply hf h1
    · intro ha
      have ha : a = G.one := by
        apply Set.mem_singleton_iff.mp ha
      rw [← f.ker_def a]
      rw [ha]
      exact f.hom_one
  · intro hKer a b hab
    have h1: H.mul (f.map a) (H.inv (f.map b)) = H.mul (f.map b) (H.inv (f.map b)) := by rw[hab]
    have h2: H.mul (f.map a) (H.inv (f.map b)) = H.one := by
      rw [H.mul_inv (f.map b)] at h1
      exact h1
    have h3 : H.inv (f.map b) = f.map (G.inv b) := by
      rw [our_map_inv f b]
    have h3: H.mul (f.map a) (f.map (G.inv b)) = H.one := by
      rw [h3] at h2
      exact h2
    have h4 : f.map (G.mul a (G.inv b)) = H.one := by
      rw [f.mul_hom a (G.inv b)] at h3
      exact h3
    have h5 : G.mul a (G.inv b) ∈ f.ker := by
      rw [← f.ker_def (G.mul a (G.inv b))]
      exact h4
    have h6 : G.mul a (G.inv b) = G.one := by
      rw [hKer, Set.mem_singleton_iff] at h5
      exact h5
    have h7 : G.inv b = G.inv a := by
      apply our_unique_inv
      exact h6
    have h8 : G.inv (G.inv b) = G.inv (G.inv a) := by
      rw [h7]
    rw [←our_unique_inv_inv a, ←our_unique_inv_inv b] at h8
    rw [h8]
