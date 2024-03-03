import Std
import SetTheory.Basic

namespace ZFC
variable {set : Type} [Membership set set] [EmptyCollection set] [ZFC set]
open ZFC
open Classical
instance: Nonempty set := ⟨∅⟩

def cartesian_product (a: set) (b: set) := separation (fun w => ∃x ∈ a, ∃y ∈ b, w = ⟪x,y⟫) $ powerset $ powerset $ a ∪ b
infixr:35 " × "  => cartesian_product

noncomputable def proj1 (a: set) : set := ⋃ separation (fun w => {w} ∈ a) (⋃ a)

noncomputable def proj2 (a: set) : set := ⋃ separation (fun w => w ≠ proj1 a ∨ a = {{w}}) (⋃ a)


theorem mem_cartesian_product_iff {a b x: set}: x ∈ (a × b) ↔ ∃y ∈ a, ∃z ∈ b, x = ⟪y,z⟫ := by
  simp only [cartesian_product, mem_separation_iff', mem_powerset_iff_subset, and_iff_right_iff_imp,
    forall_exists_index, and_imp]
  intro y hy z hz eq
  rw[eq]
  intro w hw
  rw[mem_ordered_pair_iff] at hw
  rcases hw with h|h
  · simp only [h, mem_powerset_iff_subset, singleton_subset_iff_mem, mem_union_iff, hy, true_or]
  · simp only [h, mem_powerset_iff_subset, pair_subset_iff, mem_union_iff, hy, true_or, hz,
    or_true, and_self]

@[simp] theorem ordered_pair_mem_cartesian_product_iff {a b x y: set}: ⟪x,y⟫ ∈ (a × b) ↔ (x ∈ a ∧ y ∈ b) := by
  simp only [mem_cartesian_product_iff, ordered_pair_inj, exists_eq_right_right']

theorem union_ordered_pair {a b: set}: (⋃ ⟪a,b⟫) =(pair a b : set) := by
  apply Subset.antisymm
  · rw [ordered_pair, ←union_def, union_subset_iff]
    simp only [singleton_subset_iff_mem, mem_pair_iff', true_or, Subset.refl, and_self]
  · rintro x hx
    rw[mem_pair_iff] at hx
    rcases hx with rfl|rfl
    · simp only [ordered_pair, mem_set_union_iff', mem_pair_iff', exists_eq_or_imp,
      mem_singleton_iff, exists_eq_left, true_or, or_self]
    · simp only [ordered_pair, mem_set_union_iff', mem_pair_iff', exists_eq_or_imp,
      mem_singleton_iff, exists_eq_left, or_true]

@[simp] theorem proj1_ordered_pair {a b: set}: proj1 ⟪a,b⟫ = a := by
  rw[proj1, union_ordered_pair, ordered_pair]
  suffices h: separation (fun w => {w} ∈ pair {a} (pair a b)) (pair a b) = {a} by
    rw[h]; simp only [set_union_singleton]
  apply Subset.antisymm
  · intro x hx
    simp only [mem_pair_iff', singleton_inj, singleton_eq_pair_iff, mem_separation_iff',
      mem_singleton_iff] at *
    rcases hx.2 with h | h
    · exact h
    · exact h.1
  · simp only [mem_pair_iff', singleton_inj, singleton_eq_pair_iff, singleton_subset_iff_mem,
    mem_separation_iff', true_or, true_and, and_self]

@[simp] theorem proj2_ordered_pair {a b: set}: proj2 ⟪a,b⟫ = b := by
  rw[proj2, union_ordered_pair]
  suffices h: separation (fun w => w ≠ proj1 ⟪a,b⟫ ∨ ⟪a,b⟫ = {{w}}) (pair a b) = {b} by
    rw[h]; simp only [set_union_singleton]
  apply Subset.antisymm
  · intro x hx
    simp only [proj1_ordered_pair, ne_eq, mem_separation_iff', mem_pair_iff',
      mem_singleton_iff] at *
    rcases hx with ⟨(rfl|rfl),(h2|h2)⟩
    · exact False.elim $ h2 rfl
    · have h3: pair x b ∈ ⟪x,b⟫ := by simp only [mem_ordered_pair_iff, pair_eq_singleton_iff,
      true_and, or_true]
      rw[h2] at h3
      simp only [mem_singleton_iff, pair_eq_singleton_iff, true_and] at h3
      exact h3
    · rfl
    · rfl
  · simp only [proj1_ordered_pair, ne_eq, singleton_subset_iff_mem, mem_separation_iff',
    mem_pair_iff', or_true, true_and]
    by_cases h: b = a
    · apply Or.inr
      simp only [h, ordered_pair._eq_1, pair_eq_singleton_iff, singleton_eq_pair_iff, and_self]
    · exact Or.inl h

-- TODO def converse (a: set): set := replacement (fun a )

def is_relation (a: set) := ∀b ∈ a, ∃x, ∃y, b = ordered_pair x y
def is_single_valued (a: set) := ∀x y z, ⟪x,y⟫ ∈ a → ⟪x,z⟫ ∈ a → y = z
--TODO def is_one_to_one
def is_function (a: set) := is_relation a ∧ is_single_valued a
--TODO def is_one_to_one_function
def domain (a: set) := separation (fun x => ∃ y, ⟪x,y⟫ ∈ a) (⋃ ⋃ a)
def range (a: set) := separation (fun y => ∃ x, ⟪x,y⟫ ∈ a) (⋃ ⋃ a)

@[simp] theorem mem_domain_iff {a x: set}: x ∈ domain a ↔ ∃y, ⟪x,y⟫ ∈ a := by
  simp only [domain, mem_separation_iff', mem_set_union_iff', and_iff_right_iff_imp,
    forall_exists_index]
  intro y hy
  exists singleton x
  apply And.intro
  · exists ⟪x,y⟫
    apply And.intro hy
    simp only [mem_ordered_pair_iff, singleton_eq_pair_iff, true_and, true_or]
  · simp only [mem_singleton_iff]


end ZFC
