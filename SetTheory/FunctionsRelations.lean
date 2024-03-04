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

@[simp] theorem exists_eq_right' {α : Sort u_1} {p : α → Prop} {a' : α} : (∃ (a : α), p a ∧  a' = a) ↔ p a' := by
  constructor
  · rintro ⟨a, h, rfl⟩
    exact h
  · intro h
    exists a'

noncomputable def converse (a: set): set := replacement (fun a => ⟪proj2 a, proj1 a⟫) (separation (fun a => ∃x y, a = ⟪x,y⟫) a)
theorem mem_converse_iff {a x: set}: x ∈ converse a ↔ ∃y z, ⟪y,z⟫ ∈ a ∧ x = ⟪z,y⟫ := by
  simp[converse]
  apply Iff.intro
  · rintro ⟨p, ⟨⟨hp, ⟨x,y,rfl⟩⟩, rfl⟩⟩
    exists x, y
    simp only [proj2_ordered_pair, proj1_ordered_pair, and_self, hp]
  · rintro ⟨y, z, h, rfl⟩
    exists ⟪y, z⟫
    simp only [h, ordered_pair_inj, exists_and_left, exists_eq', and_true, and_self,
      proj2_ordered_pair, proj1_ordered_pair]

@[simp] theorem ordered_pair_mem_converse_iff {a x y: set}: ⟪x,y⟫ ∈ converse a ↔ ⟪y,x⟫ ∈ a := by
  simp only [mem_converse_iff, ordered_pair_inj]
  apply Iff.intro
  · rintro ⟨y1,z1, hin, rfl, rfl⟩
    exact hin
  · intro h
    exists y,x

theorem converse_converse_subset {a: set}: converse (converse a) ⊆ a := by
  intro x hx
  simp only [mem_converse_iff, ordered_pair_inj] at hx
  rcases hx with ⟨y,z,⟨_,_,h,rfl,rfl⟩,rfl⟩
  exact h

def is_relation (a: set) := ∀b ∈ a, ∃x, ∃y, b = ordered_pair x y

@[simp] theorem converse_converse_eq_iff {a: set}: converse (converse a) = a ↔ is_relation a := by
  constructor
  · rintro h
    rw[←h]
    intro b hb
    simp only [mem_converse_iff, ordered_pair_inj] at hb
    rcases hb with ⟨y,z,_,h2⟩
    exists z, y
  · intro h
    ext x
    simp only [mem_converse_iff, ordered_pair_inj]
    constructor
    · rintro ⟨y,z, ⟨_,_,ha,rfl,rfl⟩, rfl⟩
      exact ha
    · intro xa
      obtain ⟨y,z,rfl⟩ := h x xa
      exists z, y, ⟨y,z,xa,rfl,rfl⟩

@[simp] theorem converse_is_relation {a: set}: is_relation (converse a) := by
  intro x
  simp only [mem_converse_iff, forall_exists_index, and_imp]
  rintro y z _ rfl
  exists z, y

@[simp] theorem cartesian_product_is_relation {a b: set}: is_relation (a × b) := by
  intro x
  simp only [mem_cartesian_product_iff, forall_exists_index, and_imp]
  rintro y _ z _ rfl
  exists y, z

@[simp] theorem empty_set_is_relation: is_relation (∅: set) := by
  intro x
  simp only [mem_empty_iff, false_implies]

@[simp] theorem set_union_is_relation {a: set} (h: ∀x ∈ a, is_relation x): is_relation (⋃ a) := by
  intro x
  simp only [mem_set_union_iff', forall_exists_index, and_imp]
  intro y hy hx
  exact h y hy x hx

@[simp] theorem union_is_relation {a b: set} (h: is_relation a) (h2: is_relation b): is_relation (a ∪ b) := by
  apply set_union_is_relation
  intro x2
  simp
  rintro (rfl|rfl)
  · exact h
  · exact h2

@[simp] theorem singleton_ordered_pair_is_relation {x y: set}: is_relation ({⟪x,y⟫} :set) := by
  intro a
  rw[mem_singleton_iff]
  rintro rfl
  exists x,y

@[simp] theorem pair_ordered_pair_is_relation {x y v w: set}: is_relation (pair ⟪x,y⟫ ⟪v,w⟫) := by
  intro a
  rw[mem_pair_iff]
  rintro (rfl|rfl)
  · exists x,y
  · exists v,w


theorem subset_is_relation {a b: set} (h: is_relation a) (h2: b ⊆ a): is_relation b :=
  fun x hx => h x (h2 _ hx)

@[simp] theorem inter_is_relation_left {a b: set} (h: is_relation a): is_relation (a ∩ b) := subset_is_relation h left_inter_subset
@[simp] theorem inter_is_relation_right {a b: set} (h: is_relation a): is_relation (b ∩ a) := subset_is_relation h right_inter_subset

theorem relation_ext {a b: set} (ha: is_relation a) (hb: is_relation b) (h: ∀x y, ⟪x,y⟫ ∈ a ↔ ⟪x,y⟫ ∈ b) : a = b := by
  ext x
  constructor
  · intro hx
    obtain ⟨x,y,rfl⟩ := ha x hx
    exact (h x y).mp hx
  · intro hy
    obtain ⟨x,y,rfl⟩ := hb x hy
    exact (h x y).mpr hy

theorem relation_subset_from {a b: set} (ha: is_relation a) (h: ∀x y, ⟪x,y⟫ ∈ a → ⟪x,y⟫ ∈ b) : a ⊆ b := by
  intro x hx
  obtain ⟨x,y,rfl⟩ := ha x hx
  exact h x y hx

@[simp] theorem converse_empty_set: converse (∅: set) = ∅ := by
  apply relation_ext converse_is_relation empty_set_is_relation
  intro x y
  simp only [ordered_pair_mem_converse_iff, mem_empty_iff]

@[simp] theorem converse_cartesian_product {a b: set}: converse (a × b : set) = (b × a :set) := by
  apply relation_ext converse_is_relation cartesian_product_is_relation
  intro x y
  simp only [ordered_pair_mem_converse_iff, ordered_pair_mem_cartesian_product_iff]
  exact and_comm

@[simp] theorem converse_subset {a b: set} (h: a ⊆ b): converse a ⊆ converse b := by
  apply relation_subset_from converse_is_relation
  intro x y
  simp only [ordered_pair_mem_converse_iff]
  apply h

theorem converse_inter {a b: set}: converse (a ∩ b) = converse a ∩ converse b := by
  apply relation_ext converse_is_relation (inter_is_relation_left converse_is_relation)
  intro x y
  simp only [ordered_pair_mem_converse_iff, mem_inter_iff]

@[simp] theorem for_all_mem_replacement_iff {a: set} {f: set → set} {p: set → Prop}: (∀x ∈ replacement f a, p x) ↔ (∀x ∈ a, p (f x)) := by
  constructor
  · intro h x ax
    apply h (f x)
    rw [mem_replacement_iff']
    exists x
  · intro h x hx
    rw [mem_replacement_iff'] at hx
    rcases hx with ⟨y, hy, rfl⟩
    exact h y hy

theorem converse_set_union {a: set}: converse (⋃ a) = ⋃ (replacement converse a) := by
  apply relation_ext converse_is_relation
  · apply set_union_is_relation
    apply (for_all_mem_replacement_iff (a := a) (f := converse) (p := is_relation)).mpr
    simp only [converse_is_relation, forall_const, implies_true]
  · intro x y
    simp only [ordered_pair_mem_converse_iff, mem_set_union_iff', mem_replacement_iff']
    constructor
    · rintro ⟨p,h1,h2⟩
      exists converse p
      exact ⟨⟨p,h1,rfl⟩, by simp only [ordered_pair_mem_converse_iff, h2]⟩
    · rintro ⟨p, ⟨q, h, rfl⟩, h2⟩
      exists q, h
      simp only [ordered_pair_mem_converse_iff] at h2
      exact h2

theorem converse_union {a b: set}: converse (a ∪ b) = converse a ∪ converse b := by
  apply relation_ext converse_is_relation (union_is_relation converse_is_relation converse_is_relation)
  intro x y
  simp only [ordered_pair_mem_converse_iff, mem_union_iff]


def is_single_valued (a: set) := ∀x y z, ⟪x,y⟫ ∈ a → ⟪x,z⟫ ∈ a → y = z
def is_one_to_one (a: set) := is_single_valued a ∧ is_single_valued (converse a)
def is_function (a: set) := is_relation a ∧ is_single_valued a
def is_one_to_one_function (a: set) := is_function a ∧ is_one_to_one a
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

@[simp] theorem mem_range_iff {a y: set}: y ∈ range a ↔ ∃x, ⟪x,y⟫ ∈ a := by
  simp only [range, mem_separation_iff', mem_set_union_iff', and_iff_right_iff_imp,
    forall_exists_index]
  intro x hx
  exists pair x y
  apply And.intro
  · exists ⟪x,y⟫
    apply And.intro hx
    simp only [ordered_pair, mem_pair_iff', pair_eq_singleton_iff, true_and, or_true]
  · simp only [mem_pair_iff', or_true]

def restrict_left (a b: set) := a ∩ (b × range a)

theorem mem_restrict_left_iff {x a b: set}: x ∈ restrict_left a b ↔ x ∈ a ∧ ∃y ∈ b, ∃z, x = ⟪y,z⟫ := by
  simp only [restrict_left, mem_inter_iff, mem_cartesian_product_iff, mem_range_iff,
    and_congr_right_iff]
  intro h
  apply Iff.intro
  · rintro ⟨y, h1, z, ⟨⟨_, _⟩, rfl⟩⟩
    exists y
    simp only [ordered_pair_inj, true_and, exists_eq', and_self, h1]
  · rintro ⟨y, hy, z, rfl⟩
    exists y
    simp only [ordered_pair_inj, true_and, hy]
    exists z
    exact ⟨⟨y, h⟩, rfl⟩

@[simp] theorem ordered_pair_mem_restrict_left_iff {x y a b: set}: ⟪x,y⟫ ∈ restrict_left a b ↔ (⟪x,y⟫ ∈ a ∧ x ∈ b) := by
  simp only [mem_restrict_left_iff, ordered_pair_inj, exists_and_left, exists_eq', and_true,
    exists_eq_right']

infixr:50 "↾"  => restrict_left
def image (a b: set) := range (restrict_left a b)

@[simp] theorem mem_image_iff {x a b: set}: x ∈ image a b ↔ ∃y ∈ b, ⟪y,x⟫ ∈ a := by
  simp only [image, mem_range_iff, ordered_pair_mem_restrict_left_iff]
  exact exists_congr $ fun y => and_comm

infixr:45 "“" => image

def comp (a b: set) := separation (fun p => ∃x, ∃y, ∃ z, p = ⟪x,y⟫ ∧ ⟪x,z⟫ ∈ b ∧ ⟪z,y⟫ ∈ a) (domain b × range a)
theorem mem_comp_iff {x a b: set}: x ∈ comp a b ↔ ∃w, ∃y, ∃ z, x = ⟪w,y⟫ ∧ ⟪w,z⟫ ∈ b ∧ ⟪z,y⟫ ∈ a := by
  simp only [comp, exists_and_left, mem_separation_iff', and_iff_right_iff_imp, forall_exists_index,
    and_imp]
  rintro y z rfl w yw wz
  simp only [ordered_pair_mem_cartesian_product_iff, mem_domain_iff, mem_range_iff]
  exact ⟨⟨w,yw⟩,⟨w,wz⟩⟩

@[simp] theorem ordered_pair_mem_comp_iff {x y a b: set}: ⟪x,y⟫ ∈ comp a b ↔ ∃z, ⟪x,z⟫ ∈ b ∧ ⟪z,y⟫ ∈ a := by
  simp only [mem_comp_iff, ordered_pair_inj, exists_and_left]
  constructor
  · rintro ⟨_,_,⟨rfl,rfl⟩,w,⟨h1,h2⟩⟩
    exists w
  · rintro ⟨z,hb,ha⟩
    exists x,y,⟨rfl,rfl⟩,z

infixr:90 " ∘ "  => comp

theorem mem_comp_from_mem_rels {x y z a b: set} (h: ⟪z,y⟫ ∈ a) (h2: ⟪x,z⟫ ∈ b): ⟪x,y⟫ ∈ comp a b := by
  rw[ordered_pair_mem_comp_iff]
  exists z


end ZFC
