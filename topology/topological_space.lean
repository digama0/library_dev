/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Theory of topological spaces.
-/
import algebra.lattice.filter
open set filter lattice

universes u v w

@[simp]
lemma singleton_neq_emptyset {α : Type u} {a : α} : {a} ≠ (∅ : set α) :=
take h, 
have a ∉ ({a} : set α),
  by simp [h],
this $ mem_singleton a

@[simp]
lemma principal_eq_bot_iff {α : Type u} {s : set α} : principal s = ⊥ ↔ s = ∅ :=
principal_eq_iff_eq

@[simp]
lemma return_neq_bot {α : Type u} {a : α} : return a ≠ (⊥ : filter α) :=
by simp [return, pure]

lemma not_imp_not_iff {a b : Prop} :
  (¬ a → ¬ b) ↔ (b → a) :=
⟨take h hb, classical.by_contradiction $ take na, h na hb, 
  contrapos⟩

lemma eq_of_sup_eq_inf_eq {α : Type u} [distrib_lattice α] {a b c : α}
  (h₁ : b ⊓ a = c ⊓ a) (h₂ : b ⊔ a = c ⊔ a) : b = c :=
le_antisymm
  (calc b ≤ (c ⊓ a) ⊔ b     : le_sup_right
    ... = (c ⊔ b) ⊓ (a ⊔ b) : sup_inf_right
    ... = c ⊔ (c ⊓ a)       : by rw [-h₁, sup_inf_left, -h₂]; simp [sup_comm]
    ... = c                 : sup_inf_self)
  (calc c ≤ (b ⊓ a) ⊔ c     : le_sup_right
    ... = (b ⊔ c) ⊓ (a ⊔ c) : sup_inf_right
    ... = b ⊔ (b ⊓ a)       : by rw [h₁, sup_inf_left, h₂]; simp [sup_comm]
    ... = b                 : sup_inf_self)

lemma inf_eq_bot_iff_le_compl {α : Type u} [bounded_distrib_lattice α] {a b c : α} (h₁ : b ⊔ c = ⊤) (h₂ : b ⊓ c = ⊥) :
  b ⊓ a = ⊥ ↔ a ≤ c :=
⟨suppose b ⊓ a = ⊥, 
  calc a ≤ a ⊓ (b ⊔ c) : by simp [h₁]
    ... = (b ⊓ a) ⊔ (a ⊓ c) : by simp [inf_sup_left, inf_comm]
    ... ≤ c : by simp [this, inf_le_right],
  suppose a ≤ c,
  bot_unique $
    calc b ⊓ a ≤ b ⊓ c : inf_le_inf (le_refl b) this
      ... = ⊥ : h₂⟩

lemma compl_image_set_of {α : Type u} {p : set α → Prop} :
  compl ' {x | p x} = {x | p (- x)} :=
set.ext $ take x, ⟨take ⟨y, (hy : p y), (h_eq : -y = x)⟩,
  show p (- x), by rw [-h_eq, lattice.neg_neg]; assumption,
  assume h : p (-x), ⟨_, h, lattice.neg_neg⟩⟩

class topology (α : Type u) :=
(open'       : set α → Prop)
(open_univ   : open' univ)
(open_inter  : ∀s t, open' s → open' t → open' (s ∩ t))
(open_sUnion : ∀s, (∀t∈s, open' t) → open' (⋃₀ s))

section topology

variables {α : Type u} {β : Type v} {ι : Sort w} {a a₁ a₂ : α} {s s₁ s₂ : set α}
variables [topology α]

/- open -/
def open' (s : set α) : Prop := topology.open' s

@[simp]
lemma open_univ : open' (univ : set α) := topology.open_univ α

lemma open_inter (h₁ : open' s₁) (h₂ : open' s₂) : open' (s₁ ∩ s₂) := topology.open_inter s₁ s₂ h₁ h₂

lemma open_sUnion {s : set (set α)} (h : ∀t ∈ s, open' t) : open' (⋃₀ s) := topology.open_sUnion s h

lemma open_Union {f : ι → set α} (h : ∀i, open' (f i)) : open' (⋃i, f i) :=
open_sUnion $ take t ⟨i, (heq : t = f i)⟩, heq^.symm ▸ h i

@[simp]
lemma open_empty : open' (∅ : set α) :=
have open' (⋃₀ ∅ : set α), from open_sUnion (take a, false.elim),
by simp at this; assumption

/- closed -/
def closed (s : set α) : Prop := open' (-s)

@[simp]
lemma closed_empty : closed (∅ : set α) := by simp [closed]

@[simp]
lemma closed_univ : closed (univ : set α) := by simp [closed]

lemma closed_union : closed s₁ → closed s₂ → closed (s₁ ∪ s₂) :=
by simp [closed]; exact open_inter

lemma closed_sInter {s : set (set α)} : (∀t ∈ s, closed t) → closed (⋂₀ s) :=
by simp [closed, compl_sInter]; exact take h, open_Union $ take t, open_Union $ take ht, h t ht

lemma closed_Inter {f : ι → set α} (h : ∀i, closed (f i)) : closed (⋂i, f i ) :=
closed_sInter $ take t ⟨i, (heq : t = f i)⟩, heq^.symm ▸ h i

@[simp]
lemma closed_compl_iff_open {s : set α} : open' (-s) ↔ closed s :=
by refl

@[simp]
lemma open_compl_iff_closed {s : set α} : closed (-s) ↔ open' s :=
by rw [-closed_compl_iff_open, compl_compl]

lemma open_diff {s t : set α} (h₁ : open' s) (h₂ : closed t) : open' (s - t) :=
open_inter h₁ $ closed_compl_iff_open^.mpr h₂

/- interior -/
def interior (s : set α) : set α := ⋃₀ {t | open' t ∧ t ⊆ s}

@[simp]
lemma open_interior {s : set α} : open' (interior s) :=
open_sUnion $ take t ⟨h₁, h₂⟩, h₁

lemma interior_subset {s : set α} : interior s ⊆ s :=
sUnion_subset $ take t ⟨h₁, h₂⟩, h₂

lemma interior_maximal {s t : set α} (h₁ : t ⊆ s) (h₂ : open' t) : t ⊆ interior s :=
subset_sUnion_of_mem ⟨h₂, h₁⟩

lemma interior_eq_of_open {s : set α} (h : open' s) : interior s = s :=
subset.antisymm interior_subset (interior_maximal (subset.refl s) h)

lemma interior_eq_iff_open {s : set α} : interior s = s ↔ open' s :=
⟨take h, h ▸ open_interior, interior_eq_of_open⟩

lemma subset_interior_iff_subset_of_open {s t : set α} (h₁ : open' s) :
  s ⊆ interior t ↔ s ⊆ t :=
⟨take h, subset.trans h interior_subset, take h₂, interior_maximal h₂ h₁⟩

lemma interior_mono {s t : set α} (h : s ⊆ t) : interior s ⊆ interior t :=
interior_maximal (subset.trans interior_subset h) open_interior

@[simp]
lemma interior_empty : interior (∅ : set α) = ∅ :=
interior_eq_of_open open_empty

@[simp]
lemma interior_univ : interior (univ : set α) = univ :=
interior_eq_of_open open_univ

@[simp]
lemma interior_interior {s : set α} : interior (interior s) = interior s :=
interior_eq_of_open open_interior

@[simp]
lemma interior_inter {s t : set α} : interior (s ∩ t) = interior s ∩ interior t :=
subset.antisymm
  (subset_inter (interior_mono $ inter_subset_left s t) (interior_mono $ inter_subset_right s t))
  (interior_maximal (inter_subset_inter interior_subset interior_subset) $ by simp [open_inter])

lemma interior_union_closed_of_interior_empty {s t : set α} (h₁ : closed s) (h₂ : interior t = ∅) :
  interior (s ∪ t) = interior s :=
have interior (s ∪ t) ⊆ s, from 
  take x ⟨u, ⟨(hu₁ : open' u), (hu₂ : u ⊆ s ∪ t)⟩, (hx₁ : x ∈ u)⟩, 
  classical.by_contradiction $ assume hx₂ : x ∉ s,
    have u - s ⊆ t,
      from take x ⟨h₁, h₂⟩, or.resolve_left (hu₂ h₁) h₂,
    have u - s ⊆ interior t,
      by simp [subset_interior_iff_subset_of_open, this, open_diff hu₁ h₁],
    have u - s ⊆ ∅,
      by rw [h₂] at this; assumption,
    this ⟨hx₁, hx₂⟩,
subset.antisymm
  (interior_maximal this open_interior)
  (interior_mono $ subset_union_left _ _)

/- closure -/
def closure (s : set α) : set α := ⋂₀ {t | closed t ∧ s ⊆ t}

@[simp]
lemma closed_closure {s : set α} : closed (closure s) :=
closed_sInter $ take t ⟨h₁, h₂⟩, h₁

lemma subset_closure {s : set α} : s ⊆ closure s :=
subset_sInter $ take t ⟨h₁, h₂⟩, h₂

lemma closure_minimal {s t : set α} (h₁ : s ⊆ t) (h₂ : closed t) : closure s ⊆ t :=
sInter_subset_of_mem ⟨h₂, h₁⟩

lemma closure_eq_of_closed {s : set α} (h : closed s) : closure s = s :=
subset.antisymm (closure_minimal (subset.refl s) h) subset_closure

lemma closure_eq_iff_closed {s : set α} : closure s = s ↔ closed s :=
⟨take h, h ▸ closed_closure, closure_eq_of_closed⟩

lemma closure_subset_iff_subset_of_closed {s t : set α} (h₁ : closed t) :
  closure s ⊆ t ↔ s ⊆ t :=
⟨subset.trans subset_closure, take h, closure_minimal h h₁⟩

lemma closure_mono {s t : set α} (h : s ⊆ t) : closure s ⊆ closure t :=
closure_minimal (subset.trans h subset_closure) closed_closure

@[simp]
lemma closure_empty : closure (∅ : set α) = ∅ :=
closure_eq_of_closed closed_empty

@[simp]
lemma closure_univ : closure (univ : set α) = univ :=
closure_eq_of_closed closed_univ

@[simp]
lemma closure_closure {s : set α} : closure (closure s) = closure s :=
closure_eq_of_closed closed_closure

@[simp]
lemma closure_union {s t : set α} : closure (s ∪ t) = closure s ∪ closure t :=
subset.antisymm
  (closure_minimal (union_subset_union subset_closure subset_closure) $ by simp [closed_union])
  (union_subset (closure_mono $ subset_union_left _ _) (closure_mono $ subset_union_right _ _))

lemma interior_subset_closure {s : set α} : interior s ⊆ closure s :=
subset.trans interior_subset subset_closure

@[simp]
lemma interior_compl_eq {s : set α} : interior (- s) = - closure s :=
begin 
  simp [interior, closure],
  rw [compl_sInter, compl_image_set_of],
  simp,
  apply congr_arg, apply set.ext, intro x,
  apply and_congr (iff.refl _),
  apply @neg_le_iff_neg_le (set α) _ _ _
end

@[simp]
lemma closure_compl_eq {s : set α} : closure (- s) = - interior s :=
have - - closure (- s) = - interior (- (- s)),
  by rw [interior_compl_eq],
by simp [lattice.neg_neg] at this; assumption

/- neighbourhood filter -/
def nhds (a : α) : filter α := (⨅ s ∈ {s : set α | a ∈ s ∧ open' s}, principal s)

lemma return_le_nhds : return ≤ (nhds : α → filter α) :=
take a, le_infi $ take s, le_infi $ take ⟨h₁, _⟩, principal_mono^.mpr $ by simp [h₁]

@[simp]
lemma nhds_neq_bot {a : α} : nhds a ≠ ⊥ :=
suppose nhds a = ⊥,
have return a = (⊥ : filter α),
  from lattice.bot_unique $ this ▸ return_le_nhds a,
return_neq_bot this

end topology
