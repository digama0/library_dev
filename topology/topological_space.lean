/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Theory of topological spaces.
-/
import algebra.lattice.filter

open set filter

universes u v

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

class topology (α : Type u) :=
(nhds           : α → filter α)
(return_le_nhds : return ≤ nhds)

section topology

variables {α : Type u} {ι : Type v} {a a₁ a₂ : α} {s s₁ s₂ : set α}

def nhds [t : topology α] : α → filter α :=
@topology.nhds α t

lemma return_le_nhds [t : topology α] : return ≤ (nhds : α → filter α) :=
@topology.return_le_nhds α t

variables [topology α]

/- nhds -/
@[simp]
lemma nhds_neq_bot {a : α} : nhds a ≠ ⊥ :=
suppose nhds a = ⊥,
have return a = (⊥ : filter α),
  from lattice.bot_unique $ this ▸ return_le_nhds a,
return_neq_bot this

def open' (s : set α) : Prop := ∀a ∈ s, nhds a ≤ principal s

/- open -/
lemma open'_empty : open' (∅ : set α) := by simp [open']

lemma open'_univ : open' (univ : set α) := by simp [open', univ_mem_sets]

lemma open'_inter (h₁ : open' s₁) (h₂ : open' s₂) : open' (s₁ ∩ s₂) :=
take a h, le_trans (lattice.le_inf (h₁ a h.left) (h₂ a h.right)) (by simp; exact subset.refl _)

lemma open'_sUnion {s : set (set α)} (h : ∀t ∈ s, open' t) : open' (⋃₀ s) :=
take a ⟨t, hts, hat⟩, le_trans (h t hts a hat) (principal_mono^.mpr $ subset_sUnion_of_mem hts)

lemma open'_Union {f : ι → set α} (h : ∀i, open' (f i)) : open' (⋃i, f i) :=
open'_sUnion $ take t ⟨i, (heq : t = f i)⟩, heq^.symm ▸ h i

/- closed -/
def closed (s : set α) : Prop := ∀a ∈ s, principal s ⊓ nhds a ≠ ⊥

lemma closed_empty : closed (∅ : set α) := by simp [closed]

lemma closed_univ : closed (univ : set α) := by simp [closed, univ_mem_sets, principal_univ]

#check lattice.le_inf_sup

lemma closed_union (h₁ : closed s₁) (h₂ : closed s₂) : closed (s₁ ∪ s₂)
| a (or.inl h) := _
| a (or.inr h) := _

/- interior -/
def interior (s : set α) : set α := {a | nhds a ≤ principal s }

/- closure -/
def closure (s : set α) : set α := {a | principal s ⊓ nhds a ≠ ⊥ }

end topology
