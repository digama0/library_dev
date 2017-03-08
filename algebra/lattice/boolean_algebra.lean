/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Type class hierarchy for Boolean algebras.
-/


import .bounded_lattice

universes u
variables {α : Type u} {x y z : α}

namespace lattice

class distrib_lattice α extends lattice α :=
(sup_inf : ∀x y z : α, x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z))

section distrib_lattice
variables [distrib_lattice α]

lemma sup_inf_left : ∀{x y z : α}, x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z) :=
distrib_lattice.sup_inf

lemma sup_inf_right : (y ⊓ z) ⊔ x = (y ⊔ x) ⊓ (z ⊔ x) :=
by simp [sup_inf_left, λy:α, @sup_comm α _ y x]

lemma inf_sup_left : x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) :=
calc x ⊓ (y ⊔ z) = (x ⊓ (x ⊔ z)) ⊓ (y ⊔ z)       : by rw [inf_sup_self]
             ... = x ⊓ ((x ⊓ y) ⊔ z)             : by simp [inf_assoc, sup_inf_right]
             ... = (x ⊔ (x ⊓ y)) ⊓ ((x ⊓ y) ⊔ z) : by rw [sup_inf_self]
             ... = ((x ⊓ y) ⊔ x) ⊓ ((x ⊓ y) ⊔ z) : by rw [sup_comm]
             ... = (x ⊓ y) ⊔ (x ⊓ z)             : by rw [sup_inf_left]

lemma inf_sup_right : (y ⊔ z) ⊓ x = (y ⊓ x) ⊔ (z ⊓ x) :=
by simp [inf_sup_left, λy:α, @inf_comm α _ y x] 

end distrib_lattice

class boolean_algebra α extends distrib_lattice α, bounded_lattice α, has_neg α, has_sub α :=
(inf_neg_eq_bot : ∀x:α, x ⊓ - x = ⊥)
(sup_neg_eq_top : ∀x:α, x ⊔ - x = ⊤)
(sub_eq : ∀x y:α, x - y = x ⊓ - y)

section boolean_algebra
variables [boolean_algebra α]

@[simp]
lemma inf_neg_eq_bot : x ⊓ - x = ⊥ :=
boolean_algebra.inf_neg_eq_bot x

@[simp]
lemma neg_inf_eq_bot : - x ⊓ x = ⊥ :=
eq.trans inf_comm inf_neg_eq_bot

@[simp]
lemma sup_neg_eq_top : x ⊔ - x = ⊤ :=
boolean_algebra.sup_neg_eq_top x

@[simp]
lemma neg_sup_eq_top : - x ⊔ x = ⊤ :=
eq.trans sup_comm sup_neg_eq_top

lemma sub_eq : x - y = x ⊓ - y :=
boolean_algebra.sub_eq x y

lemma neg_unique (i : x ⊓ y = ⊥) (s : x ⊔ y = ⊤) : - x = y :=
have (- x ⊓ x) ⊔ (- x ⊓ y) = (y ⊓ x) ⊔ (y ⊓ - x),
  by rsimp,
have - x ⊓ (x ⊔ y) = y ⊓ (x ⊔ - x),
  begin [smt] eblast_using inf_sup_left end,
by rsimp

@[simp]
lemma neg_top : - ⊤ = (⊥:α) :=
neg_unique (by simp) (by simp)

@[simp]
lemma neg_bot : - ⊥ = (⊤:α) :=
neg_unique (by simp) (by simp)

@[simp]
lemma neg_neg : - (- x) = x :=
neg_unique (by simp) (by simp)

lemma neg_eq_neg_of_eq (h : - x = - y) : x = y :=
have - - x = - - y,
  from congr_arg neg h,
by simp [neg_neg] at this; assumption

@[simp]
lemma neg_eq_neg_iff : - x = - y ↔ x = y :=
⟨neg_eq_neg_of_eq, congr_arg neg⟩

@[simp]
lemma neg_inf : - (x ⊓ y) = -x ⊔ -y :=
neg_unique -- TODO: try rsimp if it supports custom lemmas
  (calc (x ⊓ y) ⊓ (- x ⊔ - y) = (y ⊓ (x ⊓ - x)) ⊔ (x ⊓ (y ⊓ - y)) : by rw [inf_sup_left]; ac_refl
                          ... = ⊥ : by simp)
  (calc (x ⊓ y) ⊔ (- x ⊔ - y) = (- y ⊔ (x ⊔ - x)) ⊓ (- x ⊔ (y ⊔ - y)) : by rw [sup_inf_right]; ac_refl
                          ... = ⊤ : by simp)

@[simp]
lemma neg_sup : - (x ⊔ y) = -x ⊓ -y :=
begin [smt] eblast_using [neg_neg, neg_inf] end

lemma neg_le_neg (h : y ≤ x) : - x ≤ - y :=
le_of_inf_eq $ 
  calc -x ⊓ -y = - (x ⊔ y) : neg_sup^.symm
           ... = -x        : congr_arg neg $ sup_of_le_left h

end boolean_algebra

end lattice
