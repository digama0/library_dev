/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Theory of uniform spaces.
-/
import algebra.lattice.filter

open set lattice filter

universes u v
variables {α : Type u} {β : Type u}

def refl_rel {α : Type u} := {p : α × α | p.1 = p.2}

def trans_rel {α : Type u} (r₁ r₂ : set (α×α)) :=
{p : α × α | ∃z:α, (p.1, z) ∈ r₁ ∧ (z, p.2) ∈ r₂}

/- uniformity -/

class uniform_space (α : Type u) :=
(uniformity : filter (α × α))
(refl       : principal refl_rel ≤ uniformity)
(symm       : (λx : α × α, (x.2, x.1)) <$> uniformity ≤ uniformity)
(trans      : (⨅s∈uniformity^.sets, ⨅t∈uniformity^.sets, principal (trans_rel s t)) ≤ uniformity)

section uniform_space
variables [uniform_space α]

def uniformity : filter (α × α) := uniform_space.uniformity α

lemma refl_le_uniformity : principal {p : α × α | p^.1 = p^.2} ≤ uniformity :=
uniform_space.refl α

lemma symm_le_uniformity : (λx : α × α, (x.2, x.1)) <$> uniformity ≤ uniformity :=
uniform_space.symm α

lemma trans_le_uniformity :
  (⨅s∈(uniformity^.sets : set (set (α×α))), ⨅t∈(uniformity^.sets : set (set (α×α))),
    principal (trans_rel s t)) ≤ uniformity :=
uniform_space.trans α

lemma uniformity_le_symm : uniformity ≤ (λx : α × α, (x.2, x.1)) <$> uniformity :=
calc uniformity = id <$> uniformity : (monad.id_map _)^.symm
  ... = ((λx : α × α, (x.2, x.1)) ∘ (λx : α × α, (x.2, x.1))) <$> uniformity :
    congr_arg (λf : (α×α)→(α×α), f <$> uniformity) (by apply funext; intro x; cases x; refl)
  ... = (map (λx : α × α, (x.2, x.1)) ∘ map (λx : α × α, (x.2, x.1))) uniformity :
    congr map_compose rfl 
  ... ≤ (λx : α × α, (x.2, x.1)) <$> uniformity : map_mono symm_le_uniformity

lemma uniformity_eq_symm : uniformity = (λx : α × α, (x.2, x.1)) <$> uniformity :=
le_antisymm uniformity_le_symm symm_le_uniformity

/- neighbourhood -/
definition nhds (x : α) : filter α :=
(⨅s∈(uniformity^.sets : set (set (α×α))), principal {y | (x, y) ∈ s})

lemma pure_le_nhds {x : α} : pure x ≤ nhds x :=
le_infi $ take s, le_infi $ assume hs : s ∈ uniformity.sets,
  have (x, x) ∈ s,
    from refl_le_uniformity hs rfl,
  principal_mono.mpr $ by simp [this]

/- cauchy filters -/
definition cauchy (f : filter α) : Prop := filter.prod f f ≤ uniformity

lemma cauchy_downwards {f g : filter α} (h_c : cauchy f) (h_le : g ≤ f) : cauchy g :=
le_trans (filter.prod_mono h_le h_le) h_c

lemma cauchy_nhds {a : α} : cauchy (nhds a) :=
calc filter.prod (nhds a) (nhds a) ≤ uniformity :
  infi_le _ _



#exit

def Cauchy (α : Type u) [uniform_space α] : Type u := { f : filter α // cauchy f ∧ f ≠ bot }

def Cauchy.uniformity (α : Type u) [uniform_space α] : filter (Cauchy α × Cauchy α) :=
⨅ s ∈ (@uniformity α _)^.sets, principal {p : Cauchy α × Cauchy α | ∃(t : set α),
  t ∈ (p.1^.val ⊔ p.2^.val)^.sets ∧ set.prod t t ⊆ s}

def completion_space : uniform_space (Cauchy α) :=
{ uniformity := Cauchy.uniformity α,
  refl       := le_infi $ take s, le_infi $ take h,
  begin
    simp,
    intros a b h_ab, subst h_ab,
    note h' := a^.property^.left h,
  end,
  symm      := _, -- le_infi $ take s, le_infi $ take h, _,
  trans     := _ }

end uniform_space
