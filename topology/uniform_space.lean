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

instance : monad set :=
{ monad .
  pure := λα a, {a},
  bind := λα β s f, ⋃i∈s, f i,
  map  := λα β, set.image,
  pure_bind := take α β x f, by simp,
  bind_assoc := take α β γ s f g, set.ext $ take a,
    by simp; exact ⟨take ⟨b, ag, a, as, bf⟩, ⟨a, as, b, bf, ag⟩, take ⟨a, as, b, bf, ag⟩, ⟨b, ag, a, as, bf⟩⟩,
  id_map := take α, functor.id_map,
  bind_pure_comp_eq_map := take α β f s, set.ext $ by simp [set.image, eq_comm] }

lemma fmap_eq_image {f : α → β} {s : set α} : f <$> s = f ' s :=
rfl

lemma mem_seq {f : set (α → β)} {s : set α} {b : β} :
  b ∈ (f <*> s) ↔ (∃(f' : α → β), ∃a ∈ s, f' ∈ f ∧ b = f' a) :=
begin
  simp [seq_eq_bind_map, bind],
  apply exists_congr,
  intro f',
  exact ⟨take ⟨hf', a, ha, h_eq⟩, ⟨a, h_eq^.symm, ha, hf'⟩,
    take ⟨a, h_eq, ha, hf'⟩, ⟨hf', a, ha, h_eq^.symm⟩⟩
end

/- uniformity -/

class uniform_space (α : Type u) :=
(uniformity              : filter (α × α))
(principal_le_uniformity : principal {p : α × α | p.1 = p.2} ≤ uniformity)
(swap_uniformity_le      : (λx : α × α, (x.2, x.1)) <$> uniformity ≤ uniformity)
(transitive              :
  (do p₁ ← uniformity, p₂ ← uniformity, principal {p | p = (p₁.1, p₂.2) ∧ p₁.2 = p₂.1}) ≤ uniformity)

section uniform_space
variables [uniform_space α]

def uniformity : filter (α × α) := uniform_space.uniformity α

lemma principal_le_uniformity : principal {p : α × α | p^.1 = p^.2} ≤ uniformity :=
uniform_space.principal_le_uniformity α

lemma swap_uniformity_le : (λx : α × α, (x.2, x.1)) <$> uniformity ≤ uniformity :=
uniform_space.swap_uniformity_le α

lemma transitive_uniformity :
  (do p₁ ← uniformity, p₂ ← uniformity, principal {p : α × α | p = (p₁.1, p₂.2) ∧ p₁.2 = p₂.1}) ≤ uniformity :=
uniform_space.transitive α

lemma uniformity_le_swap : uniformity ≤ (λx : α × α, (x.2, x.1)) <$> uniformity :=
calc uniformity = id <$> uniformity : (monad.id_map _)^.symm
  ... = ((λx : α × α, (x.2, x.1)) ∘ (λx : α × α, (x.2, x.1))) <$> uniformity :
    congr_arg (λf : (α×α)→(α×α), f <$> uniformity) (by apply funext; intro x; cases x; refl)
  ... = (map (λx : α × α, (x.2, x.1)) ∘ map (λx : α × α, (x.2, x.1))) uniformity :
    congr map_compose rfl 
  ... ≤ (λx : α × α, (x.2, x.1)) <$> uniformity : map_mono swap_uniformity_le

lemma uniformity_eq_swap : uniformity = (λx : α × α, (x.2, x.1)) <$> uniformity :=
le_antisymm uniformity_le_swap swap_uniformity_le

/- neighbourhood -/
definition nhds (x : α) : filter α := uniformity >>= λp, principal {y | p = (x, y)}

lemma pure_le_nhds {x : α} : pure x ≤ nhds x :=
calc pure x ≤ (principal {p : α × α | p.1 = p.2} >>= λp, principal {y | p = (x, y)}) : 
     by simp [pure, principal_bind]; exact ⟨(x, x), rfl, rfl⟩
  ... <= nhds x : bind_mono2 principal_le_uniformity

/- cauchy filters -/
definition cauchy (f : filter α) : Prop := prod.mk <$> f <*> f ≤ uniformity

lemma cauchy_downwards {f g : filter α} (h_c : cauchy f) (h_le : g ≤ f) : cauchy g :=
le_trans (seq_mono (map_mono h_le) h_le) h_c

lemma cauchy_nhds {a : α} : cauchy (nhds a) :=
calc prod.mk <$> nhds a <*> nhds a ≤
    do { p₁ ← (λx : α × α, (x.2, x.1)) <$> uniformity, p₂ ← uniformity,
      principal {p | p = (p₁.2, p₂.2) ∧ p₁.1 = a ∧ p₂.1 = a} } :
  begin -- should be done by auto
    rw [-uniformity_eq_swap],
    simp [nhds, map_bind, bind_assoc, seq_eq_bind_map, principal_bind],
    apply bind_mono,
    apply univ_mem_sets',
    simp [supr_le_iff, image_subset_iff_subset_vimage, bounded_forall_image_iff],
    intros a₁ a₂ a₃ h, cases h with h₁ h₂, subst h₁, subst h₂,
    apply bind_mono,
    apply univ_mem_sets',
    simp [image_subset_iff_subset_vimage, bounded_forall_image_iff],
    intros a₃ a₄ a₅, intro h, cases h with h₁ h₂, subst h₁, subst h₂,
    simp
  end
  ... ≤ (do p₁ ← uniformity, p₂ ← uniformity, principal {p | p = (p₁.1, p₂.2) ∧ p₁.2 = p₂.1}) :
  begin -- should be done by auto
    simp [seq_bind_eq],
    apply bind_mono, apply univ_mem_sets', intro p₁,
    apply bind_mono, apply univ_mem_sets', intro p₂,
    simp,
    cc
  end
  ... ≤ uniformity : transitive_uniformity

def Cauchy (α : Type u) [uniform_space α] : Type u := { f : filter α // cauchy f ∧ f ≠ bot }

#exit

def completion_space : uniform_space (Cauchy α) :=
{ uniformity              := ⨅ s ∈ uniformity^.sets,
    principal {p : Cauchy α × Cauchy α | ∃t, t ∈ p.1^.val^.sets },
  principal_le_uniformity := le_infi $ take s, le_infi $ take h, _,
  swap_uniformity_le      := le_infi $ take s, le_infi $ take h, _,
  transitive              := _ }

end uniform_space
