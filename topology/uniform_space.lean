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

lemma mem_seq_iff {f : set (α → β)} {s : set α} {b : β} :
  b ∈ (f <*> s) ↔ (∃(f' : α → β), ∃a ∈ s, f' ∈ f ∧ b = f' a) :=
begin
  simp [seq_eq_bind_map, bind],
  apply exists_congr,
  intro f',
  exact ⟨take ⟨hf', a, ha, h_eq⟩, ⟨a, h_eq^.symm, ha, hf'⟩,
    take ⟨a, h_eq, ha, hf'⟩, ⟨hf', a, ha, h_eq^.symm⟩⟩
end

lemma set.mem_prod_iff {s : set α} {t : set β} {p : α × β} :
  p ∈ prod.mk <$> s <*> t ↔ (p.1 ∈ s ∧ p.2 ∈ t)  :=
begin
  cases p with a b,
  simp [mem_seq_iff, fmap_eq_image, set.image],
  exact ⟨take ⟨f, b', hb', ab_eq, a', ha', mka'_eq⟩,
    begin
      rw [-mka'_eq] at ab_eq,
      rw [prod.mk.inj_iff] at ab_eq,
      rw [ab_eq^.left, ab_eq^.right],
      exact ⟨ha', hb'⟩
    end,
    take ⟨ha, hb⟩, ⟨prod.mk a, b, hb, rfl, a, ha, rfl⟩⟩
end

lemma set.prod_comm {s : set α} {t : set β} :
  {x : β × α | (x.snd, x.fst) ∈ prod.mk <$> s <*> t} = prod.mk <$> t <*> s :=
set.ext $ by simp [set.mem_prod_iff]; intros; trivial

namespace filter

def prod (f : filter α) (g : filter β) : filter (α × β) :=
⨅s ∈ f^.sets, ⨅t ∈ g^.sets, principal (prod.mk <$> s <*> t)

lemma prod_mem_prod {s : set α} {t : set β} {f : filter α} {g : filter β} 
  (hs : s ∈ f^.sets) (ht : t ∈ g^.sets) : prod.mk <$> s <*> t ∈ (prod f g)^.sets :=
le_principal_iff^.mp $ show prod f g ≤ principal (prod.mk <$> s <*> t),
  from infi_le_of_le s $ infi_le_of_le hs $ infi_le_of_le t $ infi_le _ ht

lemma prod_mono {f₁ f₂ : filter α} {g₁ g₂ : filter β} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) :
  prod f₁ g₁ ≤ prod f₂ g₂ :=
infi_le_infi $ take s, infi_le_infi2 $ take hs, ⟨hf hs,
  infi_le_infi $ take t, infi_le_infi2 $ take ht, ⟨hg ht, le_refl _⟩⟩

lemma prod_le_comm {f : filter α} {g : filter β} : map (λp:β×α, (p.2, p.1)) (prod g f) ≤ prod f g :=
le_infi $ take s, le_infi $ take hs, le_infi $ take t, le_infi $ take ht, 
  by simp [set.prod_comm, prod_mem_prod, hs, ht]

lemma prod_comm {f : filter α} {g : filter β} : prod f g = map (λp:β×α, (p.2, p.1)) (prod g f) :=
le_antisymm
  ( have ((λ (p : β × α), (p.snd, p.fst)) ∘ λ (p : α × β), (p.snd, p.fst)) = id, 
      by apply funext; intro x; cases x; simp,
    calc prod f g = (map (λp:β×α, (p.2, p.1)) ∘ map (λp:α×β, (p.2, p.1))) (prod f g) :
        by simp [map_compose, this]
      ... ≤ map (λp:β×α, (p.2, p.1)) (prod g f) : map_mono $ prod_le_comm)
  prod_le_comm

end filter

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
definition cauchy (f : filter α) : Prop := filter.prod f f ≤ uniformity

lemma cauchy_downwards {f g : filter α} (h_c : cauchy f) (h_le : g ≤ f) : cauchy g :=
le_trans (filter.prod_mono h_le h_le) h_c

lemma cauchy_nhds {a : α} : cauchy (nhds a) :=
calc filter.prod (nhds a) (nhds a) ≤
  do {
    p₁ ← (λx : α × α, (x.2, x.1)) <$> uniformity,
    p₂ ← uniformity,
    principal {p | p = (p₁.2, p₂.2) ∧ p₁.1 = a ∧ p₂.1 = a} } :
  begin
    intro s,
    simp [mem_bind_sets],
    exact take ⟨d, hd, _⟩, _
  end
/-
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
-/
  ... ≤ (do p₁ ← uniformity, p₂ ← uniformity, principal {p | p = (p₁.1, p₂.2) ∧ p₁.2 = p₂.1}) :
  begin -- should be done by auto
    simp [seq_bind_eq],
    apply bind_mono, apply univ_mem_sets', intro p₁,
    apply bind_mono, apply univ_mem_sets', intro p₂,
    simp,
    cc
  end
  ... ≤ uniformity : transitive_uniformity

#exit

def Cauchy (α : Type u) [uniform_space α] : Type u := { f : filter α // cauchy f ∧ f ≠ bot }

def Cauchy.uniformity (α : Type u) [uniform_space α] : filter (Cauchy α × Cauchy α) :=
⨅ s ∈ (@uniformity α _)^.sets, principal {p : Cauchy α × Cauchy α | ∃(t : set α),
  t ∈ (p.1^.val ⊓ p.2^.val)^.sets ∧ (@prod.mk α α) <$> t <*> t ⊆ s}

def completion_space : uniform_space (Cauchy α) :=
{ uniformity              := Cauchy.uniformity α,
  principal_le_uniformity := le_infi $ take s, le_infi $ take h,
  begin
    simp,
    intros a b h_ab, subst h_ab,
    note h' := a^.property^.left h,
  end,
  swap_uniformity_le      := _, -- le_infi $ take s, le_infi $ take h, _,
  transitive              := _ }

end uniform_space
