/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Theory of uniform spaces.
-/
import algebra.lattice.filter

open set lattice filter

universe u
variables {α : Type u}

/- uniformity -/

class uniform_space (α : Type u) :=
(uniformity              : filter (α × α))
(principal_le_uniformity : principal {p : α × α | p.1 = p.2} ≤ uniformity)
(swap_uniformity_le      : (λx : α × α, (x.2, x.1)) <$> uniformity ≤ uniformity)
(transitive              :
  (do p₁ ← uniformity, p₂ ← uniformity, principal {p | p = (p₁.1, p₂.2) ∧ p₁.2 = p₂.1}) ≤ uniformity)

namespace uniform_space
section
variables [uniform_space α]

lemma uniformity_le_swap : uniformity α ≤ (λx : α × α, (x.2, x.1)) <$> uniformity α :=
calc
  uniformity α = id <$> uniformity α : (monad.id_map _)^.symm
           ... = ((λx : α × α, (x.2, x.1)) ∘ (λx : α × α, (x.2, x.1))) <$> uniformity α :
    congr_arg (λf, f <$> (uniformity α)) (by apply funext; intro x; cases x; refl)
           ... = (map (λx : α × α, (x.2, x.1)) ∘ map (λx : α × α, (x.2, x.1))) (uniformity α) :
    congr map_compose rfl 
           ... ≤ (λx : α × α, (x.2, x.1)) <$> uniformity α : map_mono (swap_uniformity_le α)

lemma uniformity_eq_swap : uniformity α = (λx : α × α, (x.2, x.1)) <$> uniformity α :=
le_antisymm uniformity_le_swap (swap_uniformity_le α)

/- neighbourhood -/
definition nhds (x : α) : filter α := uniformity α >>= λp, principal {y | p = (x, y)}

lemma pure_le_nhds {x : α} : pure x ≤ nhds x :=
calc pure x ≤ (principal {p : α × α | p.1 = p.2} >>= λp, principal {y | p = (x, y)}) : 
     by simp [pure, principal_bind]; exact ⟨(x, x), rfl, rfl⟩
  ... <= nhds x : bind_mono2 (principal_le_uniformity α)

/- cauchy filters -/
definition cauchy (f : filter α) : Prop := prod.mk <$> f <*> f ≤ uniformity α

lemma cauchy_downwards {f g : filter α} (h_c : cauchy f) (h_le : g ≤ f) : cauchy g :=
le_trans (seq_mono (map_mono h_le) h_le) h_c

lemma cauchy_nhds {a : α} : cauchy (nhds a) :=
calc prod.mk <$> nhds a <*> nhds a ≤
    do { p₁ ← (λx : α × α, (x.2, x.1)) <$> uniformity α, p₂ ← uniformity α, 
      principal {p | p = (p₁.2, p₂.2) ∧ p₁.1 = a ∧ p₂.1 = a} } :
  begin -- should be done by auto
    rw [-uniformity_eq_swap],
    simp [nhds, map_bind, bind_assoc, seq_eq_bind_map, principal_bind],
    apply bind_mono,
    apply univ_mem_sets',
    simp [supr_le_iff, image_subset_iff_subset_vimage, bounded_forall_image_iff],
    intros p₁ a₁ h₁,
    apply bind_mono,
    apply univ_mem_sets',
    simp [image_subset_iff_subset_vimage, bounded_forall_image_iff],
    intros p₂ a₂ h₂,
    simp [h₁, h₂]
  end
  ... ≤ (do p₁ ← uniformity α, p₂ ← uniformity α, principal {p | p = (p₁.1, p₂.2) ∧ p₁.2 = p₂.1}) :
  begin -- should be done by auto
    simp [seq_bind_eq],
    apply bind_mono, apply univ_mem_sets', intro p₁,
    apply bind_mono, apply univ_mem_sets', intro p₂,
    simp,
    cc
  end
  ... ≤ uniformity α : transitive _

end


def Cauchy (α : Type u) [uniform_space α] : Type u := { f : filter α // cauchy f ∧ f ≠ bot }

def completion_space : uniform_space (Cauchy α) :=
{ uniformity              := ⨅ s ∈ (uniformity α)^.sets,
    principal {p : Cauchy α × Cauchy α | @prod.mk α α <$> p.1^.val <*> p.2^.val ≤ principal s },
  principal_le_uniformity := le_infi $ take s, le_infi $ take h,
  begin
    simp,
    intros a a' h, subst h,
    exact a^.property^.left h
  end,
  swap_uniformity_le      := le_infi $ take s, le_infi $ take h, le_trans
    (map_mono $ infi_le_of_le _ $ infi_le _ $ swap_uniformity_le α h) 
    begin simp [image_subset_iff_subset_vimage] end,
  transitive              := _ }

end uniform_space

