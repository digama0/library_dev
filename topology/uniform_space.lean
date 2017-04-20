/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Theory of uniform spaces.
-/
import algebra.lattice.filter .topological_space .continuity
open set lattice filter

universes u v w x

section
variables {α : Type u} {β : Type v}

def id_rel {α : Type u} := {p : α × α | p.1 = p.2}

def comp_rel {α : Type u} (r₁ r₂ : set (α×α)) :=
{p : α × α | ∃z:α, (p.1, z) ∈ r₁ ∧ (z, p.2) ∈ r₂}

lemma monotone_comp_rel [weak_order β] {f g : β → set (α×α)}
  (hf : monotone f) (hg : monotone g) : monotone (λx, comp_rel (f x) (g x)) :=
take a b h p ⟨z, h₁, h₂⟩, ⟨z, hf h h₁, hg h h₂⟩

lemma prod_mk_mem_comp_rel {a b c : α} {s t : set (α×α)} (h₁ : (a, c) ∈ s) (h₂ : (c, b) ∈ t) :
  (a, b) ∈ comp_rel s t :=
⟨c, h₁, h₂⟩

@[simp]
lemma set.prod_singleton_singleton {a : α} {b : β} :
  set.prod {a} {b} = ({(a, b)} : set (α×β)) :=
set.ext $ take ⟨a', b'⟩, by simp [set.prod]

@[simp]
lemma lift'_id {f : filter α} : f.lift' id = f :=
le_antisymm
  (take s hs, mem_lift' hs)
  (le_infi $ take s, le_infi $ take hs, by simp [hs])

lemma le_lift' {f : filter α} {h : set α → set β} {g : filter β}
  (h_le : ∀s∈f.sets, h s ∈ g.sets) : g ≤ f.lift' h :=
le_infi $ take s, le_infi $ take hs, by simp [h_le]; exact h_le s hs

/- uniformity -/

class uniform_space (α : Type u) :=
(uniformity : filter (α × α))
(refl       : principal id_rel ≤ uniformity)
(symm       : prod.swap <$> uniformity ≤ uniformity)
(trans      : uniformity^.lift (λs, uniformity^.lift' (comp_rel s)) ≤ uniformity)

section uniform_space
variables [uniform_space α]

def uniformity : filter (α × α) := uniform_space.uniformity α

lemma refl_le_uniformity : principal {p : α × α | p^.1 = p^.2} ≤ uniformity :=
uniform_space.refl α

lemma refl_mem_uniformity {x : α} {s : set (α × α)} (h : s ∈ (@uniformity α _).sets) :
  (x, x) ∈ s :=
refl_le_uniformity h rfl

lemma symm_le_uniformity : map (@prod.swap α α) uniformity ≤ uniformity :=
uniform_space.symm α

lemma trans_le_uniformity' :
  uniformity^.lift (λs:set (α×α), uniformity^.lift' (comp_rel s)) ≤ uniformity :=
uniform_space.trans α

lemma trans_le_uniformity :
  uniformity^.lift' (λt:set (α×α), comp_rel t t) ≤ uniformity :=
calc uniformity^.lift' (λt:set (α×α), comp_rel t t) ≤
        uniformity^.lift (λs:set (α×α), uniformity^.lift' (comp_rel s)) :
    (le_infi $ take s, le_infi $ take hs, le_infi $ take t, le_infi $ take ht,
      infi_le_of_le (s ∩ t) $
      infi_le_of_le (inter_mem_sets hs ht) $
      principal_mono.mpr $ take x ⟨z, ⟨h₁, _⟩, ⟨_, h₂⟩⟩, ⟨z, h₁, h₂⟩)
  ... ≤ uniformity : trans_le_uniformity'

lemma trans_mem_uniformity_sets {s : set (α × α)} (hs : s ∈ (@uniformity α _).sets) :
  ∃t∈(@uniformity α _).sets, comp_rel t t ⊆ s :=
have s ∈ (uniformity^.lift' (λt:set (α×α), comp_rel t t)).sets,
  from trans_le_uniformity hs,
(mem_lift'_iff $ monotone_comp_rel monotone_id monotone_id).mp this

lemma uniformity_le_symm : uniformity ≤ map (@prod.swap α α) uniformity :=
calc uniformity = id <$> uniformity : (monad.id_map _)^.symm
  ... = (prod.swap.{u u} ∘ prod.swap) <$> uniformity :
    congr_arg (λf : (α×α)→(α×α), f <$> uniformity) (by apply funext; intro x; cases x; refl)
  ... = (map prod.swap ∘ map prod.swap) uniformity :
    congr map_compose rfl
  ... ≤ prod.swap.{u u} <$> uniformity : map_mono symm_le_uniformity

lemma uniformity_eq_symm : uniformity = (@prod.swap α α) <$> uniformity :=
le_antisymm uniformity_le_symm symm_le_uniformity

lemma uniformity_lift_le_swap {g : set (α×α) → filter β} {f : filter β} (hg : monotone g)
  (h : uniformity^.lift (λs, g (vimage prod.swap s)) ≤ f) : uniformity^.lift g ≤ f :=
le_trans
  (lift_mono uniformity_le_symm (le_refl _))
  (by rw [map_lift_eq2 hg, image_swap_eq_vimage_swap]; exact h)

lemma uniformity_lift_le_trans {f : set (α×α) → filter β} (h : monotone f):
  uniformity.lift (λs, uniformity.lift (λt, f (comp_rel s t))) ≤ uniformity.lift f :=
calc uniformity.lift (λs, uniformity.lift (λt, f (comp_rel s t))) =
    (uniformity.lift (λs:set (α×α), uniformity.lift' (λt:set (α×α), comp_rel s t)))^.lift f :
  begin
    rw [lift_assoc],
    apply congr_arg, apply funext, intro s,
    rw [lift_lift'_assoc],
    exact monotone_comp_rel monotone_const monotone_id,
    exact h,
    exact (monotone_lift' monotone_const $ monotone_lam $
      take t, monotone_comp_rel monotone_id monotone_const)
  end
  ... ≤ uniformity.lift f : lift_mono trans_le_uniformity' (le_refl _)

instance topological_space_of_uniformity : topological_space α :=
{ open'       := λs, ∀x∈s, { p : α × α | p.1 = x → p.2 ∈ s } ∈ (uniformity.sets : set (set (α×α))),
  open_univ   := by simp; intros; apply univ_mem_sets,
  open_inter  := take s t hs ht x ⟨xs, xt⟩,
    uniformity.upwards_sets (inter_mem_sets (hs x xs) (ht x xt)) $
      take p ⟨ps, pt⟩ h, ⟨ps h, pt h⟩,
  open_sUnion := take s hs x ⟨t, ts, xt⟩,
    uniformity.upwards_sets (hs t ts x xt) $
      take p ph h, ⟨t, ts, ph h⟩ }

lemma mem_nhds_uniformity_iff {x : α} {s : set α} :
  (s ∈ (nhds x).sets) ↔ ({p : α × α | p.1 = x → p.2 ∈ s} ∈ (@uniformity α _).sets) :=
⟨ begin
    simp [mem_nhds_sets_iff],
    exact take ⟨t, ht, ts, xt⟩, uniformity.upwards_sets (ht x xt) $
      take ⟨x', y⟩ h eq, ts $ h eq
  end,

  take hs,
  mem_nhds_sets_iff.mpr $ ⟨{x | {p : α × α | p.1 = x → p.2 ∈ s} ∈ (@uniformity α _).sets},
    take x', assume hx' : {p : α × α | p.fst = x' → p.snd ∈ s} ∈ (@uniformity α _).sets,
      refl_mem_uniformity hx' rfl,
    take x' hx',
      let ⟨t, ht, tr⟩ := trans_mem_uniformity_sets hx' in
      uniformity.upwards_sets ht $
      take ⟨a, b⟩ hp' (eq : a = x'),
      have hp : (x', b) ∈ t, from eq ▸ hp',
      show {p : α × α | p.fst = b → p.snd ∈ s} ∈ (@uniformity α _).sets,
        from uniformity.upwards_sets ht $
          take ⟨a, b'⟩ hp' (heq : a = b),
          have (b, b') ∈ t, from heq ▸ hp',
          have (x', b') ∈ comp_rel t t, from ⟨b, hp, this⟩,
          show b' ∈ s,
            from tr this rfl,
    hs⟩⟩

lemma nhds_eq_uniformity {x : α} :
  nhds x = uniformity^.lift' (λs:set (α×α), {y | (x, y) ∈ s}) :=
filter_eq $ set.ext $ take s,
  begin
    rw [mem_lift'_iff], tactic.swap, apply monotone_vimage,
    simp [mem_nhds_uniformity_iff],
    exact ⟨take h, ⟨_, h, take y h, h rfl⟩,
      take ⟨t, h₁, h₂⟩,
      uniformity.upwards_sets h₁ $
      take ⟨x', y⟩ hp (eq : x' = x), h₂ $
      show (x, y) ∈ t, from eq ▸ hp⟩
  end

lemma mem_nhds_left {x : α} {s : set (α×α)} (h : s ∈ (uniformity.sets : set (set (α×α)))) :
  {y : α | (x, y) ∈ s} ∈ (nhds x)^.sets :=
have nhds x ≤ principal {y : α | (x, y) ∈ s},
  by rw [nhds_eq_uniformity]; exact infi_le_of_le s (infi_le _ h),
by simp at this; assumption

lemma mem_nhds_right {y : α} {s : set (α×α)} (h : s ∈ (uniformity.sets : set (set (α×α)))) :
  {x : α | (x, y) ∈ s} ∈ (nhds y)^.sets :=
mem_nhds_left (symm_le_uniformity h)

lemma lift_nhds_left {x : α} {g : set α → filter β} (hg : monotone g) :
  (nhds x)^.lift g = uniformity^.lift (λs:set (α×α), g {y | (x, y) ∈ s}) :=
eq.trans
  begin
    rw [nhds_eq_uniformity],
    exact (filter.lift_assoc $ monotone_comp monotone_vimage $ monotone_comp monotone_vimage monotone_principal)
  end
  (congr_arg _ $ funext $ take s, filter.lift_principal hg)

lemma lift_nhds_right {x : α} {g : set α → filter β} (hg : monotone g) :
  (nhds x)^.lift g = uniformity^.lift (λs:set (α×α), g {y | (y, x) ∈ s}) :=
calc (nhds x)^.lift g = uniformity^.lift (λs:set (α×α), g {y | (x, y) ∈ s}) : lift_nhds_left hg
  ... = ((@prod.swap α α) <$> uniformity)^.lift (λs:set (α×α), g {y | (x, y) ∈ s}) : by rw [-uniformity_eq_symm]
  ... = uniformity^.lift (λs:set (α×α), g {y | (x, y) ∈ image prod.swap s}) :
    map_lift_eq2 $ monotone_comp monotone_vimage hg
  ... = _ : by simp [image_swap_eq_vimage_swap]

lemma nhds_nhds_eq_uniformity_uniformity_prod {a b : α} :
  filter.prod (nhds a) (nhds b) =
  uniformity^.lift (λs:set (α×α), uniformity^.lift' (λt:set (α×α),
    set.prod {y : α | (y, a) ∈ s} {y : α | (b, y) ∈ t})) :=
show (nhds a)^.lift (λs:set α, (nhds b)^.lift (λt:set α, principal (set.prod s t))) = _,
begin
  rw [lift_nhds_right],
  apply congr_arg, apply funext, intro s,
  rw [lift_nhds_left],
  refl,
  exact monotone_comp (monotone_prod monotone_const monotone_id) monotone_principal,
  exact (monotone_lift' monotone_const $ monotone_lam $
    take x, monotone_prod monotone_id monotone_const)
end

lemma nhds_eq_uniformity_prod {a b : α} :
  nhds (a, b) =
  uniformity^.lift' (λs:set (α×α), set.prod {y : α | (y, a) ∈ s} {y : α | (b, y) ∈ s}) :=
begin
  rw [nhds_prod_eq, nhds_nhds_eq_uniformity_uniformity_prod, lift_lift'_same_eq_lift'],
  { intro s, exact monotone_prod monotone_const monotone_vimage },
  { intro t, exact monotone_prod monotone_vimage monotone_const }
end

lemma closure_eq_inter_uniformity {t : set (α×α)} :
  closure t = (⋂ d∈(@uniformity α _).sets, comp_rel d (comp_rel t d)) :=
set.ext $ take ⟨a, b⟩, 
calc (a, b) ∈ closure t ↔ (nhds (a, b) ⊓ principal t ≠ ⊥) : by simp [closure_eq_nhds]
  ... ↔ (((@prod.swap α α) <$> uniformity).lift'
      (λ (s : set (α × α)), set.prod {x : α | (x, a) ∈ s} {y : α | (b, y) ∈ s}) ⊓ principal t ≠ ⊥) :
    by rw [-uniformity_eq_symm, nhds_eq_uniformity_prod]
  ... ↔ ((map (@prod.swap α α) uniformity).lift'
      (λ (s : set (α × α)), set.prod {x : α | (x, a) ∈ s} {y : α | (b, y) ∈ s}) ⊓ principal t ≠ ⊥) :
    by refl
  ... ↔ (uniformity.lift'
      (λ (s : set (α × α)), set.prod {y : α | (a, y) ∈ s} {x : α | (x, b) ∈ s}) ⊓ principal t ≠ ⊥) :
  begin
    rw [map_lift'_eq2],
    simp [image_swap_eq_vimage_swap, function.comp],
    exact monotone_prod monotone_vimage monotone_vimage
  end
  ... ↔ (∀s∈(@uniformity α _).sets, ∃x, x ∈ set.prod {y : α | (a, y) ∈ s} {x : α | (x, b) ∈ s} ∩ t) :
  begin
    rw [lift'_inf_principal_eq, lift'_neq_bot_iff],
    apply forall_congr, intro s, rw [ne_empty_iff_exists_mem],
    exact monotone_inter (monotone_prod monotone_vimage monotone_vimage) monotone_const
  end
  ... ↔ (∀s∈(@uniformity α _).sets, (a, b) ∈ comp_rel s (comp_rel t s)) :
    forall_congr $ take s, forall_congr $ take hs,
    ⟨take ⟨⟨x, y⟩, ⟨⟨hx, hy⟩, hxyt⟩⟩, ⟨x, hx, y, hxyt, hy⟩,
      take ⟨x, hx, y, hxyt, hy⟩, ⟨⟨x, y⟩, ⟨⟨hx, hy⟩, hxyt⟩⟩⟩
  ... ↔ _ : by simp

lemma uniformity_eq_uniformity_closure : (@uniformity α _) = uniformity.lift' closure :=
le_antisymm
  (le_infi $ take s, le_infi $ take hs, by simp; exact uniformity.upwards_sets hs subset_closure)
  (calc uniformity.lift' closure ≤ uniformity.lift' (λd, comp_rel d (comp_rel d d)) :
      lift'_mono' (by intros s hs; rw [closure_eq_inter_uniformity]; exact bInter_subset_of_mem hs)
    ... = uniformity.lift (λs, uniformity.lift' (λt:set(α×α), comp_rel s (comp_rel t t))) :
    begin
      rw [lift_lift'_same_eq_lift'],
      exact (take x, monotone_comp_rel monotone_const $ monotone_comp_rel monotone_id monotone_id),
      exact (take x, monotone_comp_rel monotone_id monotone_const),
    end
    ... = uniformity.lift (λs, uniformity.lift (λt, uniformity.lift' (λu:set(α×α), comp_rel s (comp_rel t u)))) :
      congr_arg _ $ funext $ take x,
      begin
        rw [lift_lift'_same_eq_lift'],
        exact (take x, monotone_comp_rel monotone_const $ monotone_comp_rel monotone_const monotone_id),
        exact (take x, monotone_comp_rel monotone_const $ monotone_comp_rel monotone_id monotone_const),
      end
    ... ≤ uniformity.lift (λs, uniformity.lift (principal ∘ (λt:set(α×α), comp_rel s t))) :
      lift_mono' $ take s hs, @uniformity_lift_le_trans α _ _ (principal ∘ (λt:set(α×α), comp_rel s t)) $
        monotone_comp (monotone_comp_rel monotone_const monotone_id) monotone_principal
    ... ≤ uniformity : trans_le_uniformity')

/- uniform continuity -/

definition uniform_continuous [uniform_space β] (f : α → β) :=
filter.map (λx:α×α, (f x.1, f x.2)) uniformity ≤ uniformity

definition uniform_embedding [uniform_space β] (f : α → β) :=
(∀a₁ a₂, f a₁ = f a₂ → a₁ = a₂) ∧
filter.vmap (λx:α×α, (f x.1, f x.2)) uniformity = uniformity

lemma uniform_continuous_of_embedding [uniform_space β] {f : α → β}
  (hf : uniform_embedding f) : uniform_continuous f :=
by simp [uniform_continuous, hf.right.symm]; exact take s hs, ⟨s, hs, subset.refl _⟩

/- cauchy filters -/
definition cauchy (f : filter α) := f ≠ ⊥ ∧ filter.prod f f ≤ uniformity

lemma cauchy_downwards {f g : filter α} (h_c : cauchy f) (hg : g ≠ ⊥) (h_le : g ≤ f) : cauchy g :=
⟨hg, le_trans (filter.prod_mono h_le h_le) h_c.right⟩

lemma cauchy_nhds {a : α} : cauchy (nhds a) :=
⟨nhds_neq_bot,
  calc filter.prod (nhds a) (nhds a) =
    uniformity^.lift (λs:set (α×α), uniformity^.lift' (λt:set(α×α),
      set.prod {y : α | (y, a) ∈ s} {y : α | (a, y) ∈ t})) : nhds_nhds_eq_uniformity_uniformity_prod
    ... ≤ uniformity^.lift (λs:set (α×α), uniformity^.lift' (comp_rel s)) :
      lift_mono' $ take s hs, lift'_mono' $ take t ht, take ⟨b, c⟩ ⟨ha, hb⟩, ⟨a, ha, hb⟩
    ... ≤ uniformity : trans_le_uniformity'⟩

lemma cauchy_pure {a : α} : cauchy (pure a) :=
cauchy_downwards cauchy_nhds
  (show principal {a} ≠ ⊥, by simp)
  (return_le_nhds a)

lemma le_nhds_of_cauchy_adhp {f : filter α} {x : α} (hf : cauchy f)
  (adhs : f ⊓ nhds x ≠ ⊥) : f ≤ nhds x :=
have ∀s∈f.sets, x ∈ closure s,
begin
  intros s hs,
  simp [closure_eq_nhds, inf_comm],
  exact take h', adhs $ bot_unique $ h' ▸ inf_le_inf (by simp; exact hs) (le_refl _)
end,
calc f ≤ f.lift' (λs:set α, {y | x ∈ closure s ∧ y ∈ closure s}) :
    le_infi $ take s, le_infi $ take hs,
    begin
      rw [-forall_sets_neq_empty_iff_neq_bot] at adhs,
      simp [this s hs],
      exact f.upwards_sets hs subset_closure
    end
  ... ≤ f.lift' (λs:set α, {y | (x, y) ∈ closure (set.prod s s)}) :
    by simp [closure_prod_eq]; exact le_refl _
  ... = (filter.prod f f).lift' (λs:set (α×α), {y | (x, y) ∈ closure s}) : 
  begin
    rw [prod_same_eq],
    rw [lift'_lift'_assoc],
    exact monotone_prod monotone_id monotone_id,
    exact monotone_comp (take s t h x h', closure_mono h h') monotone_vimage
  end
  ... ≤ uniformity.lift' (λs:set (α×α), {y | (x, y) ∈ closure s}) : lift'_mono hf.right (le_refl _)
  ... = (uniformity.lift' closure).lift' (λs:set (α×α), {y | (x, y) ∈ s}) :
  begin
    rw [lift'_lift'_assoc],
    exact take s t h, closure_mono h,
    exact monotone_vimage
  end
  ... = uniformity.lift' (λs:set (α×α), {y | (x, y) ∈ s}) :
    by rw [-uniformity_eq_uniformity_closure]
  ... = nhds x :
    by rw [nhds_eq_uniformity]

lemma le_nhds_iff_adhp_of_cauchy {f : filter α} {x : α} (hf : cauchy f) :
  f ≤ nhds x ↔ f ⊓ nhds x ≠ ⊥ :=
⟨take h, (inf_of_le_left h).symm ▸ hf.left,
  le_nhds_of_cauchy_adhp hf⟩

lemma cauchy_map [uniform_space β] {f : filter α} {m : α → β}
  (hm : uniform_continuous m) (hf : cauchy f) : cauchy (map m f) :=
⟨have f ≠ ⊥, from hf.left, by simp; assumption,
  calc filter.prod (map m f) (map m f) =
          map (λp:α×α, (m p.1, m p.2)) (filter.prod f f) : filter.prod_map_map_eq
    ... ≤ map (λp:α×α, (m p.1, m p.2)) uniformity : map_mono hf.right
    ... ≤ uniformity : hm⟩

lemma cauchy_vmap [uniform_space β] {f : filter β} {m : α → β}
  (hm : vmap (λp:α×α, (m p.1, m p.2)) uniformity ≤ uniformity)
  (hf : cauchy f) (hb : vmap m f ≠ ⊥) : cauchy (vmap m f) :=
⟨hb,
  calc filter.prod (vmap m f) (vmap m f) =
          vmap (λp:α×α, (m p.1, m p.2)) (filter.prod f f) : filter.prod_vmap_vmap_eq
    ... ≤ vmap (λp:α×α, (m p.1, m p.2)) uniformity : vmap_mono hf.right
    ... ≤ uniformity : hm⟩

/- separated uniformity -/

@[class]
definition separated (α : Type u) [uniform_space α] :=
(⋂₀ (@uniformity α _).sets) = id_rel

/- totally bounded -/

@[class]
definition totally_bounded (α : Type u) [uniform_space α] :=
∀d ∈ (@uniformity α _).sets, ∃s : set α, finite s ∧ (∀x, ∃y∈s, (x,y) ∈ d)

/- complete space -/

@[class]
definition complete (α : Type u) [uniform_space α] := ∀f:filter α, cauchy f → ∃x, f ≤ nhds x

lemma complete_extension [uniform_space β] {m : β → α}
  (hm : uniform_embedding m)
  (dense : ∀x, x ∈ closure (m ' univ))
  (h : ∀f:filter β, cauchy f → ∃x:α, map m f ≤ nhds x) :
  complete α :=
take (f : filter α), assume hf : cauchy f,

let g := uniformity.lift (λs : set (α × α), f^.lift' (λt, {y : α| ∃x:α, x ∈ t ∧ (x, y) ∈ s})) in

have mg₀ : monotone (λ (s : set (α × α)) (t : set α), {y : α | ∃ (x : α), x ∈ t ∧ (x, y) ∈ s}),
  from take a b h t s ⟨x, xs, xa⟩, ⟨x, xs, h xa⟩,

have mg₁ : monotone (λ (s : set (α × α)), filter.lift' f (λ (t : set α), {y : α | ∃ (x : α), x ∈ t ∧ (x, y) ∈ s})),
  from monotone_lift' monotone_const mg₀,

have mg₂ : ∀{s:set (α×α)}, monotone (λ (t : set α), {y : α | ∃ (x : α), x ∈ t ∧ (x, y) ∈ s}),
  from take s a b h x ⟨y, ya, yxs⟩, ⟨y, h ya, yxs⟩,

have vmap m g ≠ ⊥, from
  forall_sets_neq_empty_iff_neq_bot.mp $ take s ⟨t, ht, (hs_sub : vimage m t ⊆ s)⟩,
  let ⟨t', ht', ht_mem⟩ := (mem_lift_iff mg₁).mp ht in
  let ⟨t'', ht'', ht'_sub⟩ := (mem_lift'_iff mg₂).mp ht_mem in
  let ⟨x, (hx : x ∈ t'')⟩ := inhabited_of_mem_sets hf.left ht'' in
  have h₀ : nhds x ⊓ principal (m ' univ) ≠ ⊥, 
    by simp [closure_eq_nhds] at dense; exact dense x,
  have h₁ : {y | (x, y) ∈ t'} ∈ (nhds x ⊓ principal (m ' univ)).sets, 
    from @mem_inf_sets_of_left α (nhds x) (principal (m ' univ)) _ $ mem_nhds_left ht',
  have h₂ : m ' univ ∈ (nhds x ⊓ principal (m ' univ)).sets, 
    from @mem_inf_sets_of_right α (nhds x) (principal (m ' univ)) _ $ subset.refl _,
  have {y | (x, y) ∈ t'} ∩ m ' univ ∈ (nhds x ⊓ principal (m ' univ)).sets,
    from @inter_mem_sets α (nhds x ⊓ principal (m ' univ)) _ _ h₁ h₂,
  let ⟨y, xyt', b, _, b_eq⟩ := inhabited_of_mem_sets h₀ this in
  ne_empty_iff_exists_mem.mpr ⟨b,
    hs_sub $ show m b ∈ t, from b_eq.symm ▸ ht'_sub ⟨x, hx, xyt'⟩⟩,

have cauchy_g : cauchy g, from ⟨
  (lift_neq_bot_iff mg₁).mpr $ take s hs,
    (lift'_neq_bot_iff mg₂).mpr $ take t ht, 
    let ⟨x, hx⟩ := inhabited_of_mem_sets hf.left ht in
    ne_empty_iff_exists_mem.mpr ⟨x, x, hx, refl_mem_uniformity hs⟩,
  take s hs,
  let ⟨s₁, hs₁, (trans_s₁ : comp_rel s₁ s₁ ⊆ s)⟩ := trans_mem_uniformity_sets hs in
  let ⟨s₂, hs₂, (trans_s₂ : comp_rel s₂ s₂ ⊆ s₁)⟩ := trans_mem_uniformity_sets hs₁ in
  have s₂ ∈ (filter.prod f f).sets, from hf.right hs₂,
  let ⟨t, ht, (prod_t : set.prod t t ⊆ s₂)⟩ := mem_prod_same_iff.mp this in

  have vimage prod.swap s₁ ∈ (@uniformity α _).sets,
    from symm_le_uniformity hs₁,
  have hg₁ : {y : α| ∃x:α, x ∈ t ∧ (x, y) ∈ vimage prod.swap s₁} ∈ g.sets,
    from mem_lift this $ @mem_lift' α α f _ t ht,

  have hg₂ : {y : α| ∃x:α, x ∈ t ∧ (x, y) ∈ s₂} ∈ g.sets,
    from mem_lift hs₂ $ @mem_lift' α α f _ t ht,

  have hg : set.prod {y : α| ∃x:α, x ∈ t ∧ (x, y) ∈ vimage prod.swap s₁}
                     {y : α| ∃x:α, x ∈ t ∧ (x, y) ∈ s₂} ∈ (filter.prod g g).sets,
    from @prod_mem_prod α α _ _ g g hg₁ hg₂,

  (filter.prod g g).upwards_sets hg
    (take ⟨a, b⟩ ⟨⟨c₁, c₁t, (hc₁ : (a, c₁) ∈ s₁)⟩, ⟨c₂, c₂t, (hc₂ : (c₂, b) ∈ s₂)⟩⟩,
      have (c₁, c₂) ∈ set.prod t t, from ⟨c₁t, c₂t⟩,
      trans_s₁ $ prod_mk_mem_comp_rel hc₁ $
      trans_s₂ $ prod_mk_mem_comp_rel (prod_t this) hc₂)⟩,

have cauchy (filter.vmap m g),
  from cauchy_vmap (le_of_eq hm.right) cauchy_g (by assumption),

let ⟨x, (hx : map m (filter.vmap m g) ≤ nhds x)⟩ := h _ this in

have map m (filter.vmap m g) ⊓ nhds x ≠ ⊥,
  from (le_nhds_iff_adhp_of_cauchy (cauchy_map (uniform_continuous_of_embedding hm) this)).mp hx,

have g ⊓ nhds x ≠ ⊥,
  from neq_bot_of_le_neq_bot this (inf_le_inf (take s hs, ⟨s, hs, subset.refl _⟩) (le_refl _)),

⟨x, calc f ≤ g :
    le_infi $ take s, le_infi $ take hs, le_infi $ take t, le_infi $ take ht,
    le_principal_iff.mpr $
    f.upwards_sets ht $
    take x hx, ⟨x, hx, refl_mem_uniformity hs⟩
  ... ≤ nhds x : le_nhds_of_cauchy_adhp cauchy_g this⟩

end uniform_space
end

/-- Space of Cauchy filters 

This is essentially the completion of a uniform space. The embeddings are the neighbourhood filters.
This space is not minimal, the separated uniform space (i.e. quotiented on the intersection of all
entourages) is necessary for this.
-/
def Cauchy (α : Type u) [uniform_space α] : Type u := { f : filter α // cauchy f }

namespace Cauchy

section
parameters {α : Type u} [uniform_space α]

def gen (s : set (α × α)) : set (Cauchy α × Cauchy α) :=
{p | s ∈ (filter.prod (p.1^.val) (p.2^.val))^.sets }

lemma monotone_gen : monotone gen :=
monotone_set_of $ take p, @monotone_mem_sets (α×α) (filter.prod (p.1^.val) (p.2^.val))

private lemma symm_gen : map prod.swap (uniformity^.lift' gen) ≤ uniformity^.lift' gen :=
calc map prod.swap (uniformity^.lift' gen) =
  uniformity^.lift' (λs:set (α×α), {p | s ∈ (filter.prod (p.2^.val) (p.1^.val))^.sets }) :
  begin
    delta gen,
    simp [map_lift'_eq, monotone_set_of, monotone_mem_sets,
          function.comp, image_swap_eq_vimage_swap]
  end
  ... ≤ uniformity^.lift' gen :
    uniformity_lift_le_swap
      (monotone_comp (monotone_set_of $ take p,
        @monotone_mem_sets (α×α) ((filter.prod ((p.2).val) ((p.1).val)))) monotone_principal)
      begin
        note h := λ(p:Cauchy α×Cauchy α), @filter.prod_comm _ _ (p.2.val) (p.1.val),
        simp [function.comp, h],
        exact le_refl _
      end

private lemma comp_rel_gen_gen_subset_gen_comp_rel {s t : set (α×α)} : comp_rel (gen s) (gen t) ⊆
  (gen (comp_rel s t) : set (Cauchy α × Cauchy α)) :=
take ⟨f, g⟩ ⟨h, h₁, h₂⟩,
let ⟨t₁, (ht₁ : t₁ ∈ f.val.sets), t₂, (ht₂ : t₂ ∈ h.val.sets), (h₁ : set.prod t₁ t₂ ⊆ s)⟩ :=
  mem_prod_iff^.mp h₁ in
let ⟨t₃, (ht₃ : t₃ ∈ h.val.sets), t₄, (ht₄ : t₄ ∈ g.val.sets), (h₂ : set.prod t₃ t₄ ⊆ t)⟩ :=
  mem_prod_iff^.mp h₂ in
have t₂ ∩ t₃ ∈ h.val.sets,
  from inter_mem_sets ht₂ ht₃,
let ⟨x, xt₂, xt₃⟩ :=
  inhabited_of_mem_sets (h.property.left) this in
(filter.prod f^.val g^.val).upwards_sets
  (prod_mem_prod ht₁ ht₄)
  (take ⟨a, b⟩ ⟨(ha : a ∈ t₁), (hb : b ∈ t₄)⟩,
    ⟨x,
      h₁ (show (a, x) ∈ set.prod t₁ t₂, from ⟨ha, xt₂⟩),
      h₂ (show (x, b) ∈ set.prod t₃ t₄, from ⟨xt₃, hb⟩)⟩)

private lemma trans_gen :
    (uniformity^.lift' gen)^.lift (λs, (uniformity^.lift' gen)^.lift' (comp_rel s)) ≤
    uniformity^.lift' gen :=
calc (uniformity^.lift' gen)^.lift (λs, (uniformity^.lift' gen)^.lift' (comp_rel s)) =
    uniformity^.lift (λs, uniformity^.lift' (λt, comp_rel (gen s) (gen t))) :
  begin
    rw [lift_lift'_assoc],
    apply congr_arg, apply funext, intro x,
    rw [lift'_lift'_assoc],
    exact monotone_gen,
    exact (monotone_comp_rel monotone_const monotone_id),
    exact monotone_gen,
    exact monotone_lift' monotone_const
      (monotone_lam $ take t, monotone_comp_rel monotone_id monotone_const),
  end
  ... ≤ uniformity^.lift (λs, uniformity^.lift' $ λt, gen $ comp_rel s t) :
    lift_mono' $ take s hs, lift'_mono' $ take t ht, comp_rel_gen_gen_subset_gen_comp_rel
  ... = (uniformity^.lift $ λs:set(α×α), uniformity^.lift' $ comp_rel s)^.lift' gen :
  begin
    rw [lift'_lift_assoc],
    apply congr_arg, apply funext, intro x,
    rw [lift'_lift'_assoc],
    exact (monotone_comp_rel monotone_const monotone_id),
    exact monotone_gen,
    exact monotone_lift' monotone_const
      (monotone_lam $ take t, monotone_comp_rel monotone_id monotone_const)
  end
  ... ≤ uniformity^.lift' gen : lift'_mono trans_le_uniformity' (le_refl _)

instance completion_space : uniform_space (Cauchy α) :=
{ uniformity := uniformity^.lift' gen,
  refl       := principal_le_lift' $ take s hs ⟨a, b⟩ (a_eq_b : a = b),
    a_eq_b ▸ a^.property^.right hs,
  symm       := symm_gen,
  trans      := trans_gen }

def pure_cauchy (a : α) : Cauchy α :=
⟨pure a, cauchy_pure⟩

lemma uniform_embedding_pure_cauchy : uniform_embedding (pure_cauchy : α → Cauchy α) :=
⟨take a₁ a₂ h,
  have (pure_cauchy a₁).val = (pure_cauchy a₂).val, from congr_arg _ h,
  have {a₁} = ({a₂} : set α),
    from principal_eq_iff_eq.mp this,
  by simp at this; assumption,
  have (vimage (λ (x : α × α), (pure_cauchy (x.fst), pure_cauchy (x.snd))) ∘ gen) = id,
    from funext $ take s, set.ext $ take ⟨a₁, a₂⟩,
      by simp [vimage, gen, pure_cauchy, pure, prod_principal_principal],
  calc vmap (λ (x : α × α), (pure_cauchy (x.fst), pure_cauchy (x.snd))) (uniformity^.lift' gen) =
          uniformity^.lift' (vimage (λ (x : α × α), (pure_cauchy (x.fst), pure_cauchy (x.snd))) ∘ gen) :
      vmap_lift'_eq monotone_gen
    ... = uniformity : by simp [this]⟩

lemma pure_cauchy_dense : ∀x, x ∈ closure (pure_cauchy ' univ) :=
take f,
have h_ex : ∀s∈(@uniformity (Cauchy α) _).sets, ∃y:α, (f, pure_cauchy y) ∈ s, from
  take s hs,
  let ⟨t'', ht''₁, (ht''₂ : gen t'' ⊆ s)⟩ := (mem_lift'_iff monotone_gen).mp hs in
  let ⟨t', ht'₁, ht'₂⟩ := trans_mem_uniformity_sets ht''₁ in
  have t' ∈ (filter.prod (f.val) (f.val)).sets,
    from f.property.right ht'₁,
  let ⟨t, ht, (h : set.prod t t ⊆ t')⟩ := mem_prod_same_iff.mp this in
  let ⟨x, (hx : x ∈ t)⟩ := inhabited_of_mem_sets f.property.left ht in
  have t'' ∈ (filter.prod f.val (pure x)).sets,
    from mem_prod_iff.mpr ⟨t, ht, {y:α | (x, y) ∈ t'},
      take y, begin simp, intro h, simp [h], exact refl_mem_uniformity ht'₁ end,
      take ⟨a, b⟩ ⟨(h₁ : a ∈ t), (h₂ : (x, b) ∈ t')⟩,
        ht'₂ $ prod_mk_mem_comp_rel (@h (a, x) ⟨h₁, hx⟩) h₂⟩,
  ⟨x, ht''₂ $ by dsimp [gen]; exact this⟩,
begin
  simp [closure_eq_nhds, nhds_eq_uniformity, lift'_inf_principal_eq],
  exact (lift'_neq_bot_iff $ monotone_inter monotone_const monotone_vimage).mpr
    (take s hs,
      let ⟨y, hy⟩ := h_ex s hs in
      have pure_cauchy y ∈ pure_cauchy ' univ ∩ {y : Cauchy α | (f, y) ∈ s},
        from ⟨mem_image_of_mem _ $ mem_univ y, hy⟩,
      ne_empty_of_mem this)
end

instance : complete (Cauchy α) :=
complete_extension
  uniform_embedding_pure_cauchy
  pure_cauchy_dense
  (take f hf, ⟨⟨f, hf⟩,
    begin
      simp [nhds_eq_uniformity],
      exact (le_lift' $ take s hs,
        let ⟨t'', ht''₁, (ht''₂ : gen t'' ⊆ s)⟩ := (mem_lift'_iff monotone_gen).mp hs in
        have {y:α | ((⟨f, hf⟩, pure_cauchy y) : Cauchy α × Cauchy α) ∈ gen t''} ∈ f.sets,
          begin simp [gen, pure_cauchy] end,
        show {y:α | ((⟨f, hf⟩ : Cauchy α), pure_cauchy y) ∈ s} ∈ f.sets, from
          f.upwards_sets this $ vimage_mono ht''₂)
    end⟩)

end Cauchy
