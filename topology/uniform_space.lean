/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Theory of uniform spaces.
-/
import algebra.lattice.filter .topological_space
open set lattice filter

universes u v w x

lemma set.prod_image_image_eq {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  {s₁ : set α₁} {s₂ : set α₂} {m₁ : α₁ → β₁} {m₂ : α₂ → β₂} :
  set.prod (image m₁ s₁) (image m₂ s₂) = image (λp:α₁×α₂, (m₁ p.1, m₂ p.2)) (set.prod s₁ s₂) :=
set.ext $ take ⟨b₁, b₂⟩,
  ⟨take ⟨⟨a₁, ha₁, (eq₁ : m₁ a₁ = b₁)⟩, ⟨a₂, ha₂, (eq₂ : m₂ a₂ = b₂)⟩⟩,
    mem_image
      (show (a₁, a₂) ∈ set.prod s₁ s₂, from ⟨ha₁, ha₂⟩)
      (by simp [eq₁, eq₂]),
    take ⟨⟨a₁, a₂⟩, ⟨ha₁, ha₂⟩, eq⟩, eq ▸ ⟨mem_image_of_mem m₁ ha₁, mem_image_of_mem m₂ ha₂⟩⟩

namespace filter
variables {α : Type u} {β : Type v}

def vmap (m : α → β) (f : filter β) : filter α :=
{ filter .
  sets          := { s | ∃t∈f.sets, vimage m t ⊆ s },
  inhabited     := ⟨univ, univ, univ_mem_sets, by simp⟩,
  upwards_sets  := take a b ⟨a', ha', ma'a⟩ ab, ⟨a', ha', subset.trans ma'a ab⟩,
  directed_sets := take a ⟨a', ha₁, ha₂⟩ b ⟨b', hb₁, hb₂⟩,
    ⟨vimage m (a' ∩ b'),
      ⟨a' ∩ b', inter_mem_sets ha₁ hb₁, subset.refl _⟩,
      subset.trans (vimage_mono $ inter_subset_left _ _) ha₂,
      subset.trans (vimage_mono $ inter_subset_right _ _) hb₂⟩ }

lemma prod_map_map_eq {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  {f₁ : filter α₁} {f₂ : filter α₂} {m₁ : α₁ → β₁} {m₂ : α₂ → β₂} :
  filter.prod (map m₁ f₁) (map m₂ f₂) = map (λp:α₁×α₂, (m₁ p.1, m₂ p.2)) (filter.prod f₁ f₂) :=
begin
  simp [filter.prod],
  rw [map_lift_eq], tactic.swap, exact (monotone_lift' monotone_const $
    monotone_lam $ take t, monotone_prod monotone_id monotone_const),
  rw [map_lift_eq2], tactic.swap, exact (monotone_lift' monotone_const $
    monotone_lam $ take t, monotone_prod monotone_id monotone_const),
  apply congr_arg, apply funext, intro t,
  dsimp,
  rw [map_lift'_eq], tactic.swap, exact monotone_prod monotone_const monotone_id,
  rw [map_lift'_eq2], tactic.swap, exact monotone_prod monotone_const monotone_id,
  apply congr_arg, apply funext, intro t,
  exact set.prod_image_image_eq
end

end filter


section
variables {α : Type u} {β : Type v}

def refl_rel {α : Type u} := {p : α × α | p.1 = p.2}

def trans_rel {α : Type u} (r₁ r₂ : set (α×α)) :=
{p : α × α | ∃z:α, (p.1, z) ∈ r₁ ∧ (z, p.2) ∈ r₂}

lemma monotone_trans_rel [weak_order β] {f g : β → set (α×α)}
  (hf : monotone f) (hg : monotone g) : monotone (λx, trans_rel (f x) (g x)) :=
take a b h p ⟨z, h₁, h₂⟩, ⟨z, hf h h₁, hg h h₂⟩

lemma monotone_inter [weak_order β] {f g : β → set α}
  (hf : monotone f) (hg : monotone g) : monotone (λx, (f x) ∩ (g x)) :=
take a b h x ⟨h₁, h₂⟩, ⟨hf h h₁, hg h h₂⟩

lemma empty_in_sets_eq_bot {f : filter α} : ∅ ∈ f^.sets ↔ f = ⊥ :=
⟨take h, bot_unique $ take s _, f.upwards_sets h (empty_subset s),
  suppose f = ⊥, this.symm ▸ mem_bot_sets⟩

lemma inhabited_of_mem_sets {f : filter α} {s : set α} (hf : f ≠ ⊥) (hs : s ∈ f^.sets) :
  ∃x, x ∈ s :=
have ∅ ∉ f^.sets, from take h, hf $ empty_in_sets_eq_bot.mp h,
have s ≠ ∅, from take h, this (h ▸ hs),
exists_mem_of_ne_empty this

@[simp]
lemma vimage_set_of_eq {p : α → Prop} {f : β → α} :
  vimage f {a | p a} = {a | p (f a)} :=
rfl

@[simp] -- copied from parser
lemma prod.mk.eta : ∀{p : α × β}, (p.1, p.2) = p
| (a, b) := rfl

@[simp]
lemma prod_mk_mem_set_prod_eq {a : α} {b : β} {s : set α} {t : set β} :
  (a, b) ∈ set.prod s t = (a ∈ s ∧ b ∈ t) :=
rfl

lemma prod_mk_mem_trans_rel {a b c : α} {s t : set (α×α)} (h₁ : (a, c) ∈ s) (h₂ : (c, b) ∈ t) :
  (a, b) ∈ trans_rel s t :=
⟨c, h₁, h₂⟩

def prod.swap : (α×β) → (β×α) := λp, (p.2, p.1)

@[simp]
lemma prod.swap_swap : ∀x:α×β, prod.swap (prod.swap x) = x
| ⟨a, b⟩ := rfl

@[simp]
lemma prod.fst_swap {p : α×β} : (prod.swap p).1 = p.2 := rfl

@[simp]
lemma prod.snd_swap {p : α×β} : (prod.swap p).2 = p.1 := rfl

@[simp]
lemma prod.swap_prod_mk {a : α} {b : β} : prod.swap (a, b) = (b, a) := rfl

@[simp]
lemma set_of_mem_eq {s : set α} : {x | x ∈ s} = s :=
rfl

lemma mem_image_iff_of_inverse (f : α → β) (g : β → α) {b : β} {s : set α}
  (h₁ : ∀a, g (f a) = a ) (h₂ : ∀b, f (g b) = b ) : b ∈ f ' s ↔ g b ∈ s :=
⟨take ⟨a, ha, fa_eq⟩, fa_eq ▸ (h₁ a)^.symm ▸ ha,
  take h, ⟨g b, h, h₂ b⟩⟩

lemma image_eq_vimage_of_inverse (f : α → β) (g : β → α)
  (h₁ : ∀a, g (f a) = a ) (h₂ : ∀b, f (g b) = b ) : image f = vimage g :=
funext $ take s, set.ext $ take b, mem_image_iff_of_inverse f g h₁ h₂

lemma image_swap_eq_vimage_swap : image (@prod.swap α β) = vimage prod.swap :=
image_eq_vimage_of_inverse (@prod.swap α β) (@prod.swap β α)
  begin simp; intros; trivial end
  begin simp; intros; trivial end

lemma monotone_set_of [weak_order α] {p : α → β → Prop}
  (hp : ∀b, monotone (λa, p a b)) : monotone (λa, {b | p a b}) :=
take a a' h b, hp b h

@[simp] -- should be handled by implies_true_iff
lemma implies_implies_true_iff {α : Sort u} {β : Sort v} : (α → β → true) ↔ true :=
⟨take _, trivial, take _ _ _ , trivial⟩

/- uniformity -/

class uniform_space (α : Type u) :=
(uniformity : filter (α × α))
(refl       : principal refl_rel ≤ uniformity)
(symm       : prod.swap <$> uniformity ≤ uniformity)
(trans      : uniformity^.lift (λs, uniformity^.lift' (trans_rel s)) ≤ uniformity)

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
  uniformity^.lift (λs:set (α×α), uniformity^.lift' (trans_rel s)) ≤ uniformity :=
uniform_space.trans α

lemma trans_le_uniformity :
  uniformity^.lift' (λt:set (α×α), trans_rel t t) ≤ uniformity :=
calc uniformity^.lift' (λt:set (α×α), trans_rel t t) ≤
        uniformity^.lift (λs:set (α×α), uniformity^.lift' (trans_rel s)) :
    (le_infi $ take s, le_infi $ take hs, le_infi $ take t, le_infi $ take ht,
      infi_le_of_le (s ∩ t) $
      infi_le_of_le (inter_mem_sets hs ht) $
      principal_mono.mpr $ take x ⟨z, ⟨h₁, _⟩, ⟨_, h₂⟩⟩, ⟨z, h₁, h₂⟩)
  ... ≤ uniformity : trans_le_uniformity'

lemma trans_mem_uniformity_sets {s : set (α × α)} (hs : s ∈ (@uniformity α _).sets) :
  ∃t∈(@uniformity α _).sets, trans_rel t t ⊆ s :=
have s ∈ (uniformity^.lift' (λt:set (α×α), trans_rel t t)).sets,
  from trans_le_uniformity hs,
(mem_lift'_iff $ monotone_trans_rel monotone_id monotone_id).mp this

lemma uniformity_le_symm : uniformity ≤ map (@prod.swap α α) uniformity :=
calc uniformity = id <$> uniformity : (monad.id_map _)^.symm
  ... = (prod.swap.{u u} ∘ prod.swap) <$> uniformity :
    congr_arg (λf : (α×α)→(α×α), f <$> uniformity) (by apply funext; intro x; cases x; refl)
  ... = (map prod.swap ∘ map prod.swap) uniformity :
    congr map_compose rfl
  ... ≤ prod.swap.{u u} <$> uniformity : map_mono symm_le_uniformity

lemma uniformity_eq_symm : uniformity = (@prod.swap α α) <$> uniformity :=
le_antisymm uniformity_le_symm symm_le_uniformity

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
          have (x', b') ∈ trans_rel t t, from ⟨b, hp, this⟩,
          show b' ∈ s,
            from tr this rfl,
    hs⟩⟩

lemma nhds_eq {x : α} : nhds x = uniformity^.lift' (λs:set (α×α), {y | (x, y) ∈ s}) :=
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
  by rw [nhds_eq]; exact infi_le_of_le s (infi_le _ h),
by simp at this; assumption

lemma mem_nhds_right {y : α} {s : set (α×α)} (h : s ∈ (uniformity.sets : set (set (α×α)))) :
  {x : α | (x, y) ∈ s} ∈ (nhds y)^.sets :=
mem_nhds_left (symm_le_uniformity h)

lemma lift_nhds_eq {x : α} {g : set α → filter β} (hg : monotone g) :
  (nhds x)^.lift g = uniformity^.lift (λs:set (α×α), g {y | (x, y) ∈ s}) :=
eq.trans
  begin
    rw [nhds_eq],
    exact (filter.lift_assoc $ monotone_comp monotone_vimage $ monotone_comp monotone_vimage monotone_principal)
  end
  (congr_arg _ $ funext $ take s, filter.lift_principal hg)

lemma uniformity_lift_le_swap {g : set (α×α) → filter β} {f : filter β} (hg : monotone g)
  (h : uniformity^.lift (λs, g (vimage prod.swap s)) ≤ f) : uniformity^.lift g ≤ f :=
le_trans
  (lift_mono uniformity_le_symm (le_refl _))
  (by rw [map_lift_eq2 hg, image_swap_eq_vimage_swap]; exact h)

lemma uniformity_lift_le_trans {f : set (α×α) → filter β} (h : monotone f):
  uniformity.lift (λs, uniformity.lift (λt, f (trans_rel s t))) ≤ uniformity.lift f :=
calc uniformity.lift (λs, uniformity.lift (λt, f (trans_rel s t))) =
    (uniformity.lift (λs:set (α×α), uniformity.lift' (λt:set (α×α), trans_rel s t)))^.lift f :
  begin
    rw [lift_assoc],
    apply congr_arg, apply funext, intro s,
    rw [lift_lift'_assoc],
    exact monotone_trans_rel monotone_const monotone_id,
    exact h,
    exact (monotone_lift' monotone_const $ monotone_lam $
      take t, monotone_trans_rel monotone_id monotone_const)
  end
  ... ≤ uniformity.lift f : lift_mono trans_le_uniformity' (le_refl _)

/- uniform continuity -/

definition uniform [uniform_space β] (f : α → β) :=
filter.map (λx:α×α, (f x.1, f x.2)) uniformity ≤ uniformity

/- cauchy filters -/
definition cauchy (f : filter α) := filter.prod f f ≤ uniformity

lemma cauchy_downwards {f g : filter α} (h_c : cauchy f) (h_le : g ≤ f) : cauchy g :=
le_trans (filter.prod_mono h_le h_le) h_c

lemma nhds_nhds_le_uniformity_prod {a b : α} : filter.prod (nhds a) (nhds b) ≤
  uniformity^.lift (λs:set (α×α), uniformity^.lift' (λt:set(α×α),
    set.prod {y : α | (y, a) ∈ s} {y : α | (b, y) ∈ t})) :=
begin
  rw [nhds_eq],
  rw [nhds_eq],
  rw [prod_lift'_lift'],
  apply uniformity_lift_le_swap _,
  apply lift_mono (le_refl uniformity), intro s,
  apply lift'_mono (le_refl uniformity), intro t,
  exact le_refl _,
  exact (monotone_lift' monotone_const $ monotone_lam $
    take t, monotone_prod monotone_vimage monotone_const),
  exact monotone_vimage,
  exact monotone_vimage
end

lemma cauchy_nhds {a : α} : cauchy (nhds a) :=
calc filter.prod (nhds a) (nhds a) ≤
  uniformity^.lift (λs:set (α×α), uniformity^.lift' (λt:set(α×α),
    set.prod {y : α | (y, a) ∈ s} {y : α | (a, y) ∈ t})) : nhds_nhds_le_uniformity_prod
  ... ≤ uniformity^.lift (λs:set (α×α), uniformity^.lift' (trans_rel s)) :
    lift_mono' $ take s hs, lift'_mono' $ take t ht, take ⟨b, c⟩ ⟨ha, hb⟩, ⟨a, ha, hb⟩
  ... ≤ uniformity : trans_le_uniformity'

lemma cauchy_map [uniform_space β] {f : filter α} {m : α → β}
  (hm : uniform m) (hf : cauchy f) : cauchy (map m f) :=
calc filter.prod (map m f) (map m f) = map (λp:α×α, (m p.1, m p.2)) (filter.prod f f) : filter.prod_map_map_eq
  ... ≤ map (λp:α×α, (m p.1, m p.2)) uniformity : map_mono hf
  ... ≤ uniformity : hm

/- complete space -/

@[class]
definition complete (α : Type u) [uniform_space α] := ∀f:filter α, cauchy f → ∃x, f ≤ nhds x

lemma complete_extension [uniform_space β] {m : β → α}
  (hm : uniform m) (dense : ∀x, x ∈ closure (m ' univ))
  (h : ∀f:filter β, cauchy f → ∃x:α, map m f ≤ nhds x) :
  complete α :=
take (f : filter α), assume hf : cauchy f,
let g := uniformity.lift (λs : set (α × α), f^.lift' (λt, {y : α| ∃x:α, x ∈ t ∧ (x, y) ∈ s})) in
have cauchy g, from
  take s hs,
  let ⟨s₁, hs₁, (trans_s₁ : trans_rel s₁ s₁ ⊆ s)⟩ := trans_mem_uniformity_sets hs in
  let ⟨s₂, hs₂, (trans_s₂ : trans_rel s₂ s₂ ⊆ s₁)⟩ := trans_mem_uniformity_sets hs₁ in
  have s₂ ∈ (filter.prod f f).sets, from hf hs₂,
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
      trans_s₁ $ prod_mk_mem_trans_rel hc₁ $
      trans_s₂ $ prod_mk_mem_trans_rel (prod_t this) hc₂),

have cauchy (filter.vmap m g),
  from _, 
let ⟨x, (hx : map m (filter.vmap m g) ≤ nhds x)⟩ := h _ this in

⟨x,
calc f ≤ g :
    le_infi $ take s, le_infi $ take hs, le_infi $ take t, le_infi $ take ht,
    le_principal_iff.mpr $
    f.upwards_sets ht $
    take x hx, ⟨x, hx, refl_mem_uniformity hs⟩
  ... ≤ map m (filter.vmap m g) :
    take s ⟨t, ht, h_sub⟩, _ -- use density
  ... ≤ nhds x : hx⟩

end uniform_space
end

/-- Space of Cauchy filters 

This is essentially the completion of a uniform space. The embeddings are the neighbourhood filters.
This space is not minimal, the separated uniform space (i.e. quotiented on the intersection of all
entourages) is necessary for this.
-/
def Cauchy (α : Type u) [uniform_space α] : Type u :=
{ f : filter α // cauchy f ∧ f ≠ bot }

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

private lemma trans_rel_gen_gen_subset_gen_trans_rel {s t : set (α×α)} : trans_rel (gen s) (gen t) ⊆
  (gen (trans_rel s t) : set (Cauchy α × Cauchy α)) :=
take ⟨f, g⟩ ⟨h, h₁, h₂⟩,
let ⟨t₁, (ht₁ : t₁ ∈ f.val.sets), t₂, (ht₂ : t₂ ∈ h.val.sets), (h₁ : set.prod t₁ t₂ ⊆ s)⟩ :=
  mem_prod_iff^.mp h₁ in
let ⟨t₃, (ht₃ : t₃ ∈ h.val.sets), t₄, (ht₄ : t₄ ∈ g.val.sets), (h₂ : set.prod t₃ t₄ ⊆ t)⟩ :=
  mem_prod_iff^.mp h₂ in
have t₂ ∩ t₃ ∈ h.val.sets,
  from inter_mem_sets ht₂ ht₃,
let ⟨x, xt₂, xt₃⟩ :=
  inhabited_of_mem_sets (h.property.right) this in
(filter.prod f^.val g^.val).upwards_sets
  (prod_mem_prod ht₁ ht₄)
  (take ⟨a, b⟩ ⟨(ha : a ∈ t₁), (hb : b ∈ t₄)⟩,
    ⟨x,
      h₁ (show (a, x) ∈ set.prod t₁ t₂, from ⟨ha, xt₂⟩),
      h₂ (show (x, b) ∈ set.prod t₃ t₄, from ⟨xt₃, hb⟩)⟩)

private lemma trans_gen :
    (uniformity^.lift' gen)^.lift (λs, (uniformity^.lift' gen)^.lift' (trans_rel s)) ≤
    uniformity^.lift' gen :=
calc (uniformity^.lift' gen)^.lift (λs, (uniformity^.lift' gen)^.lift' (trans_rel s)) =
    uniformity^.lift (λs, uniformity^.lift' (λt, trans_rel (gen s) (gen t))) :
  begin
    rw [lift_lift'_assoc],
    apply congr_arg, apply funext, intro x,
    rw [lift'_lift'_assoc],
    exact monotone_gen,
    exact (monotone_trans_rel monotone_const monotone_id),
    exact monotone_gen,
    exact monotone_lift' monotone_const
      (monotone_lam $ take t, monotone_trans_rel monotone_id monotone_const),
  end
  ... ≤ uniformity^.lift (λs, uniformity^.lift' $ λt, gen $ trans_rel s t) :
    lift_mono' $ take s hs, lift'_mono' $ take t ht, trans_rel_gen_gen_subset_gen_trans_rel
  ... = (uniformity^.lift $ λs:set(α×α), uniformity^.lift' $ trans_rel s)^.lift' gen :
  begin
    rw [lift'_lift_assoc],
    apply congr_arg, apply funext, intro x,
    rw [lift'_lift'_assoc],
    exact (monotone_trans_rel monotone_const monotone_id),
    exact monotone_gen,
    exact monotone_lift' monotone_const
      (monotone_lam $ take t, monotone_trans_rel monotone_id monotone_const)
  end
  ... ≤ uniformity^.lift' gen : lift'_mono trans_le_uniformity' (le_refl _)

def completion_space : uniform_space (Cauchy α) :=
{ uniformity := uniformity^.lift' gen,
  refl       := principal_le_lift' $ take s hs ⟨a, b⟩ (a_eq_b : a = b),
    a_eq_b ▸ a^.property^.left hs,
  symm       := symm_gen,
  trans      := trans_gen }

local attribute [instance] completion_space

def nhds_cauchy (a : α) : Cauchy α :=
⟨nhds a, cauchy_nhds, nhds_neq_bot⟩

lemma uniform_nhds_cauchy : uniform (nhds_cauchy : α → Cauchy α) :=
calc map (λx:α×α, (nhds_cauchy x.1, nhds_cauchy x.2)) uniformity ≤
  (uniformity^.lift $ λs₁, uniformity^.lift $ λs₂, uniformity^.lift' $ λs₃,
    gen (trans_rel s₁ (trans_rel s₂ s₃))) :
    le_infi $ take s₁, le_infi $ take hs₁, le_infi $ take s₂, le_infi $ take hs₂, le_infi $ take s₃, le_infi $ take hs₃,
    begin
      simp [gen, nhds_cauchy],
      apply uniformity.upwards_sets hs₂,
      intros p hp, cases p with a b,
      apply (filter.prod (nhds a) (nhds b)).upwards_sets,
      show set.prod {x:α | (x, a) ∈ s₁} {y:α | (b, y) ∈ s₃} ∈ (filter.prod (nhds a) (nhds b)).sets,
        from @prod_mem_prod α α {x:α | (x, a) ∈ s₁} {y:α | (b, y) ∈ s₃} (nhds a) (nhds b)
          (mem_nhds_right hs₁)
          (mem_nhds_left hs₃),
      show set.prod {x:α | (x, a) ∈ s₁} {y:α | (b, y) ∈ s₃} ⊆ trans_rel s₁ (trans_rel s₂ s₃),
        from take ⟨x, y⟩ ⟨hx, hy⟩, ⟨a, hx, b, hp, hy⟩
    end
  ... ≤ (uniformity^.lift $ λs:set(α×α), uniformity^.lift' $ λt, gen (trans_rel s t)) :
    lift_mono (le_refl _) $ take s,
      @uniformity_lift_le_trans α (Cauchy α × Cauchy α) _ (principal ∘ (λ (t : set (α × α)), gen (trans_rel s t)))
        (monotone_comp (monotone_comp (monotone_trans_rel monotone_const monotone_id) monotone_gen) monotone_principal)
  ... ≤ uniformity :
    @uniformity_lift_le_trans  α (Cauchy α × Cauchy α) _ (principal ∘ gen)
      (monotone_comp monotone_gen monotone_principal)

lemma nhds_cauchy_dense : ∀x, x ∈ closure (nhds_cauchy ' univ) :=
take f,
have h_ex : ∀s∈(@uniformity (Cauchy α) _).sets, ∃y:α, (f, nhds_cauchy y) ∈ s, from
  take s hs,
  let ⟨t'', ht''₁, (ht''₂ : gen t'' ⊆ s)⟩ := (mem_lift'_iff monotone_gen).mp hs in
  let ⟨t', ht'₁, ht'₂⟩ := trans_mem_uniformity_sets ht''₁ in
  have t' ∈ (filter.prod (f.val) (f.val)).sets,
    from f.property.left ht'₁,
  let ⟨t, ht, (h : set.prod t t ⊆ t')⟩ := mem_prod_same_iff.mp this in
  let ⟨x, (hx : x ∈ t)⟩ := inhabited_of_mem_sets f.property.right ht in
  have t'' ∈ (filter.prod f.val (nhds x)).sets,
    from mem_prod_iff.mpr ⟨t, ht, {y:α | (x, y) ∈ t'}, mem_nhds_left ht'₁,
      take ⟨a, b⟩ ⟨(h₁ : a ∈ t), (h₂ : (x, b) ∈ t')⟩,
        ht'₂ $ prod_mk_mem_trans_rel (@h (a, x) ⟨h₁, hx⟩) h₂⟩,
  ⟨x, ht''₂ $ by dsimp [gen]; exact this⟩,
begin
  simp [closure_eq_nhds, nhds_eq, lift'_inf_principal_eq],
  exact lift'_neq_bot ⟨f⟩
    (monotone_inter monotone_const monotone_vimage)
    (take s hs,
      let ⟨y, hy⟩ := h_ex s hs in
      have nhds_cauchy y ∈ nhds_cauchy ' univ ∩ {y : Cauchy α | (f, y) ∈ s},
        from ⟨mem_image_of_mem _ $ mem_univ y, hy⟩,
      ne_empty_of_mem this)
end

end

end Cauchy
