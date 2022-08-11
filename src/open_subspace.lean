import algebraic_topology.fundamental_groupoid.basic
import topology.category.Top.basic
import topology.path_connected

noncomputable theory

structure top_subspace (X : Type*) [topological_space X] :=
(carrier : set X)
(univ_open : is_open carrier)

variables {X : Type*} [topological_space X]

instance : has_mem X (top_subspace X) := 
begin
  split, intro s, intro S, exact s ∈ S.carrier,
end

instance : has_coe (top_subspace X) (set X) :=
begin
  split, intro S, exact S.carrier,
end

-- instance to_topspace (H : top_subspace X) : topological_space H :=
-- begin
--   exact subtype.topological_space,
-- end

variable {H : top_subspace X} 

@[simp] lemma mem_carrier {x : X} : x ∈ H.carrier ↔ x ∈ H :=
begin
  refl
end

@[simp] lemma mem_coe {x : X} : x ∈ (↑H : set X) ↔ x ∈ H :=
begin
  refl
end

@[simp] lemma mem_coe_self : (H : set X) = H.carrier := 
begin
  refl,
end

@[reducible] def incl : H → X :=
begin
  intro h, cases h, exact h_val,
end

instance has_coe_to_topspace : has_coe (H : top_subspace X) X :=
begin
  split, exact incl,
end

instance derived_topspace : topological_space H :=
begin
  exact @topological_space.induced _ _ incl _inst_1,
end

instance has_coe_to_parent_set : has_coe (set H) (set X) :=
begin
  fconstructor, intro h, exact set.image incl h,
end 


theorem subspace_topology_equiv {X : Type*} [top_X : topological_space X] {H : top_subspace X} (x : set H):
 is_open x ↔ (∃(y : set X), is_open y ∧ y ∩ H = ↑x) :=
begin
  split, 
  {
    intro h, cases h, use h_w, cases h_h, fconstructor, assumption, 
    norm_num, rw incl at *, induction h_h_right, ring_nf, ext1,
    split, intro h2, fconstructor, fconstructor, exact x_1, finish,
    finish, intro h3, cases h3, fconstructor, finish, cases h3_h, cases h3_w, finish,
  },
  {
    intro h, cases h, cases h_h, fconstructor, exact h_w, fconstructor, assumption,
    rw set.preimage, ext1, rw incl, simp only [set.mem_set_of_eq], split,
    {
      intro hhh,
    cases x_1, simp at *, unfold_coes at *, rw incl at *, simp at *, dsimp at *,
    have s: x_1_val ∈ h_w ∩ H.carrier, fconstructor, exact hhh, exact x_1_property,
    rw h_h_right at s, finish,
    }, 
    intro h, have p: ↑x ⊆ h_w, rw ←h_h_right, intro s, intro hs, cases hs, assumption,
    apply p, fconstructor,exact x_1, split,exact h, rw incl,
    
  },
end

@[continuity] lemma incl_continuous : @continuous H X _ _ incl :=
begin
  exact continuous_induced_dom,
end

@[reducible] def i : C(↥H, X) := ⟨incl, incl_continuous⟩ 

def to_set (H : top_subspace X): set H := λh : H, true


@[simp] lemma to_set_id : set.image incl (to_set H) = H :=
begin
  unfold_coes, rw set.image, ext1, split, intro x,cases x,
  rw to_set at *, cases x_h with xh1 xh2, rw incl at xh2,simp at xh2, induction xh2, cases x_w,tauto,
  intro a, split, split,rotate 2,fconstructor,exact x,tauto, solve_by_elim, tauto,
end


-- lemma incl_intersection (x : set H) (y : set H): incl '' x ∩ incl '' y = incl '' (x ∩ y) :=
-- begin
--   sorry{rw incl, ext1, simp, split, 
--   {intro s,cases s with sx sy, cases sx, cases sx_h with sxh1 sxh2, cases sy,
--   cases sy_h with syh1 syh2, cases sx_w, cases sy_w, use x_1, simp at *, finish, fconstructor, finish,
--   finish,},
--   {
--     intro s, cases s, cases s_w, cases s_h with sh1 sh2,cases sh1, simp at *, split, use x_1, rw ←sh2, assumption,
--     split, finish, finish, use x_1, finish, split, finish,finish,
--   },}

-- end

variables {a b : (H : top_subspace X)}

-- lift a path from subspace H to X --

-- theorem subspace_path_incl (p : path a b) : path (a:X) (b:X) :=
-- begin
--   fconstructor,
--   {
--     exact { to_fun := i ∘ p.to_continuous_map,
--             continuous_to_fun := continuous_induced_dom.comp (map_continuous p.to_continuous_map)}
--   }, 
--   {
--     simp only [path.coe_to_continuous_map, function.comp_app, path.source], unfold i, unfold incl, refl,
--   },
--   {
--     simp only [path.target, path.coe_to_continuous_map, function.comp_app], unfold i, unfold incl, refl,
--   }
-- end

-- notation `πₓ` := fundamental_groupoid.fundamental_groupoid_functor.obj
-- notation `π` := fundamental_groupoid.fundamental_groupoid_functor
-- notation `πₘ` := fundamental_groupoid.fundamental_groupoid_functor.map

-- def induced_top_morphism : Top.of H ⟶ Top.of X := i
-- def induced_groupoid_morphism : πₓ (Top.of H) ⟶ πₓ (Top.of X) := πₘ i

def to_subspace (X : Type*) [top : topological_space X]: top_subspace X := 
{ carrier := @set.univ X, 
  univ_open := top.is_open_univ}

instance has_coe_to_subspace {Y : Type*} [topological_space Y] : has_coe Y (top_subspace Y) :=
begin
  fconstructor, intro h, apply to_subspace,
end

-- Partial order --

theorem ext' {H K : top_subspace X} (h : H.carrier = K.carrier) : H = K :=
begin
  cases H, 
  cases K,
  simp * at *, 
end

theorem ext'_iff {H K : top_subspace X} :
  H.carrier = K.carrier ↔ H = K :=
begin
  split,
  { exact ext' },
  { intro h,
    rw h, }
end

@[ext] theorem ext {H K : top_subspace X} (h : ∀ x, x ∈ H ↔ x ∈ K) : H = K :=
begin
  apply ext',
  ext,
  apply h,
end

instance : has_le (top_subspace X) := {le := λ X Y, X.carrier ⊆ Y.carrier}

variable K : (top_subspace X)

lemma le_def : H ≤ K ↔ H.carrier ⊆ K.carrier :=
begin
  refl
end

lemma le_iff : H ≤ K ↔ ∀ g, g ∈ H → g ∈ K :=
begin
  refl,
end

lemma le_space : H ≤ to_subspace X := 
begin
  rw le_def, rw to_subspace, simp only [set.subset_univ],
end

@[refl] lemma subspace_le_refl {H : top_subspace X}: H ≤ H :=
begin
  rw le_def,
end

lemma subspace_le_antisymm : H ≤ K → K ≤ H → H = K :=
begin
  rw [le_def, le_def, ← ext'_iff],
  exact set.subset.antisymm,
end

@[trans] lemma subspace_le_trans {H J K : top_subspace X}: H ≤ J → J ≤ K → H ≤ K :=
begin
  rw [le_def, le_def, le_def],
  exact set.subset.trans,
end

instance {X : Type*} [topological_space X]: partial_order (top_subspace X) :=
{ le := (≤),
  le_refl := 
  begin
    intro a, apply subspace_le_refl,
  end,
  le_antisymm := 
  begin
    intros a b, apply subspace_le_antisymm,
  end,
  le_trans := 
  begin
    intros a b c, apply subspace_le_trans, 
  end}

-- open subspace
variables {A B : top_subspace X}

@[reducible] def open_incl (h: A ≤ B) : A → B :=
begin
  intro a, cases a, fconstructor, exact a_val, rw le_def at h, apply h, assumption,
end

lemma incl_open_map {X : Type*} [top_X : topological_space X] {A : top_subspace X} (x : set A) :
is_open x → is_open (set.image incl x):=
begin
  intro h, rw subspace_topology_equiv at *, cases h, cases h_h, rw is_open, rw incl,  simp, 
  have p : is_open (h_w ∩ A.carrier), apply is_open.inter, assumption, exact A.univ_open, unfold_coes at *,
  rw incl at *,
  simp at h_h_right,
  rw h_h_right at p, finish,
end

@[simp] lemma incl_composition (h: A ≤ B) : (incl ∘ (open_incl h)) = incl :=
begin
  rw open_incl,rw incl, rw incl, simp, ext1, simp, cases x, simp,
end

@[simp] lemma incl_set_composition (h: A ≤ B) (x : set A): incl '' (open_incl h '' x) = incl '' x :=
begin
  rw ←set.image_comp, rw incl_composition,
  -- ext1, split, intro s, cases s, cases s_h, fconstructor, 
end

@[simp] lemma incl_point_composition (h: A ≤ B) (x : A) : incl ((open_incl h) x) = incl x :=
begin
  rw open_incl, rw incl, rw incl, cases x, simp,
end

@[simp] lemma incl_self : incl '' (to_set A) = A.carrier :=
begin
  apply to_set_id,
end

lemma incl_inj {H: top_subspace X}: function.injective (@incl X _ H) :=
begin
  rw function.injective, intros a b,
  rw incl, cases a, cases b, finish,
end

-- @[simp] lemma incl_open_intersection (x : set A) (y : set A) : incl '' x ∩ incl '' y = incl '' (x ∩ y) :=
-- begin
--   apply incl_intersection,
-- end

-- @[simp] lemma incl_composition_asso (h: A ≤ B) (x : A): incl (open_incl h) = incl :=
-- begin
--   rw open_incl,rw incl, rw incl, cases x, simp,
-- end

-- @[simp] lemma set_incl_composition (h: A ≤ B) (x : set A): (incl ∘ (open_incl h))'' x = incl '' x :=
-- begin
--   ext1, split, intro hs,
-- end


theorem top_subspace_set_incl {X : Type*} [top_X : topological_space X] {A : top_subspace X} {B : top_subspace X} (x : set A)
(h: A ≤ B): is_open x → is_open (set.image (open_incl h) x):=
begin
  intro hs, have hrs : is_open (set.image incl x), apply incl_open_map, exact hs,
  rw subspace_topology_equiv, use (incl '' x), split, assumption, unfold_coes, rw incl_set_composition,
  simp, intro,intro hx, rw set.mem_preimage,rw incl, simp, cases x_1, solve_by_elim,
end

lemma range_incl {A : top_subspace X} : set.range (@incl X _ A) = A.carrier :=
begin
  rw set.range, ext1, split, intro hx, cases hx, cases hx_w, simp_rw incl at *, finish,
  intro hx, split, rotate, split, rotate, exact x, simp_rw incl, exact hx,
end

lemma incl_sub (x : A) (s : set A) : x ∈ s ↔ incl x ∈ incl '' s :=
begin
  split, intro hx, rw incl, finish,
  rw incl, intro hx, cases x, cases hx, simp at *, cases hx_h, cases hx_w, finish,
end

lemma incl_point_self (x : A) : incl x ∈ A.carrier :=
begin
  rw incl, cases x, simp, finish,
end

def top_subspace_incl {X : Type*} [top_X : topological_space X] {A : top_subspace X} {B : top_subspace X} (h : A ≤ B) : C(A,B) := { 
  to_fun :=  
  begin
    exact open_incl h,
  end,
  continuous_to_fun :=
  begin
    fconstructor, intro bns, intro hs, rw subspace_topology_equiv at *, cases hs with sX hsX, cases hsX with hsOpen ps,
    let ans : set X := sX ∩ A, use ans, fconstructor, apply is_open.inter, assumption, exact A.univ_open,
    rw set.subset.antisymm_iff, unfold_coes, have hp : open_incl h ⁻¹' bns = incl ⁻¹' ans,
    {
      rw set.preimage, rw set.preimage, ext1,split, intro hx, simp only [set.mem_set_of_eq] at hx, 
      rw incl_sub at hx, rw incl_point_composition at hx, unfold_coes at *,rw ←ps at hx, cases hx, fconstructor, 
      assumption, apply incl_point_self,
      intro hx, simp only [set.mem_set_of_eq] at hx, cases hx with hx1 hx2, simp only [set.mem_set_of_eq], rw incl_sub, rw incl_point_composition, rw le_iff at h, 
      have hx3: incl x ∈ B, apply h, assumption,have hx4 : incl x ∈ sX∩↑B, split, assumption, assumption, 
      have hx5: sX ∩ ↑B ⊆ incl '' bns, rotate,apply hx5, assumption, rw ps, unfold_coes,
    },
    {
        rw hp, simp only [set.inter_subset_left,
        set.image_subset_iff,
        and_true,
        set.subset_inter_iff,
        mem_coe_self,
        set.inter_subset_right,
        set.preimage_inter,
        and_self], rw ←set.preimage_inter, rw set.image_preimage_eq_of_subset, 
        intro x, intro hx, cases hx, fconstructor, finish,
        assumption, rw range_incl, sorry{finish},
    },
  end}

instance point_lift (h : A ≤ B): has_coe A B :=
begin
  fconstructor, exact open_incl h,
end

--- intersection and union of subspace ---

def intersection (A : top_subspace X) (B : top_subspace X) : top_subspace X :=
begin
  fconstructor, exact A.carrier ∩ B.carrier, apply is_open.inter, exact A.univ_open, exact B.univ_open,
end

instance : has_inter (top_subspace X) := {inter := intersection}

@[simp] theorem inter_sub : A ∩ B ≤ A := 
begin
  rw le_def, intro, intro hx, cases hx, assumption,
end

@[simp] theorem inter_sub2 : A ∩ B ≤ B := 
begin
  rw le_def, intro, intro hx, cases hx, assumption,
end

def union (A : top_subspace X) (B : top_subspace X) : top_subspace X :=
begin
  fconstructor, exact A.carrier ∪ B.carrier, apply is_open.union, exact A.univ_open, exact B.univ_open,
end

instance : has_union (top_subspace X) := {union := union}

@[simp] theorem union_sub : A ≤ A ∪ B :=
begin
  rw le_def, intro, intro hx, fconstructor, exact hx,
end

@[simp] theorem union_sub2 : B ≤ A ∪ B :=
begin
  rw le_def, intro, intro hx, simp at *, right, exact hx,
end


-- (backward) lift of element

def elem_backward_inclusion (x : X) (hx : x ∈ H) : H :=
begin
  fconstructor, exact x, exact hx,
end

instance hascoe_top : has_coe (top_subspace X) Top := 
begin
  fconstructor, intro x, exact Top.of x,
end
-- (backward) lift of function

@[simp] lemma incl_inj_eq {x y : H}: incl x = incl y ↔ x = y :=
begin
  rw incl, cases x, cases y, simp,
end

@[simp] lemma incl_carrier (a : H) : incl a ∈ H.carrier :=
begin
  cases a, simp_rw incl, assumption,
end 

lemma openincl_carrier {G : top_subspace X} (h : H ≤ G) (a : H) : incl a ∈ G.carrier :=
begin
  rw le_def at h, apply h, simp,
end

-- variables {A B : top_subspace X} {hAB : A≤ B}

-- instance subspace_has_coe (hAB : A ≤ B): has_coe (A : top_subspace X) (top_subspace B):=
-- begin
--   split, intro a, split, cases A, cases B, rw le_def at hAB, simp only [] at hAB,
--   cases a, tauto,
-- end

-- def subspace_lift {A B : top_subspace X} (hAB : A ≤ B): top_subspace B :=
-- begin
--   split, rw le_def at hAB, cases A, cases B, simp only [] at hAB, simp only [coe_sort_coe_base],
--   unfold_coes, simp only [], intro h, cases h, exact h_val ∈ A,
-- end

-- #check (@derived_topspace X _ A)
-- #check (@subspace_lift X _ A B hAB)
-- #check @derived_topspace B _ ((@subspace_lift X _ A B hAB) : top_subspace B)

-- theorem topology_equivalence (hAB : A ≤ B): (@derived_topspace X _ A).is_open = (@derived_topspace B _ (@subspace_lift X _ A B hAB)).is_open
-- def continuous_subspace_incl (A B : top_subspace X) {hAB : A ≤ B}: C(A,B) := 
-- { to_fun := 
--   begin
--     intro a, exact {val := a.val,
--     property := hAB a.property}
--   end,
--   continuous_to_fun := 
--   begin
--     fconstructor,
--   end, }


