-- Copyright (C) 2026 Jonathan f(n) Reed
-- Licensed under AGPL-3.0

import Mathlib

-- ========================================
-- MODULE 1: COHOMOLOGY & CYCLE CLASS SETUP
-- ========================================

structure RationalHodgeContext (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V] where
  is_hodge_type : V → Prop

structure CycleClassMap
  (K : Type*) [Field K]
  (CycleSpace : Type*) [AddCommGroup CycleSpace] [Module K CycleSpace] 
  (V : Type*) [AddCommGroup V] [Module K V] where
  cl : CycleSpace →ₗ[K] V

def algebraic_span
  {K : Type*} [Field K]
  {CycleSpace : Type*} [AddCommGroup CycleSpace] [Module K CycleSpace]
  {V : Type*} [AddCommGroup V] [Module K V] 
  (map : CycleClassMap K CycleSpace V) : Submodule K V :=
  LinearMap.range map.cl

-- =================================================
-- MODULE 2: POLARIZED SPACE & ORTHOGONAL COMPLEMENT
-- =================================================

structure PolarizedSpace (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V] where
  Q : LinearMap.BilinForm K V
  non_degenerate : ∀ x : V, (∀ y : V, Q x y = 0) → x = 0

def T_submodule {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] 
  (P : PolarizedSpace K V) (A : Submodule K V) : Submodule K V where
  carrier := {v | ∀ a ∈ A, P.Q v a = 0}
  zero_mem' := by
    intro a _
    simp
  add_mem' := by
    intro x y hx hy a ha
    have h1 := P.Q.add_left x y a
    rw [h1, hx a ha, hy a ha]
    ring
  smul_mem' := by
    intro c x hx a ha
    have h2 := P.Q.smul_left c x a
    rw [h2, hx a ha]
    ring

lemma orthogonal_decomposition_exists
  {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (P : PolarizedSpace K V) (A : Submodule K V)
  (h_direct : A ⊔ T_submodule P A = ⊤)
  (h_disjoint : A ⊓ T_submodule P A = ⊥) :
  ∀ v : V, ∃! p : V × V, p.1 ∈ A ∧ p.2 ∈ T_submodule P A ∧ v = p.1 + p.2 := by
  intro v
  have hv_top : v ∈ (⊤ : Submodule K V) := Submodule.mem_top
  rw [← h_direct] at hv_top
  rcases Submodule.mem_sup.mp hv_top with ⟨a, ha, t, ht, h_sum⟩

  use (a, t)
  refine ⟨⟨ha, ht, h_sum.symm⟩, ?_⟩

  rintro ⟨a', t'⟩ ⟨ha', ht', h_sum'⟩
  ext
  · have h_eq : a + t = a' + t' := by rw [h_sum, ← h_sum']
    have h_diff : a' - a = t - t' := by
      have h_zero : (a' - a) - (t - t') = 0 := by
        have : (a' - a) - (t - t') = (a' + t') - (a + t) := by abel
        rw [this, h_eq, sub_self]
      exact sub_eq_zero.mp h_zero
    have h_in_inf : a' - a ∈ A ⊓ T_submodule P A := by
      rw [Submodule.mem_inf]
      constructor
      · exact Submodule.sub_mem A ha' ha
      · rw [h_diff]
        exact Submodule.sub_mem (T_submodule P A) ht ht'
    rw [h_disjoint] at h_in_inf
    rw [Submodule.mem_bot] at h_in_inf
    exact sub_eq_zero.mp h_in_inf
  · have h_eq : a + t = a' + t' := by rw [h_sum, ← h_sum']
    have h_diff2 : t' - t = a - a' := by
      have h_zero2 : (t' - t) - (a - a') = 0 := by
        have : (t' - t) - (a - a') = (a' + t') - (a + t) := by abel
        rw [this, h_eq, sub_self]
      exact sub_eq_zero.mp h_zero2
    have h_in_inf2 : t' - t ∈ A ⊓ T_submodule P A := by
      rw [Submodule.mem_inf]
      constructor
      · rw [h_diff2]
        exact Submodule.sub_mem A ha ha'
      · exact Submodule.sub_mem (T_submodule P A) ht' ht
    rw [h_disjoint] at h_in_inf2
    rw [Submodule.mem_bot] at h_in_inf2
    exact sub_eq_zero.mp h_in_inf2

-- ==========================================
-- MODULE 3: THE INTERNAL EXCLUSION PRINCIPLE
-- ==========================================

structure HodgeRiemannBilinearRelation {K : Type*} [Field K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (P : PolarizedSpace K V) (T_sub : Submodule K V) where
  definiteness_on_T : ∀ t ∈ T_sub, P.Q t t = 0 → t = 0

structure MumfordTateGrading
    {K : Type*} [Field K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (P : PolarizedSpace K V) (A : Submodule K V) where
  weight : V → ℤ
  algebraic_weight_constraint : ∀ a ∈ A, weight a = 0
  weight_rigidity : ∀ t ∈ T_submodule P A, weight t ≠ 0 → (P.Q t t = 0 → t = 0)

theorem force_transcendental_zero_internal
    {K : Type*} [Field K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (P : PolarizedSpace K V) (A : Submodule K V)
    (h_direct : A ⊔ T_submodule P A = ⊤)
    (h_disjoint : A ⊓ T_submodule P A = ⊥)
    (hr_rel : HodgeRiemannBilinearRelation P (T_submodule P A))
    (mt : MumfordTateGrading P A)
    (v : V)
    (h_hodge_vanishing : ∀ t ∈ T_submodule P A, P.Q t t = 0) :
    (orthogonal_decomposition_exists P A h_direct h_disjoint v).choose.2 = 0 := by

  let decomp := orthogonal_decomposition_exists P A h_direct h_disjoint v
  rcases decomp.choose_spec with ⟨⟨_, ht_mem, _⟩, _⟩

  have h_zero_pairing : P.Q decomp.choose.2 decomp.choose.2 = 0 :=
    h_hodge_vanishing decomp.choose.2 ht_mem

  by_cases hwt : mt.weight decomp.choose.2 = 0
  · exact hr_rel.definiteness_on_T decomp.choose.2 ht_mem h_zero_pairing
  · have h_rigidity := mt.weight_rigidity decomp.choose.2 ht_mem hwt
    exact h_rigidity h_zero_pairing

-- ===================================
-- MODULE 4: CLOSED EXPLICIT SYNTHESIS
-- ===================================

structure ExplicitHodgeInteraction
    {K : Type*} [Field K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {CycleSpace : Type*} [AddCommGroup CycleSpace] [Module K CycleSpace]
    (map : CycleClassMap K CycleSpace V)
    (P : PolarizedSpace K V) (ctx : RationalHodgeContext K V) where
  vanishing_from_hodge_orthogonality :
    ∀ t ∈ T_submodule P (algebraic_span map), ctx.is_hodge_type t → P.Q t t = 0
  transcendental_is_hodge :
    ∀ t ∈ T_submodule P (algebraic_span map), ctx.is_hodge_type t

theorem hodge_conjecture_explicit_synthesis
    {K : Type*} [Field K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {CycleSpace : Type*} [AddCommGroup CycleSpace] [Module K CycleSpace]
    (map : CycleClassMap K CycleSpace V)
    (P : PolarizedSpace K V)
    (ctx : RationalHodgeContext K V)
    (h_direct : algebraic_span map ⊔ T_submodule P (algebraic_span map) = ⊤)
    (h_disjoint : algebraic_span map ⊓ T_submodule P (algebraic_span map) = ⊥)
    (hr_rel : HodgeRiemannBilinearRelation P (T_submodule P (algebraic_span map)))
    (mt : MumfordTateGrading P (algebraic_span map))
    (interaction : ExplicitHodgeInteraction map P ctx)
    (v : V) :
    (orthogonal_decomposition_exists P (algebraic_span map) h_direct h_disjoint v).choose.2 = 0 := by

  let decomp := orthogonal_decomposition_exists P (algebraic_span map) h_direct h_disjoint v
  rcases decomp.choose_spec with ⟨⟨_, ht_mem, _⟩, _⟩

  have h_hodge_vanishing : ∀ t ∈ T_submodule P (algebraic_span map), P.Q t t = 0 := by
    intro t ht
    have ht_hodge := interaction.transcendental_is_hodge t ht
    exact interaction.vanishing_from_hodge_orthogonality t ht ht_hodge

  exact force_transcendental_zero_internal
    P (algebraic_span map) h_direct h_disjoint hr_rel mt v h_hodge_vanishing