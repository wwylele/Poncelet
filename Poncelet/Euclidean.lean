import Mathlib
import Poncelet.Circle

open EuclideanGeometry Real RealInnerProductSpace



variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] [hrank : Fact (Module.finrank ℝ V = 2)]

omit [Fact (Module.finrank ℝ V = 2)] in
theorem finrank_direction_affineSpan_eq_two {p q : P} (h : p ≠ q) :
    Module.finrank ℝ (affineSpan ℝ {p, q}).direction = 1 := by
  classical
  have : ({p, q} : Set P) = Set.range ((↑) : ({p, q} : Finset P) → P) := by
    ext i
    simp
  rw [direction_affineSpan, this]
  apply AffineIndependent.finrank_vectorSpan ?_ ?_
  · rw [affineIndependent_iff_linearIndependent_vsub ℝ _ ⟨p, by simp⟩]
    have : Subsingleton {x : ({p, q} : Finset P) // x ≠ ⟨p, by simp⟩} :=
      ⟨by grind⟩
    apply LinearIndependent.of_subsingleton ⟨⟨q, by simp⟩, by simpa using h.symm⟩
    simpa using h.symm
  · simpa using Finset.card_eq_two.mpr ⟨_, _, h, rfl⟩

theorem proj_two {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (h : ⟪x, y⟫ = 0) (v : V) :
    ⟪v, x⟫ ^ 2 / ‖x‖ ^ 2 + ⟪v, y⟫ ^ 2 / ‖y‖ ^ 2 = ‖v‖ ^ 2 := by
  have h_basis : LinearIndependent ℝ ![x, y] := by
    rw [LinearIndependent.pair_iff' hx]
    intro a ha
    simpa [h, inner_smul_left, hy] using congr(⟪$ha, y⟫).symm
  have hrangexy : {x, y} = Set.range ![x, y] := by aesop
  have h_span : Module.finrank ℝ (Submodule.span ℝ {x, y}) = 2 := by
    convert finrank_span_eq_card h_basis
  have h_submodule_eq_top : Submodule.span ℝ {x, y} = ⊤ := by
    have h_finite_dim : FiniteDimensional ℝ V := by
      exact FiniteDimensional.of_finrank_pos (by simp [hrank.1])
    apply Submodule.eq_top_of_finrank_eq
    rw [h_span, hrank.1]
  have h_basis : Submodule.span ℝ {x, y} = ⊤ := by
    exact h_submodule_eq_top
  obtain ⟨a, b, hv⟩ : ∃ a b : ℝ, v = a • x + b • y := by
    have := h_basis.ge (Submodule.mem_top : v ∈ ⊤)
    rw [Submodule.mem_span_pair] at this
    tauto
  have h' : ⟪y, x⟫ = 0 := by
    rw [real_inner_comm]
    exact h
  simp [hv, h, h',
    inner_add_left, inner_smul_left, inner_smul_right, norm_add_sq_real, norm_smul, mul_pow, field]


def edge {n : ℕ} [NeZero n]
    (a : Fin n → P) (i : Fin n) :=
  affineSpan ℝ {a i, a (i + 1)}

def IsProperPolygon
    {n : ℕ} [NeZero n] (a : Fin n → P) :=
  ∀ i, a i ≠ a (i + 1) ∧ edge a i ≠ edge a (i + 1)

def Inscribe {n : ℕ} [NeZero n] (a : Fin n → P) (s : Sphere P) :=
  ∀ i, a i ∈ s

def Circumscribe {n : ℕ} [NeZero n] (a : Fin n → P) (s : Sphere P) :=
  ∀ i, s.IsTangent (edge a i)

variable (P) in
structure EuConfig where
  o : Sphere P
  i : Sphere P
  o_pos : 0 < o.radius
  i_pos : 0 < i.radius
  inside : ∀ p ∈ i, dist p o.center < o.radius
  center : o.center ≠ i.center

namespace EuConfig
variable (cf : EuConfig P)

def xAxis := affineSpan ℝ {cf.o.center, cf.i.center}

omit [Fact (Module.finrank ℝ V = 2)] in
theorem finrank_direction_xAxis : Module.finrank ℝ cf.xAxis.direction = 1 := by
  apply finrank_direction_affineSpan_eq_two cf.center

def yAxis := AffineSubspace.mk' cf.i.center cf.xAxis.directionᗮ

theorem finrank_direction_yAxis : Module.finrank ℝ cf.yAxis.direction = 1 := by
  have : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_pos (by simp [hrank.out])
  rw [← add_right_inj (Module.finrank ℝ cf.xAxis.direction)]
  rw [yAxis, AffineSubspace.direction_mk', Submodule.finrank_add_finrank_orthogonal]
  simp [finrank_direction_xAxis, hrank.out]

theorem eixsts_mem_yAxis_ne_center_i :
    ∃ p ∈ cf.yAxis, p ≠ cf.i.center := by
  by_contra! h
  have : cf.yAxis ≤ affineSpan ℝ {cf.i.center}  := by
    intro p hp
    simpa using h p hp
  obtain hdir := Submodule.finrank_mono <| AffineSubspace.direction_le this
  rw [finrank_direction_yAxis, direction_affineSpan] at hdir
  simp at hdir

noncomputable
def yDir := cf.eixsts_mem_yAxis_ne_center_i.choose

theorem yDir_mem_yAxis : cf.yDir ∈ cf.yAxis := cf.eixsts_mem_yAxis_ne_center_i.choose_spec.1
theorem yDir_ne_center_i : cf.yDir ≠ cf.i.center := cf.eixsts_mem_yAxis_ne_center_i.choose_spec.2

theorem inner_yDir_center_o : ⟪cf.o.center -ᵥ cf.i.center, cf.yDir -ᵥ cf.i.center⟫ = 0 := by
  obtain hmem := cf.yDir_mem_yAxis
  rw [yAxis, AffineSubspace.mem_mk', Submodule.mem_orthogonal] at hmem
  apply hmem
  rw [xAxis, direction_affineSpan, mem_vectorSpan_pair]
  use 1
  simp

noncomputable
def toConfig : Config ℝ where
  u := dist cf.o.center cf.i.center / cf.i.radius
  r := cf.o.radius / cf.i.radius
  hu := by simp [cf.center, cf.i_pos.ne.symm]
  hr := by simp [cf.o_pos.ne.symm, cf.i_pos.ne.symm]
  k := √(((dist cf.o.center cf.i.center + cf.o.radius) / cf.i.radius) ^ 2 - 1)
  k_sq := by
    rw [sq_sqrt ?_]
    · ring
    apply sub_nonneg_of_le
    rw [one_le_sq_iff_one_le_abs, abs_div]
    rw [one_le_div (by simpa using cf.i_pos.ne.symm)]
    rw [(abs_add_eq_add_abs_iff _ _).mpr (Or.inl ⟨by simp, cf.o_pos.le⟩)]
    suffices |cf.i.radius| ≤ |cf.o.radius| from this.trans (by simp)

    sorry

noncomputable
def sendPoint (p : P) : P2 ℝ := P2.mk ![
  ⟪p -ᵥ cf.i.center, cf.o.center -ᵥ cf.i.center⟫ / (dist cf.o.center cf.i.center * cf.i.radius),
  ⟪p -ᵥ cf.i.center, cf.yDir -ᵥ cf.i.center⟫ / (dist cf.yDir cf.i.center * cf.i.radius),
  1] (by simp)

theorem mem_o_iff (p : P) :
    p ∈ cf.o ↔ OuterCircle (cf.toConfig) (cf.sendPoint p) := by
  rw [OuterCircle, sendPoint, EuclideanGeometry.mem_sphere]
  simp only [P2.lift_mk, Matrix.cons_val_zero, Matrix.cons_val, mul_one,
    Matrix.cons_val_one, one_pow]
  rw [toConfig]
  simp only
  simp_rw [← div_div, ← sub_div, div_pow, ← add_div, dist_eq_norm_vsub V]
  rw [div_left_inj' (by simpa using cf.i_pos.ne.symm)]
  rw [div_sub' (by simpa using cf.center), div_pow, ← real_inner_self_eq_norm_mul_norm]
  rw [← inner_sub_left]
  rw [vsub_sub_vsub_comm, vsub_self, sub_zero]
  rw [show ⟪p -ᵥ cf.i.center, cf.yDir -ᵥ cf.i.center⟫ =
        ⟪p -ᵥ cf.o.center, cf.yDir -ᵥ cf.i.center⟫ by
    rw [← sub_eq_zero, ← inner_sub_left, vsub_sub_vsub_comm, vsub_self, zero_sub,
      neg_vsub_eq_vsub_rev]
    apply inner_yDir_center_o]
  rw [proj_two (by simpa using cf.center) (by simpa using cf.yDir_ne_center_i)
    cf.inner_yDir_center_o]
  exact (sq_eq_sq₀ (by simp) cf.o_pos.le).symm

noncomputable
def sendChord (p : AffineSubspace ℝ P) : P2 ℝ :=
  if Module.finrank ℝ p.direction = 1 then
    sorry
  else
    P2.mk ![0, 0, 1] (by simp)

end EuConfig
/-


def sendChord (outer inner : Sphere P) (p : AffineSubspace ℝ P) : P2 ℝ := sorry

theorem isTangent_inner_iff_inner_sendChord
    (hor : 0 < outer.radius) (hir : 0 < inner.radius)
    (hsphere : ∀ p ∈ outer, inner.radius < dist p inner.center)
    (hcenter : outer.center ≠ inner.center) {q : AffineSubspace ℝ P}
    (hq : Module.finrank ℝ q.direction = 1) :
    inner.IsTangent q ↔ InnerCircle (config hor hir hsphere hcenter) (sendChord outer inner q) := by
  sorry

theorem mem_iff_incidence
    (hor : 0 < outer.radius) (hir : 0 < inner.radius)
    (hsphere : ∀ p ∈ outer, inner.radius < dist p inner.center)
    (hcenter : outer.center ≠ inner.center) (p : P) {q : AffineSubspace ℝ P}
    (hq : Module.finrank ℝ q.direction = 1) :
    p ∈ q ↔ Incidence (config hor hir hsphere hcenter)
      (sendPoint outer inner p) (sendChord outer inner q) := by
  sorry

def receivePoint (outer inner : Sphere P) (p : P2 ℝ) : P :=
  sorry

def receiveChord (outer inner : Sphere P) (p : P2 ℝ) : AffineSubspace ℝ P :=
  sorry

def IsFinitePoint (p : P2 ℝ) : Prop :=
  sorry

theorem sendPoint_receivePoint (hor : 0 < outer.radius) (hir : 0 < inner.radius)
    (hsphere : ∀ p ∈ outer, inner.radius < dist p inner.center)
    (hcenter : outer.center ≠ inner.center) {p : P2 ℝ} (h : IsFinitePoint p) :
    sendPoint outer inner (receivePoint outer inner p) = p := by
  sorry

theorem receivePoint_sendPoint (hor : 0 < outer.radius) (hir : 0 < inner.radius)
    (hsphere : ∀ p ∈ outer, inner.radius < dist p inner.center)
    (hcenter : outer.center ≠ inner.center) (p : P) :
    receivePoint outer inner (sendPoint outer inner p) = p := by
  sorry

theorem isTangent_iff_eq_rPoint (hor : 0 < outer.radius) (hir : 0 < inner.radius)
    (hsphere : ∀ p ∈ outer, inner.radius < dist p inner.center)
    (hcenter : outer.center ≠ inner.center) {p1 p2 : P} (h : p1 ≠ p2) :
    inner.IsTangent (affineSpan ℝ {p1, p2}) ↔
    sendPoint outer inner p2 =
    (rPoint (config hor hir hsphere hcenter)
      ⟨sendPoint outer inner p1, sendChord outer inner (affineSpan ℝ {p1, p2})⟩).1 := by
  sorry


theorem poncelet {outer inner : Sphere P} (hor : 0 < outer.radius) (hir : 0 < inner.radius)
    (hsphere : ∀ p ∈ outer, inner.radius < dist p inner.center)
    (hcenter : outer.center ≠ inner.center)
    {n : ℕ} [NeZero n] {a : Fin n → P}
    (houter : Inscribe a outer) (hinner : Circumscribe a inner)
    (ha : IsProperPolygon a) {x : P} (hx : x ∈ outer) :
    ∃ b : Fin n → P, b 0 = x ∧ Inscribe b outer ∧ Circumscribe b inner := by sorry
-/
