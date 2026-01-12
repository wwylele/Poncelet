import Mathlib
import Poncelet.Circle

open EuclideanGeometry Real RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)]

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

variable {outer inner : Sphere P}

noncomputable
def config (hor : 0 < outer.radius) (hir : 0 < inner.radius)
    (hsphere : ∀ p ∈ outer, inner.radius < dist p inner.center)
    (hcenter : outer.center ≠ inner.center) : Config ℝ where
  u := dist outer.center inner.center / inner.radius
  r := outer.radius / inner.radius
  hu := by simp [hcenter, hir.ne.symm]
  hr := by simp [hor.ne.symm, hir.ne.symm]
  k := √(((dist outer.center inner.center + outer.radius) / inner.radius) ^ 2 - 1)
  k_sq := by
    rw [sq_sqrt ?_]
    · ring
    apply sub_nonneg_of_le
    rw [one_le_sq_iff_one_le_abs, abs_div]
    rw [one_le_div (by simpa using hir.ne.symm)]
    let axis := affineSpan ℝ {inner.center, outer.center}
    obtain hsphere := hsphere
    sorry

noncomputable
def sendPoint (outer inner : Sphere P) (p : P) : P2 ℝ := P2.mk ![
  sorry,
  sorry,
  1] (by simp)

theorem mem_outer_iff_outer_sendPoint
    (hor : 0 < outer.radius) (hir : 0 < inner.radius)
    (hsphere : ∀ p ∈ outer, inner.radius < dist p inner.center)
    (hcenter : outer.center ≠ inner.center) (p : P) :
    p ∈ outer ↔ OuterCircle (config hor hir hsphere hcenter) (sendPoint outer inner p) := by
  sorry

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


theorem poncelet {n : ℕ} [NeZero n]
    {a : Fin n → P} (houter : Inscribe a outer) (hinner : Circumscribe a inner)
    (ha : IsProperPolygon a) {x : P} (hx : x ∈ outer) :
    ∃ b : Fin n → P, b 0 = x ∧ Inscribe b outer ∧ Circumscribe b inner := by sorry
