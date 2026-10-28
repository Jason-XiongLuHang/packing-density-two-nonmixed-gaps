import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Equiv.Fin.Rotate
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 800000
open scoped BigOperators
open Finset

namespace TwoGap

def Box (a b k m d : ℤ) : Prop :=
  ∃ i j : ℤ, 0 ≤ i ∧ i ≤ k ∧ 0 ≤ j ∧ j ≤ m ∧
    0 < i + j ∧ d = i * a + j * b

def Avoid (a b k m : ℤ) (A : Finset ℤ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x < y → ¬ Box a b k m (y - x)

def CyclicForbidden (a b k m D δ : ℤ) : Prop :=
  ∃ d : ℤ, Box a b k m d ∧ 0 < d ∧ d < D ∧ D ∣ d - δ

lemma mod_unique {D x y : ℤ} (hD : 0 < D)
    (hx : 0 ≤ x ∧ x < D) (hy : 0 ≤ y ∧ y < D)
    (h : D ∣ x - y) : x = y := by
  rcases h with ⟨r, hr⟩
  have hr0 : r = 0 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hn | hn
    · have : r ≤ -1 := by omega
      nlinarith
    · have : 1 ≤ r := by omega
      nlinarith
  subst r
  nlinarith

lemma canonical_lift {a b k m u v δ ell : ℤ}
    (hm : 0 < m) (hbez : a * u + b * v = 1)
    (hd : k*a + m*b ∣ (m*u-k*v)*δ-ell) :
    ∃ p q : ℤ, 0 ≤ q ∧ q < m ∧ m*p-k*q=ell ∧
      k*a+m*b ∣ a*p+b*q-δ := by
  rcases hd with ⟨r, hr⟩
  let p₁ := u*δ-r*b
  let q₁ := v*δ+r*a
  have h₁ : m*p₁-k*q₁=ell := by dsimp [p₁,q₁]; nlinarith [hr]
  have h₂ : a*p₁+b*q₁=δ := by
    calc
      a*p₁+b*q₁ = (a*u+b*v)*δ := by dsimp [p₁,q₁]; ring
      _ = δ := by rw [hbez]; ring
  let s := q₁ / m
  let q := q₁ % m
  let p := p₁-k*s
  have hmod := Int.emod_nonneg q₁ (ne_of_gt hm)
  have hlt := Int.emod_lt_of_pos q₁ hm
  have hsplit : m*s+q=q₁ := by simpa [s,q] using Int.ediv_add_emod q₁ m
  refine ⟨p,q,hmod,hlt,?_,?_⟩
  · change m*(p₁-k*s)-k*q=ell
    calc
      m*(p₁-k*s)-k*q = m*p₁-k*(m*s+q) := by ring
      _ = ell := by rw [hsplit]; exact h₁
  · refine ⟨-s, ?_⟩
    change a*(p₁-k*s)+b*q-δ=(k*a+m*b)*(-s)
    calc
      a*(p₁-k*s)+b*q-δ = (a*p₁+b*q₁-δ)-(k*a+m*b)*s := by
        rw [← hsplit]; ring
      _ = (k*a+m*b)*(-s) := by rw [h₂]; ring

lemma ordinary_lift {a b k m u v δ ell : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) (hm : 0 < m)
    (hbez : a*u+b*v=1) (hell : 0 < ell)
    (hd : k*a+m*b ∣ (m*u-k*v)*δ-ell)
    (hnot : ¬ CyclicForbidden a b k m (k*a+m*b) δ) :
    ∃ p q : ℤ, 1 ≤ p ∧ q ≤ -1 ∧ m*p-k*q=ell ∧
      k*a+m*b ∣ a*p+b*q-δ := by
  obtain ⟨p,q,hq,hqm,hh,hr⟩ := canonical_lift hm hbez hd
  have hp : 0 < p := by nlinarith
  have hpk : k < p := by
    by_contra hle
    have hle : p ≤ k := by omega
    apply hnot
    refine ⟨a*p+b*q, ?_, ?_, ?_, ?_⟩
    · exact ⟨p,q,le_of_lt hp,hle,hq,le_of_lt hqm,by omega,by ring⟩
    · nlinarith
    · nlinarith
    · exact hr
  refine ⟨p-k,q-m,by omega,by omega,?_,?_⟩
  · nlinarith [hh]
  · obtain ⟨r,hr⟩ := hr
    refine ⟨r-1,?_⟩
    nlinarith [hr]

lemma flux {a b k m B C I J D : ℤ} (hD : D=k*a+m*b) (hpos : 0 < D)
    (hi : B ≤ I) (hj : C ≤ -J)
    (height : m*I-k*J=D) (closed : D ∣ a*I+b*J) :
    ∃ h : ℤ, B ≤ b+k*h ∧ C ≤ a-m*h := by
  obtain ⟨h,hh⟩ := closed
  have ei : I=b+k*h := by
    have hz : D*I=D*(b+k*h) := by
      calc
        D*I = b*(m*I-k*J)+k*(a*I+b*J) := by rw [hD]; ring
        _ = b*D+k*(D*h) := by rw [height,hh]
        _ = D*(b+k*h) := by ring
    nlinarith
  have ej : J=-a+m*h := by
    have hz : D*J=D*(-a+m*h) := by
      calc
        D*J = -a*(m*I-k*J)+m*(a*I+b*J) := by rw [hD]; ring
        _ = -a*D+m*(D*h) := by rw [height,hh]
        _ = D*(-a+m*h) := by ring
    nlinarith
  exact ⟨h,by omega,by omega⟩

lemma box_pos {a b k m d : ℤ} (ha : 0 < a) (hb : 0 < b)
    (h : Box a b k m d) : 0 < d := by
  obtain ⟨i,j,hi,hik,hj,hjm,hij,rfl⟩ := h
  have hia := mul_nonneg hi (show 0 ≤ a-1 by omega)
  have hjb := mul_nonneg hj (show 0 ≤ b-1 by omega)
  nlinarith

lemma residue_cases {D r δ : ℤ} (hD : 0 < D)
    (hr : 0 ≤ r ∧ r < D) (hd : -2*D < δ ∧ δ < 2*D)
    (h : D ∣ r-δ) :
    δ=r-2*D ∨ δ=r-D ∨ δ=r ∨ δ=r+D := by
  obtain ⟨s,hs⟩ := h
  have hlo : -1 ≤ s := by
    by_contra hn
    have : s ≤ -2 := by omega
    nlinarith
  have hhi : s ≤ 2 := by
    by_contra hn
    have : 3 ≤ s := by omega
    nlinarith
  have hc : s=-1 ∨ s=0 ∨ s=1 ∨ s=2 := by omega
  rcases hc with hc|hc|hc|hc <;> subst s <;> omega

lemma basic_bounds {a b k m : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) (hm : 0 < m) :
    0 < k*a+m*b ∧ a < k*a+m*b := by
  have hka := mul_nonneg (show 0 ≤ k-1 by omega) (le_of_lt ha)
  have hmb := mul_pos hm hb
  constructor <;> nlinarith

lemma pair_lift {a b k m u v x y ell : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) (hm : 0 < m)
    (hbez : a*u+b*v=1)
    (hx : 0 ≤ x ∧ x < k*a+m*b+a) (hy : 0 ≤ y ∧ y < k*a+m*b+a)
    (havoid : ¬Box a b k m (y-x) ∧ ¬Box a b k m (x-y))
    (hell : 0 < ell)
    (hd : k*a+m*b ∣ (m*u-k*v)*(y-x)-ell) :
    ∃ p q : ℤ, (if x < k*a+m*b+b then 1 else 0) ≤ p ∧ q ≤ -1 ∧
      m*p-k*q=ell ∧ k*a+m*b ∣ a*p+b*q-(y-x) := by
  classical
  obtain ⟨hD,haD⟩ := basic_bounds ha hb hk hm
  obtain ⟨p,q,hq,hqm,hh,hr⟩ := canonical_lift hm hbez hd
  have hp : 1 ≤ p := by nlinarith
  by_cases hpk : k < p
  · refine ⟨p-k,q-m,?_,by omega,?_,?_⟩
    · split_ifs <;> omega
    · nlinarith [hh]
    · obtain ⟨s,hs⟩ := hr
      exact ⟨s-1,by nlinarith [hs]⟩
  · have hpk : p ≤ k := by omega
    have hdlo : 0 < a*p+b*q := by nlinarith
    have hdhi : a*p+b*q < k*a+m*b := by nlinarith
    have hδ : -2*(k*a+m*b) < y-x ∧ y-x < 2*(k*a+m*b) := by omega
    have cases := residue_cases hD ⟨le_of_lt hdlo,hdhi⟩ hδ hr
    rcases cases with hc|hc|hc|hc
    · have hsmall : k*a+m*b-(a*p+b*q) < a := by omega
      have hpeq : p=k := by
        by_contra hn
        have : p ≤ k-1 := by omega
        have hmul := mul_nonneg (show 0 ≤ k-p-1 by omega) (le_of_lt ha)
        nlinarith
      subst p
      have hcut : ¬ x < k*a+m*b+b := by nlinarith
      refine ⟨0,-(m-q),by simp [hcut],by omega,?_,?_⟩
      · nlinarith [hh]
      · refine ⟨1,?_⟩
        nlinarith [hc]
    · apply False.elim
      apply havoid.2
      refine ⟨k-p,m-q,by omega,by omega,by omega,by omega,by omega,?_⟩
      nlinarith [hc]
    · exact False.elim (havoid.1 ⟨p,q,by omega,hpk,hq,by omega,by omega,by nlinarith [hc]⟩)
    · have hsmall : a*p+b*q < a := by omega
      nlinarith

lemma pair_avoid {a b k m : ℤ} {A : Finset ℤ}
    (ha : 0 < a) (hb : 0 < b) (hA : Avoid a b k m A)
    {x y : ℤ} (hx : x ∈ A) (hy : y ∈ A) :
    ¬Box a b k m (y-x) ∧ ¬Box a b k m (x-y) := by
  constructor
  · intro h
    exact hA x hx y hy (by have := box_pos ha hb h; omega) h
  · intro h
    exact hA y hy x hx (by have := box_pos ha hb h; omega) h

lemma height_injective {a b k m u v : ℤ} {A : Finset ℤ}
    (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) (hm : 0 < m)
    (hbez : a*u+b*v=1) (hA : Avoid a b k m A)
    (hwin : ∀ z ∈ A, 0 ≤ z ∧ z < k*a+m*b+a) :
    Set.InjOn (fun z : ℤ => ((m*u-k*v)*z) % (k*a+m*b)) ↑A := by
  intro x hx y hy heq
  by_contra hne
  wlog hxy : x < y generalizing x y
  · exact this hy hx (Eq.symm heq) (Ne.symm hne) (by omega)
  obtain ⟨hD,haD⟩ := basic_bounds ha hb hk hm
  have hpair := pair_avoid ha hb hA hx hy
  have hd : k*a+m*b ∣ (m*u-k*v)*(y-x)-0 := by
    have hz : Int.ModEq (k*a+m*b) ((m*u-k*v)*x) ((m*u-k*v)*y) := heq
    have hw := hz.dvd
    convert hw using 1 <;> ring
  obtain ⟨p,q,hq,hqm,hh,hr⟩ := canonical_lift hm hbez hd
  have hp : 0 ≤ p := by nlinarith
  have hpk : p < k := by nlinarith
  have hdlo : 0 ≤ a*p+b*q := by positivity
  have hdhi : a*p+b*q < k*a+m*b := by nlinarith
  have hδ : -2*(k*a+m*b) < y-x ∧ y-x < 2*(k*a+m*b) := by
    have := hwin x hx; have := hwin y hy; omega
  rcases residue_cases hD ⟨hdlo,hdhi⟩ hδ hr with hc|hc|hc|hc
  · omega
  · omega
  · apply hpair.1
    refine ⟨p,q,hp,by omega,hq,by omega,?_,by nlinarith [hc]⟩
    by_contra hn
    have hpq : p=0 ∧ q=0 := by omega
    rcases hpq with ⟨rfl,rfl⟩
    omega
  · have hsmall : a*p+b*q < a := by
      have := hwin x hx; have := hwin y hy; omega
    have hp0 : p=0 := by nlinarith
    have hq0 : q=0 := by nlinarith [hh]
    subst p; subst q
    apply hpair.1
    refine ⟨k,m,by omega,by omega,by omega,by omega,by omega,?_⟩
    nlinarith [hc]

def gap {n : ℕ} (D : ℤ) (r : Fin (n+1) → ℤ) (i : Fin (n+1)) : ℤ :=
  r (finRotate (n+1) i) - r i + if i=Fin.last n then D else 0

lemma gaps_positive {n : ℕ} {D : ℤ} {r : Fin (n+1) → ℤ}
    (hn : 0 < n) (hmono : StrictMono r)
    (hr : ∀ i, 0 ≤ r i ∧ r i < D) :
    ∀ i, 0 < gap D r i ∧ gap D r i < D := by
  intro i
  by_cases hi : i=Fin.last n
  · subst i
    have hlt : (0 : Fin (n+1)) < Fin.last n := by
      change 0 < n
      exact hn
    have hs := hmono hlt
    have h₀ := hr 0
    have h₁ := hr (Fin.last n)
    simp only [gap,finRotate_last,if_pos rfl,ite_true]
    constructor <;> omega
  · have hs := hmono ((lt_finRotate_iff_ne_last i).mpr hi)
    have h₀ := hr i
    have h₁ := hr (finRotate (n+1) i)
    simp only [gap,if_neg hi]
    constructor <;> omega

lemma gaps_sum {n : ℕ} (D : ℤ) (r : Fin (n+1) → ℤ) :
    ∑ i, gap D r i = D := by
  simp only [gap,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [Equiv.sum_comp (finRotate (n+1)) r]
  simp

lemma gap_congruence {n : ℕ} {D t : ℤ} {z r : Fin (n+1) → ℤ}
    (hr : ∀ i, (t*z i)%D=r i) :
    ∀ i, D ∣ t*(z (finRotate (n+1) i)-z i)-gap D r i := by
  intro i
  have h₁ := Int.dvd_sub_of_emod_eq (hr (finRotate (n+1) i))
  have h₂ := Int.dvd_sub_of_emod_eq (hr i)
  have h₃ := dvd_sub h₁ h₂
  by_cases hi : i=Fin.last n
  · have h₄ := dvd_sub h₃ (dvd_refl D)
    convert h₄ using 1 <;> simp [gap,hi] <;> ring
  · convert h₃ using 1 <;> simp [gap,hi] <;> ring

lemma indexed_staircase {n : ℕ} {a b k m u v : ℤ} {A : Finset ℤ}
    (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) (hm : 0 < m)
    (hbez : a*u+b*v=1) (hA : Avoid a b k m A)
    (hn : 0 < n) (z r : Fin (n+1) → ℤ)
    (hz : ∀ i, z i ∈ A)
    (hwin : ∀ i, 0 ≤ z i ∧ z i < k*a+m*b+a)
    (hmono : StrictMono r)
    (hrange : ∀ i, 0 ≤ r i ∧ r i < k*a+m*b)
    (hphi : ∀ i, ((m*u-k*v)*z i)%(k*a+m*b)=r i) :
    ∃ h : ℤ, (∑ i, if z i < k*a+m*b+b then (1:ℤ) else 0) ≤ b+k*h ∧
      (n+1:ℤ) ≤ a-m*h := by
  classical
  let D := k*a+m*b
  let rho := finRotate (n+1)
  have hD : 0 < D := (basic_bounds ha hb hk hm).1
  have hg := gaps_positive hn hmono hrange
  have hc := gap_congruence hphi
  have hl : ∀ i, ∃ p q : ℤ,
      (if z i < D+b then 1 else 0) ≤ p ∧ q ≤ -1 ∧
      m*p-k*q=gap D r i ∧ D ∣ a*p+b*q-(z (rho i)-z i) := by
    intro i
    exact pair_lift ha hb hk hm hbez (hwin i) (hwin (rho i))
      (pair_avoid ha hb hA (hz i) (hz (rho i))) (hg i).1 (hc i)
  choose p q hp hq hheight hclosed using hl
  let I := ∑ i, p i
  let J := ∑ i, q i
  have hi : (∑ i, if z i < D+b then (1:ℤ) else 0) ≤ I := by
    exact Finset.sum_le_sum (fun i _ => hp i)
  have hj : (n+1:ℤ) ≤ -J := by
    have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hq i)
    simpa [J] using (neg_le_neg hs)
  have height : m*I-k*J=D := by
    calc
      m*I-k*J = ∑ i, (m*p i-k*q i) := by
        simp only [I,J,Finset.sum_sub_distrib,Finset.mul_sum]
      _ = ∑ i, gap D r i := by simp only [hheight]
      _ = D := gaps_sum D r
  have telescope : (∑ i, (z (rho i)-z i))=0 := by
    rw [Finset.sum_sub_distrib,Equiv.sum_comp rho z]
    simp
  have closed : D ∣ a*I+b*J := by
    have hs := Finset.dvd_sum (fun i (_ : i ∈ Finset.univ) => hclosed i)
    have heq : (∑ i, (a*p i+b*q i-(z (rho i)-z i)))=a*I+b*J := by
      rw [Finset.sum_sub_distrib,telescope]
      simp only [I,J,Finset.sum_add_distrib,Finset.mul_sum,sub_zero]
    rwa [heq] at hs
  exact flux rfl hD hi hj height closed

theorem staircase_of_bezout {a b k m u v : ℤ} (A : Finset ℤ)
    (ha : b < a) (hb : 0 < b) (hk : 0 < k) (hm : 0 < m)
    (hbez : a*u+b*v=1) (hA : Avoid a b k m A)
    (hwin : ∀ z ∈ A, 0 ≤ z ∧ z < k*a+m*b+a) :
    ∃ h : ℤ, ((A.filter (fun z => z < k*a+m*b+b)).card:ℤ) ≤ b+k*h ∧
      (A.card:ℤ) ≤ a-m*h := by
  classical
  have ha0 : 0 < a := by omega
  by_cases hsmall : A.card ≤ 1
  · refine ⟨0,?_,?_⟩
    · have := Finset.card_filter_le (s:=A) (p:=fun z => z < k*a+m*b+b)
      simp only [mul_zero,add_zero]
      omega
    · simp only [mul_zero,sub_zero]
      omega
  · have hbig : 2 ≤ A.card := by omega
    let t := m*u-k*v
    let D := k*a+m*b
    let phi := fun z : ℤ => (t*z)%D
    let H := A.image phi
    have hinj : Set.InjOn phi ↑A := height_injective ha0 hb hk hm hbez hA hwin
    have hcard : H.card=A.card := Finset.card_image_of_injOn hinj
    let n := A.card-1
    have hnc : A.card=n+1 := by dsimp [n]; omega
    have hn : 0 < n := by dsimp [n]; omega
    have hH : H.card=n+1 := hcard.trans hnc
    let o : Fin (n+1) ≃o H := H.orderIsoOfFin hH
    let f : A → H := fun z => ⟨phi z,Finset.mem_image.mpr ⟨z,z.property,rfl⟩⟩
    have hf : Function.Bijective f := by
      constructor
      · intro x y heq
        apply Subtype.ext
        exact hinj x.property y.property (congrArg Subtype.val heq)
      · intro y
        obtain ⟨x,hx,hxy⟩ := Finset.mem_image.mp y.property
        exact ⟨⟨x,hx⟩,Subtype.ext hxy⟩
    let e : A ≃ H := Equiv.ofBijective f hf
    let ze : Fin (n+1) ≃ A := o.toEquiv.trans e.symm
    let z : Fin (n+1) → ℤ := fun i => (ze i).val
    let r : Fin (n+1) → ℤ := fun i => (o i).val
    have hphi : ∀ i, phi (z i)=r i := by
      intro i
      have hz : e (ze i)=o i := by
        change e (e.symm (o i))=o i
        exact e.apply_symm_apply _
      exact congrArg Subtype.val hz
    have hz : ∀ i, z i ∈ A := fun i => (ze i).property
    have hmono : StrictMono r := by
      intro i j hij
      exact o.strictMono hij
    have hrange : ∀ i, 0 ≤ r i ∧ r i < D := by
      intro i
      rw [← hphi i]
      exact ⟨Int.emod_nonneg _ (ne_of_gt (basic_bounds ha0 hb hk hm).1),
        Int.emod_lt_of_pos _ (basic_bounds ha0 hb hk hm).1⟩
    obtain ⟨h,hB,hC⟩ := indexed_staircase ha0 hb hk hm hbez hA hn z r hz
      (fun i => hwin (z i) (hz i)) hmono hrange hphi
    have hsum : (∑ i, if z i < D+b then (1:ℤ) else 0)=
        ((A.filter (fun z => z < D+b)).card:ℤ) := by
      change (∑ i, (fun x : A => if x.val < D+b then (1:ℤ) else 0) (ze i))=_
      rw [Equiv.sum_comp ze (fun x : A => if x.val < D+b then (1:ℤ) else 0),
        Finset.sum_coe_sort A (fun x : ℤ => if x < D+b then (1:ℤ) else 0)]
      rw [← Finset.sum_filter]
      simp
    refine ⟨h,?_,?_⟩
    · change (∑ i, if z i < D+b then (1:ℤ) else 0) ≤ b+k*h at hB
      rw [hsum] at hB
      exact hB
    · have hc : (A.card:ℤ)=(n+1:ℤ) := by omega
      rwa [hc]

theorem staircase {a b k m : ℤ} (A : Finset ℤ)
    (ha : b < a) (hb : 0 < b) (hk : 0 < k) (hm : 0 < m)
    (hcoprime : Int.gcd a b=1) (hA : Avoid a b k m A)
    (hwin : ∀ z ∈ A, 0 ≤ z ∧ z < k*a+m*b+a) :
    ∃ h : ℤ, ((A.filter (fun z => z < k*a+m*b+b)).card:ℤ) ≤ b+k*h ∧
      (A.card:ℤ) ≤ a-m*h := by
  have hbez : a*Int.gcdA a b+b*Int.gcdB a b=1 := by
    simpa [hcoprime] using (Int.gcd_eq_gcd_ab a b).symm
  exact staircase_of_bezout A ha hb hk hm hbez hA hwin

noncomputable def window (S : Set ℤ) (N : ℤ) : Finset ℤ := by
  classical
  exact (Finset.Ico 0 N).filter (fun z => z ∈ S)

@[simp] lemma mem_window {S : Set ℤ} {N z : ℤ} :
    z ∈ window S N ↔ 0 ≤ z ∧ z < N ∧ z ∈ S := by
  classical
  simp [window,and_assoc]

def SetAvoid (a b k m : ℤ) (S : Set ℤ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x < y → ¬Box a b k m (y-x)

/-- The manuscript's complete two-window theorem, for arbitrary subsets of Z. -/
theorem two_window_staircase {a b k m : ℤ} (S : Set ℤ)
    (ha : b < a) (hb : 0 < b) (hk : 0 < k) (hm : 0 < m)
    (hcoprime : Int.gcd a b=1) (hS : SetAvoid a b k m S) :
    ∃ h : ℤ, ((window S (k*a+m*b+b)).card:ℤ) ≤ b+k*h ∧
      ((window S (k*a+m*b+a)).card:ℤ) ≤ a-m*h := by
  classical
  let D := k*a+m*b
  let A := window S (D+a)
  have hwin : ∀ z ∈ A, 0 ≤ z ∧ z < D+a := by
    intro z hz
    have hz := mem_window.mp hz
    exact ⟨hz.1,hz.2.1⟩
  have hA : Avoid a b k m A := by
    intro x hx y hy hxy
    exact hS x (mem_window.mp hx).2.2 y (mem_window.mp hy).2.2 hxy
  have hw : A.filter (fun z => z < D+b)=window S (D+b) := by
    ext z
    dsimp only [A]
    simp only [Finset.mem_filter,mem_window]
    change ((0 ≤ z ∧ z < D+a ∧ z ∈ S) ∧ z < D+b) ↔
      (0 ≤ z ∧ z < D+b ∧ z ∈ S)
    constructor
    · rintro ⟨⟨hz0,hza,hzS⟩,hzb⟩
      exact ⟨hz0,hzb,hzS⟩
    · rintro ⟨hz0,hzb,hzS⟩
      exact ⟨⟨hz0,by omega,hzS⟩,hzb⟩
  obtain ⟨h,hB,hC⟩ := staircase A ha hb hk hm hcoprime hA hwin
  refine ⟨h,?_,hC⟩
  change ((A.filter (fun z => z < D+b)).card:ℤ) ≤ b+k*h at hB
  rwa [hw] at hB

/-- Integer ceiling division; for positive k this is ceil(z/k). -/
def ceilDiv (z k : ℤ) : ℤ := -((-z)/k)

lemma ceilDiv_le_iff {z k h : ℤ} (hk : 0 < k) :
    ceilDiv z k ≤ h ↔ z ≤ k*h := by
  unfold ceilDiv
  constructor
  · intro hh
    have he : -h ≤ (-z)/k := by omega
    have hx := (Int.le_ediv_iff_mul_le hk).mp he
    nlinarith
  · intro hh
    have he : -h ≤ (-z)/k := (Int.le_ediv_iff_mul_le hk).mpr (by nlinarith)
    omega

/-- The ceiling form of Theorem 2, with no finite-configuration assumptions. -/
theorem two_window_ceiling {a b k m : ℤ} (S : Set ℤ)
    (ha : b < a) (hb : 0 < b) (hk : 0 < k) (hm : 0 < m)
    (hcoprime : Int.gcd a b=1) (hS : SetAvoid a b k m S) :
    ((window S (k*a+m*b+a)).card:ℤ) ≤
      a-m*ceilDiv (((window S (k*a+m*b+b)).card:ℤ)-b) k := by
  obtain ⟨h,hB,hC⟩ := two_window_staircase S ha hb hk hm hcoprime hS
  have hc : ceilDiv (((window S (k*a+m*b+b)).card:ℤ)-b) k ≤ h :=
    (ceilDiv_le_iff hk).mpr (by omega)
  have hs := mul_le_mul_of_nonneg_left hc (le_of_lt hm)
  omega

#print axioms two_window_staircase
#print axioms two_window_ceiling

end TwoGap
