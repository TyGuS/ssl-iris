From SSL_Iris Require Import core.
From iris.heap_lang Require Import lang notation proofmode.
From iris_string_ident Require Import ltac2_string_ident.
Section common.
Context `{!heapG Σ}.


(*** Least fixpoint definition ***)
Canonical Structure list0 := leibnizO (list Z).

Definition sll' (f : loc * list Z -> iProp Σ) (arg : loc * list Z) : iProp Σ :=
  let (x, s) := arg in
  (⌜x = null_loc /\ s = []⌝ ∨ (∃ v1 s1 (next : loc), ⌜~ (x = null_loc) ∧ (s = ([v1] ++ s1))⌝ ∗ ⌜True⌝ ∗ x ↦ #v1 ∗ (x +ₗ 1) ↦ #next ∗ f (next, s1)))%I.

Global Instance sll'_mono : fixpoint.BiMonoPred sll'.
Proof.
  constructor.
  - iIntros (??) "#H".
    iIntros ([x s]) "[A | B]"; first by iLeft.
    rewrite/sll'. iRight.
    iDestruct "B" as (v1 s1 next) "(? & ? & ? & ? & ?)".
    iExists v1, s1, next.
    iFrame. by iApply "H".
  - intros.
    intros ???.
Admitted.

Definition sll_ := fixpoint.bi_least_fixpoint sll'.

Lemma cons_0_open  (x: loc) (s: (list Z)) :
  x = null_loc → sll_ (x, s) ⊣⊢ ⌜(x = null_loc) ∧ (s = [])⌝.
Proof.
  intros Eq. iSplit.
  - iIntros "P".
    unfold sll_. rewrite (fixpoint.least_fixpoint_unfold sll' (x, s)).
    rewrite Eq.
    iDestruct "P" as "[#P | P]".
    by iFrame "P".
    by iDestruct "P" as (v s1 nxt) "((% & %) & (? & ? & ? & ?))".
  - iIntros "[%%]".
    unfold sll_. rewrite (fixpoint.least_fixpoint_unfold sll' (x, s)). simpl.
    iLeft. done.
Qed.

Lemma cons_1_open  (x: loc) (s: (list Z)) :
  ~ (x = null_loc) → sll_ (x, s) ⊣⊢
     (∃ (v : Z) (s1 : (list Z)) (nxt : loc), ⌜~ (x = null_loc) ∧ (s = ([v] ++ s1))⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #nxt ∗ sll_ (nxt, s1)).
Proof.
  intros Eq. iSplit.
  - iIntros "P".
    unfold sll_. rewrite (fixpoint.least_fixpoint_unfold sll' (x, s)).
    iDestruct "P" as "[#P | P]".
    + by iDestruct "P" as "(% & %)".
    + iDestruct "P" as (v s1 nxt) "((% & %) & (? & ? & ? & ?))".
    iExists v, s1, nxt. iFrame. eauto.
  - iDestruct 1 as (v s1 nxt) "((% & %) & (? & ? & ? & ?))".
    unfold sll_. rewrite (fixpoint.least_fixpoint_unfold sll' (x, s)). simpl.
    iRight. by iExists v, s1, nxt; iFrame.
Qed.

(*** Cardinality definition ***)

Inductive sll_card : Set :=
    | sll_card_0 : sll_card
    | sll_card_1 : sll_card -> sll_card.

Fixpoint sll (x: loc) (s: (list Z)) (self_card: sll_card) { struct self_card } : iProp Σ := match self_card with
    | sll_card_0  => ⌜(x = null_loc) ∧ (s = [])⌝
    | sll_card_1 _alpha_522 => ∃ (v : Z) (s1 : (list Z)) (nxt : loc), ⌜~ (x = null_loc) ∧ (s = ([v] ++ s1))⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #nxt ∗ (sll nxt s1 _alpha_522)
end.

Global Opaque sll.

Lemma sll_card_0_learn (x: loc) (s: (list Z)) self_card:
sll x s self_card  ⊢ sll x s self_card ∗ ⌜(x = null_loc) -> self_card = sll_card_0⌝.
Proof.
Transparent sll.
destruct self_card; iIntros "P".
- iDestruct "P" as  "(% & %)".
   iSplitL.
    iFrame. eauto.
   eauto.
- iDestruct "P" as (v s1 nxt) "((% & %) & (? & ? & ? & ?))".
   iSplitL.
   iExists v, s1, nxt. iFrame. eauto.
   eauto.
Global Opaque sll.
Qed.


Lemma sll_card_1_learn (x: loc) (s: (list Z)) self_card:
sll x s self_card  ⊢ sll x s self_card ∗ ⌜~ (x = null_loc) -> ∃ _alpha_522, self_card = (sll_card_1 _alpha_522)⌝.
Proof.
Transparent sll.
destruct self_card; iIntros "P".
- iDestruct "P" as  "(% & %)".
   iSplitL.
    iFrame. eauto.
   eauto.
- iDestruct "P" as (v s1 nxt) "((% & %) & (? & ? & ? & ?))".
   iSplitL.
   iExists v, s1, nxt. iFrame. eauto.
   eauto.
Global Opaque sll.
Qed.

Lemma sll_card_0_open  (x: loc) (s: (list Z)) :
sll x s (sll_card_0 ) = (⌜(x = null_loc) ∧ (s = [])⌝)%I.
Proof. auto. Qed.

Lemma sll_card_1_open (_alpha_522 : sll_card) (x: loc) (s: (list Z)) :
sll x s (sll_card_1 _alpha_522) = (∃ (v : Z) (s1 : (list Z)) (nxt : loc), ⌜~ (x = null_loc) ∧ (s = ([v] ++ s1))⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #nxt ∗ (sll nxt s1 _alpha_522))%I.
Proof. auto. Qed.

End common.
