From SSL_Iris Require Import core.
From iris.heap_lang Require Import lang notation proofmode.
From iris_string_ident Require Import ltac2_string_ident.
Section common.
Context `{!heapG Σ}.
Inductive sll_card : Set :=
    | sll_card_0 : sll_card
    | sll_card_1 : sll_card -> sll_card.

Fixpoint sll (x: loc) (s: (list Z)) (self_card: sll_card) { struct self_card } : iProp Σ := match self_card with
    | sll_card_0  => ⌜(x = null_loc) ∧ (s = [])⌝
    | sll_card_1 _alpha_543 => ∃ (v : Z) (s1 : (list Z)) (nxt : loc), ⌜~ (x = null_loc) ∧ (s = ([v] ++ s1))⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #nxt ∗ (sll nxt s1 _alpha_543)
end.

Global Opaque sll.

Inductive treeN_card : Set :=
    | treeN_card_0 : treeN_card
    | treeN_card_2 : treeN_card -> treeN_card -> treeN_card.

Fixpoint treeN (x: loc) (n: Z) (self_card: treeN_card) { struct self_card } : iProp Σ := match self_card with
    | treeN_card_0  => ⌜(x = null_loc) ∧ (n = 0)⌝
    | treeN_card_2 _alpha_542 _alpha_541 => ∃ (n1 : Z) (n2 : Z) (v : loc) (l : loc) (r : loc), ⌜~ (x = null_loc) ∧ (0 ≤ n1)%Z ∧ (0 ≤ n2)%Z ∧ (n = ((1 + n1)%Z + n2)%Z)⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #l ∗ (x +ₗ 2) ↦ #r ∗ (treeN l n1 _alpha_541) ∗ (treeN r n2 _alpha_542)
end.

Global Opaque treeN.

Inductive tree_card : Set :=
    | tree_card_0 : tree_card
    | tree_card_2 : tree_card -> tree_card -> tree_card.

Fixpoint tree (x: loc) (s: (list Z)) (self_card: tree_card) { struct self_card } : iProp Σ := match self_card with
    | tree_card_0  => ⌜(x = null_loc) ∧ (s = [])⌝
    | tree_card_2 _alpha_540 _alpha_539 => ∃ (v : Z) (s1 : (list Z)) (s2 : (list Z)) (l : loc) (r : loc), ⌜~ (x = null_loc) ∧ (s = (([v] ++ s1) ++ s2))⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #l ∗ (x +ₗ 2) ↦ #r ∗ (tree l s1 _alpha_539) ∗ (tree r s2 _alpha_540)
end.

Global Opaque tree.

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
sll x s self_card  ⊢ sll x s self_card ∗ ⌜~ (x = null_loc) -> ∃ _alpha_543, self_card = (sll_card_1 _alpha_543)⌝.
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

Lemma sll_card_1_open (_alpha_543 : sll_card) (x: loc) (s: (list Z)) :
sll x s (sll_card_1 _alpha_543) = (∃ (v : Z) (s1 : (list Z)) (nxt : loc), ⌜~ (x = null_loc) ∧ (s = ([v] ++ s1))⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #nxt ∗ (sll nxt s1 _alpha_543))%I.
Proof. auto. Qed.

Lemma treeN_card_0_learn (x: loc) (n: Z) self_card:
treeN x n self_card  ⊢ treeN x n self_card ∗ ⌜(x = null_loc) -> self_card = treeN_card_0⌝.
Proof.
Transparent treeN.
destruct self_card; iIntros "P".
- iDestruct "P" as  "(% & %)".
   iSplitL.
    iFrame. eauto.
   eauto.
- iDestruct "P" as (n1 n2 v l r) "((% & % & % & %) & (? & ? & ? & ? & ? & ?))".
   iSplitL.
   iExists n1, n2, v, l, r. iFrame. eauto.
   eauto.
Global Opaque treeN.
Qed.

Lemma treeN_card_2_learn (x: loc) (n: Z) self_card:
treeN x n self_card  ⊢ treeN x n self_card ∗ ⌜~ (x = null_loc) -> ∃ _alpha_542 _alpha_541, self_card = (treeN_card_2 _alpha_542 _alpha_541)⌝.
Proof.
Transparent treeN.
destruct self_card; iIntros "P".
- iDestruct "P" as  "(% & %)".
   iSplitL.
    iFrame. eauto.
   eauto.
- iDestruct "P" as (n1 n2 v l r) "((% & % & % & %) & (? & ? & ? & ? & ? & ?))".
   iSplitL.
   iExists n1, n2, v, l, r. iFrame. eauto.
   eauto.
Global Opaque treeN.
Qed.

Lemma treeN_card_0_open  (x: loc) (n: Z) :
treeN x n (treeN_card_0 ) = (⌜(x = null_loc) ∧ (n = 0)⌝)%I.
Proof. auto. Qed.

Lemma treeN_card_2_open (_alpha_542 : treeN_card) (_alpha_541 : treeN_card) (x: loc) (n: Z) :
treeN x n (treeN_card_2 _alpha_542 _alpha_541) = (∃ (n1 : Z) (n2 : Z) (v : loc) (l : loc) (r : loc), ⌜~ (x = null_loc) ∧ (0 ≤ n1)%Z ∧ (0 ≤ n2)%Z ∧ (n = ((1 + n1)%Z + n2)%Z)⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #l ∗ (x +ₗ 2) ↦ #r ∗ (treeN l n1 _alpha_541) ∗ (treeN r n2 _alpha_542))%I.
Proof. auto. Qed.

Lemma tree_card_0_learn (x: loc) (s: (list Z)) self_card:
tree x s self_card  ⊢ tree x s self_card ∗ ⌜(x = null_loc) -> self_card = tree_card_0⌝.
Proof.
Transparent tree.
destruct self_card; iIntros "P".
- iDestruct "P" as  "(% & %)".
   iSplitL.
    iFrame. eauto.
   eauto.
- iDestruct "P" as (v s1 s2 l r) "((% & %) & (? & ? & ? & ? & ? & ?))".
   iSplitL.
   iExists v, s1, s2, l, r. iFrame. eauto.
   eauto.
Global Opaque tree.
Qed.

Lemma tree_card_2_learn (x: loc) (s: (list Z)) self_card:
tree x s self_card  ⊢ tree x s self_card ∗ ⌜~ (x = null_loc) -> ∃ _alpha_540 _alpha_539, self_card = (tree_card_2 _alpha_540 _alpha_539)⌝.
Proof.
Transparent tree.
destruct self_card; iIntros "P".
- iDestruct "P" as  "(% & %)".
   iSplitL.
    iFrame. eauto.
   eauto.
- iDestruct "P" as (v s1 s2 l r) "((% & %) & (? & ? & ? & ? & ? & ?))".
   iSplitL.
   iExists v, s1, s2, l, r. iFrame. eauto.
   eauto.
Global Opaque tree.
Qed.

Lemma tree_card_0_open  (x: loc) (s: (list Z)) :
tree x s (tree_card_0 ) = (⌜(x = null_loc) ∧ (s = [])⌝)%I.
Proof. auto. Qed.

Lemma tree_card_2_open (_alpha_540 : tree_card) (_alpha_539 : tree_card) (x: loc) (s: (list Z)) :
tree x s (tree_card_2 _alpha_540 _alpha_539) = (∃ (v : Z) (s1 : (list Z)) (s2 : (list Z)) (l : loc) (r : loc), ⌜~ (x = null_loc) ∧ (s = (([v] ++ s1) ++ s2))⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #l ∗ (x +ₗ 2) ↦ #r ∗ (tree l s1 _alpha_539) ∗ (tree r s2 _alpha_540))%I.
Proof. auto. Qed.

End common.