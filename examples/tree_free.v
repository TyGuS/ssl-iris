From SSL_Iris Require Import core.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Export tactics coq_tactics ltac_tactics reduction.
From iris.heap_lang Require Import lang notation proofmode.

From iris_string_ident Require Import ltac2_string_ident.
From Hammer Require Import Hammer.
Context `{!heapG Σ}.
Set Default Proof Using "Type".
Axiom NilNotLval:
  forall x v,
  x ↦ v -∗ x ↦ v ∗ ⌜x ≠ null_loc⌝.
Inductive tree_card : Set :=
    | tree_card_0 : tree_card
    | tree_card_2 : tree_card -> tree_card -> tree_card.

Fixpoint tree (x: loc) (s: (list Z)) (self_card: tree_card) { struct self_card } : iProp Σ := match self_card with
    | tree_card_0  => ⌜(x = null_loc) ∧ (s = [])⌝
    | tree_card_2 _alpha_514 _alpha_513 => ∃ (v : Z) (s1 : (list Z)) (s2 : (list Z)) (l : loc) (r : loc), ⌜~ (x = null_loc) ∧ (s = (([v] ++ s1) ++ s2))⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #l ∗ (x +ₗ 2) ↦ #r ∗ (tree l s1 _alpha_513) ∗ (tree r s2 _alpha_514)
end.

Global Opaque tree.

Inductive treeN_card : Set :=
    | treeN_card_0 : treeN_card
    | treeN_card_2 : treeN_card -> treeN_card -> treeN_card.

Fixpoint treeN (x: loc) (n: Z) (self_card: treeN_card) { struct self_card } : iProp Σ := match self_card with
    | treeN_card_0  => ⌜(x = null_loc) ∧ (n = 0)⌝
    | treeN_card_2 _alpha_516 _alpha_515 => ∃ (n1 : Z) (n2 : Z) (v : loc) (l : loc) (r : loc), ⌜~ (x = null_loc) ∧ (0 ≤ n1)%Z ∧ (0 ≤ n2)%Z ∧ (n = ((1 + n1)%Z + n2)%Z)⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #l ∗ (x +ₗ 2) ↦ #r ∗ (treeN l n1 _alpha_515) ∗ (treeN r n2 _alpha_516)
end.

Global Opaque treeN.

Inductive sll_card : Set :=
    | sll_card_0 : sll_card
    | sll_card_1 : sll_card -> sll_card.

Fixpoint sll (x: loc) (s: (list Z)) (self_card: sll_card) { struct self_card } : iProp Σ := match self_card with
    | sll_card_0  => ⌜(x = null_loc) ∧ (s = [])⌝
    | sll_card_1 _alpha_517 => ∃ (v : Z) (s1 : (list Z)) (nxt : loc), ⌜~ (x = null_loc) ∧ (s = ([v] ++ s1))⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #nxt ∗ (sll nxt s1 _alpha_517)
end.

Global Opaque sll.

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
tree x s self_card  ⊢ tree x s self_card ∗ ⌜~ (x = null_loc) -> ∃ _alpha_514 _alpha_513, self_card = (tree_card_2 _alpha_514 _alpha_513)⌝.
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

Lemma tree_card_2_open (_alpha_514 : tree_card) (_alpha_513 : tree_card) (x: loc) (s: (list Z)) :
tree x s (tree_card_2 _alpha_514 _alpha_513) = (∃ (v : Z) (s1 : (list Z)) (s2 : (list Z)) (l : loc) (r : loc), ⌜~ (x = null_loc) ∧ (s = (([v] ++ s1) ++ s2))⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #l ∗ (x +ₗ 2) ↦ #r ∗ (tree l s1 _alpha_513) ∗ (tree r s2 _alpha_514))%I.
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
treeN x n self_card  ⊢ treeN x n self_card ∗ ⌜~ (x = null_loc) -> ∃ _alpha_516 _alpha_515, self_card = (treeN_card_2 _alpha_516 _alpha_515)⌝.
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

Lemma treeN_card_2_open (_alpha_516 : treeN_card) (_alpha_515 : treeN_card) (x: loc) (n: Z) :
treeN x n (treeN_card_2 _alpha_516 _alpha_515) = (∃ (n1 : Z) (n2 : Z) (v : loc) (l : loc) (r : loc), ⌜~ (x = null_loc) ∧ (0 ≤ n1)%Z ∧ (0 ≤ n2)%Z ∧ (n = ((1 + n1)%Z + n2)%Z)⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #l ∗ (x +ₗ 2) ↦ #r ∗ (treeN l n1 _alpha_515) ∗ (treeN r n2 _alpha_516))%I.
Proof. auto. Qed.

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
sll x s self_card  ⊢ sll x s self_card ∗ ⌜~ (x = null_loc) -> ∃ _alpha_517, self_card = (sll_card_1 _alpha_517)⌝.
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

Lemma sll_card_1_open (_alpha_517 : sll_card) (x: loc) (s: (list Z)) :
sll x s (sll_card_1 _alpha_517) = (∃ (v : Z) (s1 : (list Z)) (nxt : loc), ⌜~ (x = null_loc) ∧ (s = ([v] ++ s1))⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #nxt ∗ (sll nxt s1 _alpha_517))%I.
Proof. auto. Qed.

Definition tree_free : val :=
rec: "tree_free" "x" :=
if: "x" = #null_loc
then (
#()
)
else (
let: "vx2" := ! ("x") in
#();; 
let: "lx2" := ! ("x" +ₗ #1) in
#();; 
let: "rx2" := ! ("x" +ₗ #2) in
#();; 
"tree_free" "lx2";; 
"tree_free" "rx2";; 
Free ("x");; 
Free ("x" +ₗ #1);; 
Free ("x" +ₗ #2);; 
#()
).


Lemma tree_free_spec :
∀ (x : loc) (s : (list Z)) (_alpha_518 : tree_card),
{{{ (tree x s _alpha_518) }}}
  tree_free #x
{{{ RET #(); True }}}.
Proof.
iIntros (x s _alpha_518 ϕ) "iH1 Post".
iRewriteHyp.
iLöb as "tree_free" forall (x s _alpha_518 ϕ).
ssl_begin.
iRename select ((tree x s _alpha_518))%I into "iH2".
ssl_if Cond_iH2.

iDestruct (tree_card_0_learn with "iH2") as "[iH2 %iH2_eqn]".
rewrite iH2_eqn; last by safeDispatchPure.
tac_except_post ltac:(rewrite tree_card_0_open).
iDestruct "iH2" as  "(%iH3 & %iH4)".
try wp_pures.
iFindApply.
ssl_finish.


iDestruct (tree_card_2_learn with "iH2") as "[iH2 %iH2_eqn]".

edestruct iH2_eqn as [_alpha_514x [_alpha_513x ->]]; first by safeDispatchPure.
tac_except_post ltac:(rewrite tree_card_2_open).
iDestruct "iH2" as (vx s1x s2x lx rx) "((%iH5 & %iH6) & (iH7 & iH8 & iH9 & iH10 & iH11 & iH12))".
try rename vx into vx2.
ssl_load.
try rename lx into lx2.
ssl_load.
try rename rx into rx2.
ssl_load.
wp_apply ("tree_free" $! (lx2) (s1x) (_alpha_513x) with "[$]").


iIntros  "iH13".

try wp_pures.
wp_apply ("tree_free" $! (rx2) (s2x) (_alpha_514x) with "[$]").


iIntros  "iH14".

try wp_pures.
ssl_free.
ssl_free.
ssl_free.
try wp_pures.
iFindApply.
ssl_finish.
Qed.
