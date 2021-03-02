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
Proof. Admitted.

Lemma tree_card_2_learn (x: loc) (s: (list Z)) self_card:
tree x s self_card  ⊢ tree x s self_card ∗ ⌜~ (x = null_loc) -> ∃ _alpha_514 _alpha_513, self_card = (tree_card_2 _alpha_514 _alpha_513)⌝.
Proof. Admitted.

Lemma tree_card_0_open  (x: loc) (s: (list Z)) :
tree x s (tree_card_0 ) = (⌜(x = null_loc) ∧ (s = [])⌝)%I.
Proof. auto. Qed.

Lemma tree_card_2_open (_alpha_514 : tree_card) (_alpha_513 : tree_card) (x: loc) (s: (list Z)) :
tree x s (tree_card_2 _alpha_514 _alpha_513) = (∃ (v : Z) (s1 : (list Z)) (s2 : (list Z)) (l : loc) (r : loc), ⌜~ (x = null_loc) ∧ (s = (([v] ++ s1) ++ s2))⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #l ∗ (x +ₗ 2) ↦ #r ∗ (tree l s1 _alpha_513) ∗ (tree r s2 _alpha_514))%I.
Proof. auto. Qed.

Lemma treeN_card_0_learn (x: loc) (n: Z) self_card:
treeN x n self_card  ⊢ treeN x n self_card ∗ ⌜(x = null_loc) -> self_card = treeN_card_0⌝.
Proof. Admitted.

Lemma treeN_card_2_learn (x: loc) (n: Z) self_card:
treeN x n self_card  ⊢ treeN x n self_card ∗ ⌜~ (x = null_loc) -> ∃ _alpha_516 _alpha_515, self_card = (treeN_card_2 _alpha_516 _alpha_515)⌝.
Proof. Admitted.

Lemma treeN_card_0_open  (x: loc) (n: Z) :
treeN x n (treeN_card_0 ) = (⌜(x = null_loc) ∧ (n = 0)⌝)%I.
Proof. auto. Qed.

Lemma treeN_card_2_open (_alpha_516 : treeN_card) (_alpha_515 : treeN_card) (x: loc) (n: Z) :
treeN x n (treeN_card_2 _alpha_516 _alpha_515) = (∃ (n1 : Z) (n2 : Z) (v : loc) (l : loc) (r : loc), ⌜~ (x = null_loc) ∧ (0 ≤ n1)%Z ∧ (0 ≤ n2)%Z ∧ (n = ((1 + n1)%Z + n2)%Z)⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #l ∗ (x +ₗ 2) ↦ #r ∗ (treeN l n1 _alpha_515) ∗ (treeN r n2 _alpha_516))%I.
Proof. auto. Qed.

Lemma sll_card_0_learn (x: loc) (s: (list Z)) self_card:
sll x s self_card  ⊢ sll x s self_card ∗ ⌜(x = null_loc) -> self_card = sll_card_0⌝.
Proof. Admitted.

Lemma sll_card_1_learn (x: loc) (s: (list Z)) self_card:
sll x s self_card  ⊢ sll x s self_card ∗ ⌜~ (x = null_loc) -> ∃ _alpha_517, self_card = (sll_card_1 _alpha_517)⌝.
Proof. Admitted.

Lemma sll_card_0_open  (x: loc) (s: (list Z)) :
sll x s (sll_card_0 ) = (⌜(x = null_loc) ∧ (s = [])⌝)%I.
Proof. auto. Qed.

Lemma sll_card_1_open (_alpha_517 : sll_card) (x: loc) (s: (list Z)) :
sll x s (sll_card_1 _alpha_517) = (∃ (v : Z) (s1 : (list Z)) (nxt : loc), ⌜~ (x = null_loc) ∧ (s = ([v] ++ s1))⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #nxt ∗ (sll nxt s1 _alpha_517))%I.
Proof. auto. Qed.

Definition tree_size : val :=
rec: "tree_size" "x" "r" :=
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
"tree_size" "lx2" "r";; 
let: "n1x2" := ! ("r") in
#();; 
("r") <- (#0);; 
"tree_size" "rx2" "r";; 
let: "n2x2" := ! ("r") in
#();; 
("r") <- (#1 + "n1x2" + "n2x2");; 
#()
).


Lemma tree_size_spec :
∀ (n : Z) (r : loc) (x : loc) (a : treeN_card),
{{{ ⌜(0 ≤ n)%Z⌝ ∗ r ↦ #0 ∗ (treeN x n a) }}}
  tree_size #x #r
{{{ RET #(); r ↦ #n ∗ (treeN x n a) }}}.
Proof.
iIntros (n r x a ϕ) "(%iH1 & iH2 & iH3) Post".
iRewriteHyp.
iLöb as "tree_size" forall (n r x a iH1 ϕ).
ssl_begin.

iRename select (r ↦ _)%I into "iH4".
iDestruct (NilNotLval with "iH4") as "[iH4 %]".

iRename select ((treeN x n a))%I into "iH5".
ssl_if Cond_iH5.

iDestruct (treeN_card_0_learn with "iH5") as "[iH5 %iH5_eqn]".
rewrite iH5_eqn; last by safeDispatchPure.
tac_except_post ltac:(rewrite treeN_card_0_open).
iDestruct "iH5" as  "(%iH6 & %iH7)".
try wp_pures.
iFindApply.
ssl_finish.
ssl_rewrite_first_heap treeN_card_0_open.
ssl_finish.


iDestruct (treeN_card_2_learn with "iH5") as "[iH5 %iH5_eqn]".

edestruct iH5_eqn as [_alpha_516x [_alpha_515x ->]]; first by safeDispatchPure.
tac_except_post ltac:(rewrite treeN_card_2_open).
iDestruct "iH5" as (n1x n2x vx lx rx) "((%iH8 & %iH9 & %iH10 & %iH11) & (iH12 & iH13 & iH14 & iH15 & iH16 & iH17))".
try rename vx into vx2.
ssl_load.
try rename lx into lx2.
ssl_load.
try rename rx into rx2.
ssl_load.
wp_apply ("tree_size" $! (n1x) (r) (lx2) (_alpha_515x) with "[] [$] [$]").
ssl_finish.

iIntros  "iH20".
iDestruct "iH20" as  "(iH18 & iH19)".
try wp_pures.
try rename n1x into n1x2.
ssl_load.
ssl_store.
wp_apply ("tree_size" $! (n2x) (r) (rx2) (_alpha_516x) with "[] [$] [$]").
ssl_finish.

iIntros  "iH23".
iDestruct "iH23" as  "(iH21 & iH22)".
try wp_pures.
try rename n2x into n2x2.
ssl_load.
ssl_store.
try wp_pures.
iFindApply.
ssl_finish.
ssl_rewrite_first_heap treeN_card_2_open.
pull_out_exist.
iExists n1x2.
pull_out_exist.
iExists n2x2.
pull_out_exist.
iExists vx2.
pull_out_exist.
iExists lx2.
pull_out_exist.
iExists rx2.
ssl_finish.
Qed.
