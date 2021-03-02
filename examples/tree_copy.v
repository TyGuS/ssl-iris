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

Definition tree_copy : val :=
rec: "tree_copy" "r" :=
let: "x2" := ! ("r") in
#();; 
if: "x2" = #null_loc
then (
#()
)
else (
let: "vx22" := ! ("x2") in
#();; 
let: "lx22" := ! ("x2" +ₗ #1) in
#();; 
let: "rx22" := ! ("x2" +ₗ #2) in
#();; 
("r") <- ("lx22");; 
"tree_copy" "r";; 
let: "y12" := ! ("r") in
#();; 
("r") <- ("rx22");; 
"tree_copy" "r";; 
let: "y22" := ! ("r") in
#();; 
let: "y3" := AllocN (#3) (#()) in
#();; 
("r") <- ("y3");; 
("y3" +ₗ #1) <- ("y12");; 
("y3" +ₗ #2) <- ("y22");; 
("y3") <- ("vx22");; 
#()
).


Lemma tree_copy_spec :
∀ (r : loc) (x : loc) (s : (list Z)) (a : tree_card),
{{{ r ↦ #x ∗ (tree x s a) }}}
  tree_copy #r
{{{ RET #(); ∃ (y : loc), r ↦ #y ∗ (tree x s a) ∗ (tree y s a) }}}.
Proof.
iIntros (r x s a ϕ) "(iH1 & iH2) Post".
iRewriteHyp.
iLöb as "tree_copy" forall (r x s a ϕ).
ssl_begin.

iRename select (r ↦ _)%I into "iH3".
iDestruct (NilNotLval with "iH3") as "[iH3 %]".

try rename x into x2.
ssl_load.
iRename select ((tree x2 s a))%I into "iH4".
ssl_if Cond_iH4.

iDestruct (tree_card_0_learn with "iH4") as "[iH4 %iH4_eqn]".
rewrite iH4_eqn; last by safeDispatchPure.
tac_except_post ltac:(rewrite tree_card_0_open).
iDestruct "iH4" as  "(%iH5 & %iH6)".
try wp_pures.
iFindApply.
iExists null_loc.
ssl_finish.
ssl_rewrite_first_heap tree_card_0_open.
ssl_finish.
ssl_rewrite_first_heap tree_card_0_open.
ssl_finish.


iDestruct (tree_card_2_learn with "iH4") as "[iH4 %iH4_eqn]".

edestruct iH4_eqn as [_alpha_514x2 [_alpha_513x2 ->]]; first by safeDispatchPure.
tac_except_post ltac:(rewrite tree_card_2_open).
iDestruct "iH4" as (vx2 s1x2 s2x2 lx2 rx2) "((%iH7 & %iH8) & (iH9 & iH10 & iH11 & iH12 & iH13 & iH14))".
try rename vx2 into vx22.
ssl_load.
try rename lx2 into lx22.
ssl_load.
try rename rx2 into rx22.
ssl_load.
ssl_store.
wp_apply ("tree_copy" $! (r) (lx22) (s1x2) (_alpha_513x2) with "[$] [$]").


iIntros  "iH18".
iDestruct "iH18" as (y1) "(iH15 & iH16 & iH17)".
try wp_pures.
try rename y1 into y12.
ssl_load.
ssl_store.
wp_apply ("tree_copy" $! (r) (rx22) (s2x2) (_alpha_514x2) with "[$] [$]").


iIntros  "iH22".
iDestruct "iH22" as (y2) "(iH19 & iH20 & iH21)".
try wp_pures.
try rename y2 into y22.
ssl_load.
wp_alloc y3 as "?"; try by safeDispatchPure.
wp_pures.
do 3 try rewrite array_cons. iSplitAllHyps. try rewrite array_nil.
try rewrite !loc_add_assoc !Z.add_1_r.


iRename select (y3 ↦ _)%I into "iH23".
iDestruct (NilNotLval with "iH23") as "[iH23 %]".

ssl_store.
ssl_store.
ssl_store.
ssl_store.
try wp_pures.
iFindApply.
iExists y3.
ssl_finish.
ssl_rewrite_first_heap tree_card_2_open.
pull_out_exist.
iExists vx22.
pull_out_exist.
iExists s1x2.
pull_out_exist.
iExists s2x2.
pull_out_exist.
iExists lx22.
pull_out_exist.
iExists rx22.
ssl_finish.
ssl_rewrite_first_heap tree_card_2_open.
pull_out_exist.
iExists vx22.
pull_out_exist.
iExists s1x2.
pull_out_exist.
iExists s2x2.
pull_out_exist.
iExists y12.
pull_out_exist.
iExists y22.
ssl_finish.
Qed.
