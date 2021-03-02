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
Axiom sll_append: val.

Axiom sll_append_spec :
∀ (x2 : loc) (ret : loc) (s2 : (list Z)) (x1 : loc) (s1 : (list Z)) (_alpha_518 : sll_card) (_alpha_519 : sll_card),
{{{ (sll x1 s1 _alpha_518) ∗ (sll x2 s2 _alpha_519) ∗ ret ↦ #x2 }}}
  sll_append #x1 #ret
{{{ RET #(); ∃ (y : loc) (_alpha_520 : sll_card) (s : (list Z)), ⌜(s = (s1 ++ s2))⌝ ∗ (sll y s _alpha_520) ∗ ret ↦ #y }}}.

Definition tree_flatten : val :=
rec: "tree_flatten" "z" :=
let: "x2" := ! ("z") in
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
("z") <- ("lx22");; 
"tree_flatten" "z";; 
let: "y12" := ! ("z") in
#();; 
("z") <- ("rx22");; 
"tree_flatten" "z";; 
let: "y22" := ! ("z") in
#();; 
sll_append "y12" "z";; 
let: "y32" := ! ("z") in
#();; 
let: "y4" := AllocN (#2) (#()) in
#();; 
Free ("x2");; 
Free ("x2" +ₗ #1);; 
Free ("x2" +ₗ #2);; 
("z") <- ("y4");; 
("y4" +ₗ #1) <- ("y32");; 
("y4") <- ("vx22");; 
#()
).


Lemma tree_flatten_spec :
∀ (z : loc) (x : loc) (s : (list Z)) (_alpha_521 : tree_card),
{{{ z ↦ #x ∗ (tree x s _alpha_521) }}}
  tree_flatten #z
{{{ RET #(); ∃ (y : loc) (_alpha_522 : sll_card), z ↦ #y ∗ (sll y s _alpha_522) }}}.
Proof.
iIntros (z x s _alpha_521 ϕ) "(iH1 & iH2) Post".
iRewriteHyp.
iLöb as "tree_flatten" forall (z x s _alpha_521 ϕ).
ssl_begin.

iRename select (z ↦ _)%I into "iH3".
iDestruct (NilNotLval with "iH3") as "[iH3 %]".

try rename x into x2.
ssl_load.
iRename select ((tree x2 s _alpha_521))%I into "iH4".
ssl_if Cond_iH4.

iDestruct (tree_card_0_learn with "iH4") as "[iH4 %iH4_eqn]".
rewrite iH4_eqn; last by safeDispatchPure.
tac_except_post ltac:(rewrite tree_card_0_open).
iDestruct "iH4" as  "(%iH5 & %iH6)".
try wp_pures.
iFindApply.
iExists null_loc.
iExists (sll_card_0  : sll_card).
ssl_finish.
ssl_rewrite_first_heap sll_card_0_open.
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
wp_apply ("tree_flatten" $! (z) (lx22) (s1x2) (_alpha_513x2) with "[$] [$]").


iIntros  "iH17".
iDestruct "iH17" as (y1 _alpha_5221) "(iH15 & iH16)".
try wp_pures.
try rename y1 into y12.
ssl_load.
ssl_store.
wp_apply ("tree_flatten" $! (z) (rx22) (s2x2) (_alpha_514x2) with "[$] [$]").


iIntros  "iH20".
iDestruct "iH20" as (y2 _alpha_5222) "(iH18 & iH19)".
try wp_pures.
try rename y2 into y22.
ssl_load.
wp_apply (sll_append_spec  (y22) (z) (s2x2) (y12) (s1x2) (_alpha_5221) (_alpha_5222) with "[$]").


iIntros  "iH24".
iDestruct "iH24" as (y3 _alpha_520 s3) "(%iH21 & (iH22 & iH23))".
try wp_pures.
try rename y3 into y32.
ssl_load.
wp_alloc y4 as "?"; try by safeDispatchPure.
wp_pures.
do 2 try rewrite array_cons. iSplitAllHyps. try rewrite array_nil.
try rewrite !loc_add_assoc !Z.add_1_r.


iRename select (y4 ↦ _)%I into "iH25".
iDestruct (NilNotLval with "iH25") as "[iH25 %]".

ssl_free.
ssl_free.
ssl_free.
ssl_store.
ssl_store.
ssl_store.
try wp_pures.
iFindApply.
iExists y4.
iExists (sll_card_1 _alpha_520 : sll_card).
ssl_finish.
ssl_rewrite_first_heap sll_card_1_open.
pull_out_exist.
iExists vx22.
pull_out_exist.
iExists (s1x2 ++ s2x2).
pull_out_exist.
iExists y32.
ssl_finish.
Qed.
