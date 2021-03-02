From SSL_Iris Require Import core.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Export tactics coq_tactics ltac_tactics reduction.
From iris.heap_lang Require Import lang notation proofmode.
Require Import common.
From iris_string_ident Require Import ltac2_string_ident.
From Hammer Require Import Hammer.
Context `{!heapG Σ}.
Set Default Proof Using "Type".


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
try rename x into x2.
ssl_load.
iRename select ((tree x2 s a))%I into "iH3".
ssl_if Cond_iH3.

iDestruct (tree_card_0_learn with "iH3") as "[iH3 %iH3_eqn]".
rewrite iH3_eqn; last by safeDispatchPure.
tac_except_post ltac:(rewrite tree_card_0_open).
iDestruct "iH3" as  "(%iH4 & %iH5)".
try wp_pures.
iFindApply.
iExists null_loc.
ssl_finish.
ssl_rewrite_first_heap tree_card_0_open.
ssl_finish.
ssl_rewrite_first_heap tree_card_0_open.
ssl_finish.


iDestruct (tree_card_2_learn with "iH3") as "[iH3 %iH3_eqn]".

edestruct iH3_eqn as [_alpha_545x2 [_alpha_544x2 ->]]; first by safeDispatchPure.
tac_except_post ltac:(rewrite tree_card_2_open).
iDestruct "iH3" as (vx2 s1x2 s2x2 lx2 rx2) "((%iH6 & %iH7) & (iH8 & iH9 & iH10 & iH11 & iH12 & iH13))".
try rename vx2 into vx22.
ssl_load.
try rename lx2 into lx22.
ssl_load.
try rename rx2 into rx22.
ssl_load.
ssl_store.
wp_apply ("tree_copy" $! (r) (lx22) (s1x2) (_alpha_544x2) with "[$] [$]").


iIntros  "iH17".
iDestruct "iH17" as (y1) "(iH14 & iH15 & iH16)".
try wp_pures.
try rename y1 into y12.
ssl_load.
ssl_store.
wp_apply ("tree_copy" $! (r) (rx22) (s2x2) (_alpha_545x2) with "[$] [$]").


iIntros  "iH21".
iDestruct "iH21" as (y2) "(iH18 & iH19 & iH20)".
try wp_pures.
try rename y2 into y22.
ssl_load.
wp_alloc y3 as "?"; try by safeDispatchPure.
wp_pures.
do 3 try rewrite array_cons. iSplitAllHyps. try rewrite array_nil.
try rewrite !loc_add_assoc !Z.add_1_r.

movePure.
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
