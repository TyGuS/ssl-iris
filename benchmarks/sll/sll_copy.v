From SSL_Iris Require Import core.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Export tactics coq_tactics ltac_tactics reduction.
From iris.heap_lang Require Import lang notation proofmode.
Require Import common.
From iris_string_ident Require Import ltac2_string_ident.
From Hammer Require Import Hammer.
Context `{!heapG Σ}.
Set Default Proof Using "Type".


Definition sll_copy : val :=
rec: "sll_copy" "r" :=
let: "x2" := ! ("r") in
#();; 
if: "x2" = #null_loc
then (
#()
)
else (
let: "vx22" := ! ("x2") in
#();; 
let: "nxtx22" := ! ("x2" +ₗ #1) in
#();; 
("r") <- ("nxtx22");; 
"sll_copy" "r";; 
let: "y12" := ! ("r") in
#();; 
let: "y2" := AllocN (#2) (#()) in
#();; 
("r") <- ("y2");; 
("y2" +ₗ #1) <- ("y12");; 
("y2") <- ("vx22");; 
#()
).


Lemma sll_copy_spec :
∀ (r : loc) (x : loc) (s : (list Z)) (a : sll_card),
{{{ r ↦ #x ∗ (sll x s a) }}}
  sll_copy #r
{{{ RET #(); ∃ (b : sll_card) (y : loc), r ↦ #y ∗ (sll x s a) ∗ (sll y s b) }}}.
Proof.
iIntros (r x s a ϕ) "(iH1 & iH2) Post".
iRewriteHyp.
iLöb as "sll_copy" forall (r x s a ϕ).
ssl_begin.
try rename x into x2.
ssl_load.
iRename select ((sll x2 s a))%I into "iH3".
ssl_if Cond_iH3.

iDestruct (sll_card_0_learn with "iH3") as "[iH3 %iH3_eqn]".
rewrite iH3_eqn; last by safeDispatchPure.
tac_except_post ltac:(rewrite sll_card_0_open).
iDestruct "iH3" as  "(%iH4 & %iH5)".
try wp_pures.
iFindApply.
iExists (sll_card_0  : sll_card).
iExists null_loc.
ssl_finish.
ssl_rewrite_first_heap sll_card_0_open.
ssl_finish.
ssl_rewrite_first_heap sll_card_0_open.
ssl_finish.


iDestruct (sll_card_1_learn with "iH3") as "[iH3 %iH3_eqn]".

edestruct iH3_eqn as [_alpha_526x2 ->]; first by safeDispatchPure.
tac_except_post ltac:(rewrite sll_card_1_open).
iDestruct "iH3" as (vx2 s1x2 nxtx2) "((%iH6 & %iH7) & (iH8 & iH9 & iH10 & iH11))".
try rename vx2 into vx22.
ssl_load.
try rename nxtx2 into nxtx22.
ssl_load.
ssl_store.
wp_apply ("sll_copy" $! (r) (nxtx22) (s1x2) (_alpha_526x2) with "[$] [$]").


iIntros  "iH15".
iDestruct "iH15" as (b1 y1) "(iH12 & iH13 & iH14)".
try wp_pures.
try rename y1 into y12.
ssl_load.
wp_alloc y2 as "?"; try by safeDispatchPure.
wp_pures.
do 2 try rewrite array_cons. iSplitAllHyps. try rewrite array_nil.
try rewrite !loc_add_assoc !Z.add_1_r.

movePure.
ssl_store.
ssl_store.
ssl_store.
try wp_pures.
iFindApply.
iExists (sll_card_1 b1 : sll_card).
iExists y2.
ssl_finish.
ssl_rewrite_first_heap sll_card_1_open.
pull_out_exist.
iExists vx22.
pull_out_exist.
iExists s1x2.
pull_out_exist.
iExists nxtx22.
ssl_finish.
ssl_rewrite_first_heap sll_card_1_open.
pull_out_exist.
iExists vx22.
pull_out_exist.
iExists s1x2.
pull_out_exist.
iExists y12.
ssl_finish.
Qed.
