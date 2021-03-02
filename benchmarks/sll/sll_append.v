From SSL_Iris Require Import core.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Export tactics coq_tactics ltac_tactics reduction.
From iris.heap_lang Require Import lang notation proofmode.
Require Import common.
From iris_string_ident Require Import ltac2_string_ident.
From Hammer Require Import Hammer.
Context `{!heapG Σ}.
Set Default Proof Using "Type".


Definition sll_append : val :=
rec: "sll_append" "x1" "r" :=
let: "x22" := ! ("r") in
#();; 
if: "x1" = #null_loc
then (
#()
)
else (
let: "vx12" := ! ("x1") in
#();; 
let: "nxtx12" := ! ("x1" +ₗ #1) in
#();; 
"sll_append" "nxtx12" "r";; 
let: "y12" := ! ("r") in
#();; 
("x1" +ₗ #1) <- ("y12");; 
("r") <- ("x1");; 
#()
).


Lemma sll_append_spec :
∀ (r : loc) (x2 : loc) (s2 : (list Z)) (_alpha_531 : sll_card) (x1 : loc) (s1 : (list Z)) (_alpha_530 : sll_card),
{{{ (sll x1 s1 _alpha_530) ∗ (sll x2 s2 _alpha_531) ∗ r ↦ #x2 }}}
  sll_append #x1 #r
{{{ RET #(); ∃ (y : loc) (_alpha_532 : sll_card) (s : (list Z)), ⌜(s = (s1 ++ s2))⌝ ∗ (sll y s _alpha_532) ∗ r ↦ #y }}}.
Proof.
iIntros (r x2 s2 _alpha_531 x1 s1 _alpha_530 ϕ) "(iH1 & iH2 & iH3) Post".
iRewriteHyp.
iLöb as "sll_append" forall (r x2 s2 _alpha_531 x1 s1 _alpha_530 ϕ).
ssl_begin.
try rename x2 into x22.
ssl_load.
iRename select ((sll x1 s1 _alpha_530))%I into "iH4".
ssl_if Cond_iH4.

iDestruct (sll_card_0_learn with "iH4") as "[iH4 %iH4_eqn]".
rewrite iH4_eqn; last by safeDispatchPure.
tac_except_post ltac:(rewrite sll_card_0_open).
iDestruct "iH4" as  "(%iH5 & %iH6)".
try wp_pures.
iFindApply.
iExists x22.
iExists _alpha_531.
iExists ([] ++ s2).
ssl_finish.


iDestruct (sll_card_1_learn with "iH4") as "[iH4 %iH4_eqn]".

edestruct iH4_eqn as [_alpha_529x1 ->]; first by safeDispatchPure.
tac_except_post ltac:(rewrite sll_card_1_open).
iDestruct "iH4" as (vx1 s1x1 nxtx1) "((%iH7 & %iH8) & (iH9 & iH10 & iH11 & iH12))".
try rename vx1 into vx12.
ssl_load.
try rename nxtx1 into nxtx12.
ssl_load.
wp_apply ("sll_append" $! (r) (x22) (s2) (_alpha_531) (nxtx12) (s1x1) (_alpha_529x1) with "[$] [$] [$]").


iIntros  "iH16".
iDestruct "iH16" as (y1 _alpha_5321 s3) "(%iH13 & (iH14 & iH15))".
try wp_pures.
try rename y1 into y12.
ssl_load.
ssl_store.
ssl_store.
try wp_pures.
iFindApply.
iExists x1.
iExists (sll_card_1 _alpha_5321 : sll_card).
iExists (([vx12] ++ s1x1) ++ s2).
ssl_finish.
ssl_rewrite_first_heap sll_card_1_open.
pull_out_exist.
iExists vx12.
pull_out_exist.
iExists (s1x1 ++ s2).
pull_out_exist.
iExists y12.
ssl_finish.
Qed.
