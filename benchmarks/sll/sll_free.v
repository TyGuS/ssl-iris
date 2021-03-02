From SSL_Iris Require Import core.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Export tactics coq_tactics ltac_tactics reduction.
From iris.heap_lang Require Import lang notation proofmode.
Require Import common.
From iris_string_ident Require Import ltac2_string_ident.
From Hammer Require Import Hammer.
Context `{!heapG Σ}.
Set Default Proof Using "Type".


Definition sll_free : val :=
rec: "sll_free" "x" :=
if: "x" = #null_loc
then (
#()
)
else (
let: "vx2" := ! ("x") in
#();; 
let: "nxtx2" := ! ("x" +ₗ #1) in
#();; 
"sll_free" "nxtx2";; 
Free ("x");; 
Free ("x" +ₗ #1);; 
#()
).


Lemma sll_free_spec :
∀ (x : loc) (s : (list Z)) (_alpha_528 : sll_card),
{{{ (sll x s _alpha_528) }}}
  sll_free #x
{{{ RET #(); True }}}.
Proof.
iIntros (x s _alpha_528 ϕ) "iH1 Post".
iRewriteHyp.
iLöb as "sll_free" forall (x s _alpha_528 ϕ).
ssl_begin.
iRename select ((sll x s _alpha_528))%I into "iH2".
ssl_if Cond_iH2.

iDestruct (sll_card_0_learn with "iH2") as "[iH2 %iH2_eqn]".
rewrite iH2_eqn; last by safeDispatchPure.
tac_except_post ltac:(rewrite sll_card_0_open).
iDestruct "iH2" as  "(%iH3 & %iH4)".
try wp_pures.
iFindApply.
ssl_finish.


iDestruct (sll_card_1_learn with "iH2") as "[iH2 %iH2_eqn]".

edestruct iH2_eqn as [_alpha_527x ->]; first by safeDispatchPure.
tac_except_post ltac:(rewrite sll_card_1_open).
iDestruct "iH2" as (vx s1x nxtx) "((%iH5 & %iH6) & (iH7 & iH8 & iH9 & iH10))".
try rename vx into vx2.
ssl_load.
try rename nxtx into nxtx2.
ssl_load.
wp_apply ("sll_free" $! (nxtx2) (s1x) (_alpha_527x) with "[$]").


iIntros  "iH11".

try wp_pures.
ssl_free.
ssl_free.
try wp_pures.
iFindApply.
ssl_finish.
Qed.
