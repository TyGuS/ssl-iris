From SSL_Iris Require Import core.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Export tactics coq_tactics ltac_tactics reduction.
From iris.heap_lang Require Import lang notation proofmode.
Require Import common.
From iris_string_ident Require Import ltac2_string_ident.
From Hammer Require Import Hammer.
Context `{!heapG Σ}.
Set Default Proof Using "Type".


Definition sll_len : val :=
rec: "sll_len" "x" "r" :=
let: "a2" := ! ("r") in
#();; 
if: "x" = #null_loc
then (
("r") <- (#0);; 
#()
)
else (
let: "vx2" := ! ("x") in
#();; 
let: "nxtx2" := ! ("x" +ₗ #1) in
#();; 
"sll_len" "nxtx2" "r";; 
let: "len1x2" := ! ("r") in
#();; 
("r") <- (#1 + "len1x2");; 
#()
).


Lemma sll_len_spec :
∀ (r : loc) (n : Z) (x : loc) (_alpha_514 : sll_card) (a : loc) (hi : Z) (lo : Z),
{{{ ⌜(0 ≤ n)%Z⌝ ∗ r ↦ #a ∗ (sll x n lo hi _alpha_514) }}}
  sll_len #x #r
{{{ RET #(); ∃ (_alpha_515 : sll_card), r ↦ #n ∗ (sll x n lo hi _alpha_515) }}}.
Proof.
iIntros (r n x _alpha_514 a hi lo ϕ) "(%iH1 & iH2 & iH3) Post".
iRewriteHyp.
iLöb as "sll_len" forall (r n x _alpha_514 a hi lo iH1 ϕ).
ssl_begin.
try rename a into a2.
ssl_load.
iRename select ((sll x n lo hi _alpha_514))%I into "iH4".
ssl_if Cond_iH4.

iDestruct (sll_card_0_learn with "iH4") as "[iH4 %iH4_eqn]".
rewrite iH4_eqn; last by safeDispatchPure.
tac_except_post ltac:(rewrite sll_card_0_open).
iDestruct "iH4" as  "(%iH5 & %iH6 & %iH7 & %iH8)".
ssl_store.
try wp_pures.
iFindApply.
iExists (sll_card_0  : sll_card).
ssl_finish.
ssl_rewrite_first_heap sll_card_0_open.
ssl_finish.


iDestruct (sll_card_1_learn with "iH4") as "[iH4 %iH4_eqn]".

edestruct iH4_eqn as [_alpha_513x ->]; first by safeDispatchPure.
tac_except_post ltac:(rewrite sll_card_1_open).
iDestruct "iH4" as (len1x vx hi1x lo1x nxtx) "((%iH9 & %iH10 & %iH11 & %iH12 & %iH13 & %iH14 & %iH15) & (iH16 & iH17 & iH18 & iH19))".
try rename vx into vx2.
ssl_load.
try rename nxtx into nxtx2.
ssl_load.
wp_apply ("sll_len" $! (r) (len1x) (nxtx2) (_alpha_513x) (a2) (hi1x) (lo1x) with "[] [$] [$]").
ssl_finish.

iIntros  "iH22".
iDestruct "iH22" as (_alpha_5151) "(iH20 & iH21)".
try wp_pures.
try rename len1x into len1x2.
ssl_load.
ssl_store.
try wp_pures.
iFindApply.
iExists (sll_card_1 _alpha_5151 : sll_card).
ssl_finish.
ssl_rewrite_first_heap sll_card_1_open.
pull_out_exist.
iExists len1x2.
pull_out_exist.
iExists vx2.
pull_out_exist.
iExists hi1x.
pull_out_exist.
iExists lo1x.
pull_out_exist.
iExists nxtx2.
ssl_finish.
Qed.
