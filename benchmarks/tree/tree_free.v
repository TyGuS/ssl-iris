From SSL_Iris Require Import core.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Export tactics coq_tactics ltac_tactics reduction.
From iris.heap_lang Require Import lang notation proofmode.
Require Import common.
From iris_string_ident Require Import ltac2_string_ident.
From Hammer Require Import Hammer.
Context `{!heapG Σ}.
Set Default Proof Using "Type".


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
∀ (x : loc) (s : (list Z)) (_alpha_564 : tree_card),
{{{ (tree x s _alpha_564) }}}
  tree_free #x
{{{ RET #(); True }}}.
Proof.
iIntros (x s _alpha_564 ϕ) "iH1 Post".
iRewriteHyp.
iLöb as "tree_free" forall (x s _alpha_564 ϕ).
ssl_begin.
iRename select ((tree x s _alpha_564))%I into "iH2".
ssl_if Cond_iH2.

iDestruct (tree_card_0_learn with "iH2") as "[iH2 %iH2_eqn]".
rewrite iH2_eqn; last by safeDispatchPure.
tac_except_post ltac:(rewrite tree_card_0_open).
iDestruct "iH2" as  "(%iH3 & %iH4)".
try wp_pures.
iFindApply.
ssl_finish.


iDestruct (tree_card_2_learn with "iH2") as "[iH2 %iH2_eqn]".

edestruct iH2_eqn as [_alpha_560x [_alpha_559x ->]]; first by safeDispatchPure.
tac_except_post ltac:(rewrite tree_card_2_open).
iDestruct "iH2" as (vx s1x s2x lx rx) "((%iH5 & %iH6) & (iH7 & iH8 & iH9 & iH10 & iH11 & iH12))".
try rename vx into vx2.
ssl_load.
try rename lx into lx2.
ssl_load.
try rename rx into rx2.
ssl_load.
wp_apply ("tree_free" $! (lx2) (s1x) (_alpha_559x) with "[$]").


iIntros  "iH13".

try wp_pures.
wp_apply ("tree_free" $! (rx2) (s2x) (_alpha_560x) with "[$]").


iIntros  "iH14".

try wp_pures.
ssl_free.
ssl_free.
ssl_free.
try wp_pures.
iFindApply.
ssl_finish.
Qed.
