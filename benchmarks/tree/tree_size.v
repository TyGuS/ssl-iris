From SSL_Iris Require Import core.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Export tactics coq_tactics ltac_tactics reduction.
From iris.heap_lang Require Import lang notation proofmode.
Require Import common.
From iris_string_ident Require Import ltac2_string_ident.
From Hammer Require Import Hammer.
Context `{!heapG Σ}.
Set Default Proof Using "Type".


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
iRename select ((treeN x n a))%I into "iH4".
ssl_if Cond_iH4.

iDestruct (treeN_card_0_learn with "iH4") as "[iH4 %iH4_eqn]".
rewrite iH4_eqn; last by safeDispatchPure.
tac_except_post ltac:(rewrite treeN_card_0_open).
iDestruct "iH4" as  "(%iH5 & %iH6)".
try wp_pures.
iFindApply.
ssl_finish.
ssl_rewrite_first_heap treeN_card_0_open.
ssl_finish.


iDestruct (treeN_card_2_learn with "iH4") as "[iH4 %iH4_eqn]".

edestruct iH4_eqn as [_alpha_542x [_alpha_541x ->]]; first by safeDispatchPure.
tac_except_post ltac:(rewrite treeN_card_2_open).
iDestruct "iH4" as (n1x n2x vx lx rx) "((%iH7 & %iH8 & %iH9 & %iH10) & (iH11 & iH12 & iH13 & iH14 & iH15 & iH16))".
try rename vx into vx2.
ssl_load.
try rename lx into lx2.
ssl_load.
try rename rx into rx2.
ssl_load.
wp_apply ("tree_size" $! (n1x) (r) (lx2) (_alpha_541x) with "[] [$] [$]").
ssl_finish.

iIntros  "iH19".
iDestruct "iH19" as  "(iH17 & iH18)".
try wp_pures.
try rename n1x into n1x2.
ssl_load.
ssl_store.
wp_apply ("tree_size" $! (n2x) (r) (rx2) (_alpha_542x) with "[] [$] [$]").
ssl_finish.

iIntros  "iH22".
iDestruct "iH22" as  "(iH20 & iH21)".
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
