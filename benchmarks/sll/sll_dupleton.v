From SSL_Iris Require Import core.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Export tactics coq_tactics ltac_tactics reduction.
From iris.heap_lang Require Import lang notation proofmode.
Require Import common.
From iris_string_ident Require Import ltac2_string_ident.
From Hammer Require Import Hammer.
Context `{!heapG Σ}.
Set Default Proof Using "Type".


Definition sll_dupleton : val :=
rec: "sll_dupleton" "x" "y" "r" :=
let: "a2" := ! ("r") in
#();; 
let: "z2" := AllocN (#2) (#()) in
#();; 
let: "nxtz2" := AllocN (#2) (#()) in
#();; 
("r") <- ("z2");; 
("z2" +ₗ #1) <- ("nxtz2");; 
("nxtz2" +ₗ #1) <- (#null_loc);; 
("z2") <- ("x");; 
("nxtz2") <- ("y");; 
#().


Lemma sll_dupleton_spec :
∀ (r : loc) (a : loc) (x : Z) (y : Z),
{{{ r ↦ #a }}}
  sll_dupleton #x #y #r
{{{ RET #(); ∃ (elems : (list Z)) (z : loc) (_alpha_523 : sll_card), ⌜(elems = [x; y])⌝ ∗ r ↦ #z ∗ (sll z elems _alpha_523) }}}.
Proof.
iIntros (r a x y ϕ) "iH1 Post".
iRewriteHyp.
iLöb as "sll_dupleton" forall (r a x y ϕ).
ssl_begin.
try rename a into a2.
ssl_load.
wp_alloc z2 as "?"; try by safeDispatchPure.
wp_pures.
do 2 try rewrite array_cons. iSplitAllHyps. try rewrite array_nil.
try rewrite !loc_add_assoc !Z.add_1_r.

movePure.
wp_alloc nxtz2 as "?"; try by safeDispatchPure.
wp_pures.
do 2 try rewrite array_cons. iSplitAllHyps. try rewrite array_nil.
try rewrite !loc_add_assoc !Z.add_1_r.

movePure.
ssl_store.
ssl_store.
ssl_store.
ssl_store.
ssl_store.
try wp_pures.
iFindApply.
iExists [x; y].
iExists z2.
iExists (sll_card_1 (sll_card_1 (sll_card_0  : sll_card) : sll_card) : sll_card).
ssl_finish.
ssl_rewrite_first_heap sll_card_1_open.
pull_out_exist.
iExists x.
pull_out_exist.
iExists ([y] ++ []).
pull_out_exist.
iExists nxtz2.
ssl_finish.
ssl_rewrite_first_heap sll_card_1_open.
pull_out_exist.
iExists y.
pull_out_exist.
iExists [].
pull_out_exist.
iExists null_loc.
ssl_finish.
ssl_rewrite_first_heap sll_card_0_open.
ssl_finish.
Qed.
