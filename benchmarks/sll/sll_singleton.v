From SSL_Iris Require Import core.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Export tactics coq_tactics ltac_tactics reduction.
From iris.heap_lang Require Import lang notation proofmode.
Require Import common.
From iris_string_ident Require Import ltac2_string_ident.
From Hammer Require Import Hammer.
Context `{!heapG Σ}.
Set Default Proof Using "Type".


Definition sll_singleton : val :=
rec: "sll_singleton" "x" "p" :=
let: "a2" := ! ("p") in
#();; 
let: "y2" := AllocN (#2) (#()) in
#();; 
("p") <- ("y2");; 
("y2" +ₗ #1) <- (#null_loc);; 
("y2") <- ("x");; 
#().


Lemma sll_singleton_spec :
∀ (p : loc) (a : loc) (x : Z),
{{{ p ↦ #a }}}
  sll_singleton #x #p
{{{ RET #(); ∃ (elems : (list Z)) (_alpha_525 : sll_card) (y : loc), ⌜(elems = [x])⌝ ∗ p ↦ #y ∗ (sll y elems _alpha_525) }}}.
Proof.
iIntros (p a x ϕ) "iH1 Post".
iRewriteHyp.
iLöb as "sll_singleton" forall (p a x ϕ).
ssl_begin.
try rename a into a2.
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
iExists [x].
iExists (sll_card_1 (sll_card_0  : sll_card) : sll_card).
iExists y2.
ssl_finish.
ssl_rewrite_first_heap sll_card_1_open.
pull_out_exist.
iExists x.
pull_out_exist.
iExists [].
pull_out_exist.
iExists null_loc.
ssl_finish.
ssl_rewrite_first_heap sll_card_0_open.
ssl_finish.
Qed.
