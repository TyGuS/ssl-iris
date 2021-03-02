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
Inductive dll_card : Set :=
    | dll_card_0 : dll_card
    | dll_card_1 : dll_card -> dll_card.

Fixpoint dll (x: loc) (z: loc) (s: (list Z)) (self_card: dll_card) { struct self_card } : iProp Σ := match self_card with
    | dll_card_0  => ⌜(x = null_loc) ∧ (s = [])⌝
    | dll_card_1 _alpha_513 => ∃ (v : Z) (s1 : (list Z)) (w : loc), ⌜~ (x = null_loc) ∧ (s = ([v] ++ s1))⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #w ∗ (x +ₗ 2) ↦ #z ∗ (dll w x s1 _alpha_513)
end.

Global Opaque dll.

Inductive sll_card : Set :=
    | sll_card_0 : sll_card
    | sll_card_1 : sll_card -> sll_card.

Fixpoint sll (x: loc) (s: (list Z)) (self_card: sll_card) { struct self_card } : iProp Σ := match self_card with
    | sll_card_0  => ⌜(x = null_loc) ∧ (s = [])⌝
    | sll_card_1 _alpha_514 => ∃ (v : Z) (s1 : (list Z)) (nxt : loc), ⌜~ (x = null_loc) ∧ (s = ([v] ++ s1))⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #nxt ∗ (sll nxt s1 _alpha_514)
end.

Global Opaque sll.

Lemma dll_card_0_learn (x: loc) (z: loc) (s: (list Z)) self_card:
dll x z s self_card  ⊢ dll x z s self_card ∗ ⌜(x = null_loc) -> self_card = dll_card_0⌝.
Proof. Admitted.

Lemma dll_card_1_learn (x: loc) (z: loc) (s: (list Z)) self_card:
dll x z s self_card  ⊢ dll x z s self_card ∗ ⌜~ (x = null_loc) -> ∃ _alpha_513, self_card = (dll_card_1 _alpha_513)⌝.
Proof. Admitted.

Lemma dll_card_0_open  (x: loc) (z: loc) (s: (list Z)) :
dll x z s (dll_card_0 ) = (⌜(x = null_loc) ∧ (s = [])⌝)%I.
Proof. auto. Qed.

Lemma dll_card_1_open (_alpha_513 : dll_card) (x: loc) (z: loc) (s: (list Z)) :
dll x z s (dll_card_1 _alpha_513) = (∃ (v : Z) (s1 : (list Z)) (w : loc), ⌜~ (x = null_loc) ∧ (s = ([v] ++ s1))⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #w ∗ (x +ₗ 2) ↦ #z ∗ (dll w x s1 _alpha_513))%I.
Proof. auto. Qed.

Lemma sll_card_0_learn (x: loc) (s: (list Z)) self_card:
sll x s self_card  ⊢ sll x s self_card ∗ ⌜(x = null_loc) -> self_card = sll_card_0⌝.
Proof. Admitted.

Lemma sll_card_1_learn (x: loc) (s: (list Z)) self_card:
sll x s self_card  ⊢ sll x s self_card ∗ ⌜~ (x = null_loc) -> ∃ _alpha_514, self_card = (sll_card_1 _alpha_514)⌝.
Proof. Admitted.

Lemma sll_card_0_open  (x: loc) (s: (list Z)) :
sll x s (sll_card_0 ) = (⌜(x = null_loc) ∧ (s = [])⌝)%I.
Proof. auto. Qed.

Lemma sll_card_1_open (_alpha_514 : sll_card) (x: loc) (s: (list Z)) :
sll x s (sll_card_1 _alpha_514) = (∃ (v : Z) (s1 : (list Z)) (nxt : loc), ⌜~ (x = null_loc) ∧ (s = ([v] ++ s1))⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #nxt ∗ (sll nxt s1 _alpha_514))%I.
Proof. auto. Qed.

Definition dll_append : val :=
rec: "dll_append" "x1" "r" :=
let: "x22" := ! ("r") in
#();; 
if: "x1" = #null_loc
then (
#()
)
else (
let: "vx12" := ! ("x1") in
#();; 
let: "wx12" := ! ("x1" +ₗ #1) in
#();; 
let: "a2" := ! ("x1" +ₗ #2) in
#();; 
"dll_append" "wx12" "r";; 
let: "y12" := ! ("r") in
#();; 
if: "y12" = #null_loc
then (
("x1" +ₗ #1) <- (#null_loc);; 
("r") <- ("x1");; 
#()
)
else (
let: "vy122" := ! ("y12") in
#();; 
let: "wy122" := ! ("y12" +ₗ #1) in
#();; 
let: "c12" := ! ("y12" +ₗ #2) in
#();; 
("y12" +ₗ #2) <- ("x1");; 
("x1" +ₗ #1) <- ("y12");; 
("r") <- ("x1");; 
#()
)
).


Lemma dll_append_spec :
∀ (r : loc) (x2 : loc) (s2 : (list Z)) (a : loc) (x1 : loc) (s1 : (list Z)) (_alpha_516 : dll_card) (b : loc) (_alpha_515 : dll_card),
{{{ (dll x1 a s1 _alpha_515) ∗ (dll x2 b s2 _alpha_516) ∗ r ↦ #x2 }}}
  dll_append #x1 #r
{{{ RET #(); ∃ (_alpha_517 : dll_card) (c : loc) (y : loc) (s : (list Z)), ⌜(s = (s1 ++ s2))⌝ ∗ (dll y c s _alpha_517) ∗ r ↦ #y }}}.
Proof.
iIntros (r x2 s2 a x1 s1 _alpha_516 b _alpha_515 ϕ) "(iH1 & iH2 & iH3) Post".
iRewriteHyp.
iLöb as "dll_append" forall (r x2 s2 a x1 s1 _alpha_516 b _alpha_515 ϕ).
ssl_begin.

iRename select (r ↦ _)%I into "iH4".
iDestruct (NilNotLval with "iH4") as "[iH4 %]".

try rename x2 into x22.
ssl_load.
iRename select ((dll x1 a s1 _alpha_515))%I into "iH5".
ssl_if Cond_iH5.

iDestruct (dll_card_0_learn with "iH5") as "[iH5 %iH5_eqn]".
rewrite iH5_eqn; last by safeDispatchPure.
tac_except_post ltac:(rewrite dll_card_0_open).
iDestruct "iH5" as  "(%iH6 & %iH7)".
try wp_pures.
iFindApply.
iExists _alpha_516.
iExists b.
iExists x22.
iExists ([] ++ s2).
ssl_finish.


iDestruct (dll_card_1_learn with "iH5") as "[iH5 %iH5_eqn]".

edestruct iH5_eqn as [_alpha_513x1 ->]; first by safeDispatchPure.
tac_except_post ltac:(rewrite dll_card_1_open).
iDestruct "iH5" as (vx1 s1x1 wx1) "((%iH8 & %iH9) & (iH10 & iH11 & iH12 & iH13 & iH14))".
try rename vx1 into vx12.
ssl_load.
try rename wx1 into wx12.
ssl_load.
try rename a into a2.
ssl_load.
wp_apply ("dll_append" $! (r) (x22) (s2) (x1) (wx12) (s1x1) (_alpha_516) (b) (_alpha_513x1) with "[$] [$] [$]").


iIntros  "iH18".
iDestruct "iH18" as (_alpha_5171 c1 y1 s3) "(%iH15 & (iH16 & iH17))".
try wp_pures.
try rename y1 into y12.
ssl_load.
iRename select ((dll y12 c1 (s1x1 ++ s2) _alpha_5171))%I into "iH19".
ssl_if Cond_iH19.

iDestruct (dll_card_0_learn with "iH19") as "[iH19 %iH19_eqn]".
rewrite iH19_eqn; last by safeDispatchPure.
tac_except_post ltac:(rewrite dll_card_0_open).
iDestruct "iH19" as  "(%iH20 & %iH21)".
ssl_store.
ssl_store.
try wp_pures.
iFindApply.
iExists (dll_card_1 (dll_card_0  : dll_card) : dll_card).
iExists a2.
iExists x1.
iExists (([vx12] ++ s1x1) ++ s2).
ssl_finish.
ssl_rewrite_first_heap dll_card_1_open.
pull_out_exist.
iExists vx12.
pull_out_exist.
iExists [].
pull_out_exist.
iExists null_loc.
ssl_finish.
ssl_rewrite_first_heap dll_card_0_open.
ssl_finish.


iDestruct (dll_card_1_learn with "iH19") as "[iH19 %iH19_eqn]".

edestruct iH19_eqn as [_alpha_513y12 ->]; first by safeDispatchPure.
tac_except_post ltac:(rewrite dll_card_1_open).
iDestruct "iH19" as (vy12 s1y12 wy12) "((%iH22 & %iH23) & (iH24 & iH25 & iH26 & iH27 & iH28))".
try rename vy12 into vy122.
ssl_load.
try rename wy12 into wy122.
ssl_load.
try rename c1 into c12.
ssl_load.
ssl_store.
ssl_store.
ssl_store.
try wp_pures.
iFindApply.
iExists (dll_card_1 (dll_card_1 _alpha_513y12 : dll_card) : dll_card).
iExists a2.
iExists x1.
iExists (([vx12] ++ s1x1) ++ s2).
ssl_finish.
ssl_rewrite_first_heap dll_card_1_open.
pull_out_exist.
iExists vx12.
pull_out_exist.
iExists ([vy122] ++ s1y12).
pull_out_exist.
iExists y12.
ssl_finish.
ssl_rewrite_first_heap dll_card_1_open.
pull_out_exist.
iExists vy122.
pull_out_exist.
iExists s1y12.
pull_out_exist.
iExists wy122.
ssl_finish.
Qed.
