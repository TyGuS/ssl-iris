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


Definition min2 : val :=
rec: "min2" "r" "x" "y" :=
if: "x" ≤ "y"
then (
("r") <- ("x");; 
#()
)
else (
("r") <- ("y");; 
#()
).


Lemma min2_spec :
∀ (r : loc) (x : Z) (y : Z),
{{{ r ↦ #0 }}}
  min2 #r #x #y
{{{ RET #(); ∃ (m : Z), ⌜(m ≤ x)%Z ∧ (m ≤ y)%Z⌝ ∗ r ↦ #m }}}.
Proof.
iIntros (r x y ϕ) "iH1 Post".
iRewriteHyp.
iLöb as "min2" forall (r x y ϕ).
ssl_begin.
ssl_if iH2.

iRename select (r ↦ _)%I into "iH3".
iDestruct (NilNotLval with "iH3") as "[iH3 %]".

ssl_store.
try wp_pures.
iFindApply.
iExists x.
ssl_finish.


iRename select (r ↦ _)%I into "iH4".
iDestruct (NilNotLval with "iH4") as "[iH4 %]".

ssl_store.
try wp_pures.
iFindApply.
iExists y.
ssl_finish.
Qed.
